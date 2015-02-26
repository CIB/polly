#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"

#include "polly/EWPTAliasAnalysis.h"

#include <isl/flow.h>
#include <isl/constraint.h>
#include <isl/ctx.h>
#include <isl/set.h>
#include <isl/map.h>
#include <isl/printer.h>
#include <isl/space.h>
#include <isl/local_space.h>
#include <isl/val.h>
#include <isl/options.h>

#include <queue>

using namespace llvm;

class EWPTAliasAnalysis;
class EWPTAliasAnalysisState;
class EWPTAliasAnalysisFrame;

/**
 * An EWPT mapping entry of the form
 * <N_s[a_1, ..., a_k], c>(x_1, ..., x_d), where s is the source
 * location of a heap object, a_i represent the iteration vector of
 * the heap object, x_i represent variables of subscript expressions,
 * and c is a system of linear constraints over a_i and x_i.
 */
class EWPTEntry {
public:
    EWPTEntry()
        : Mapping(NULL)
    { }

    /**
     * The amount of parameters x_1, x_2, ..., x_d, where d is the
     * depth of this entry.
     */
    int Depth;

    /**
     * The amount of iteration indices a_1, ..., a_k by which the heap
     * object is identified, k being this value.
     */
    int AmountOfIterators;

    /**
     * The source location of the heap object mapped by this entry.
     */
    const llvm::Value *SourceLocation;

    /**
     * An additional set of free variables which represent variables
     * in the C++ source code. All llvm::Value's here must be valid
     * within the same basic block as the EWPT mapping is.
     */
    std::vector<const llvm::Value *> FreeVariables;

    /**
     * Set of constraints over x_i, a_i and our free variables,
     * mapping x_i to a_i with additional requirements to free variables.
     */
    isl_basic_map *Mapping;

    /**
     * Apply the given llvm::Value as subscript expression to the first
     * parameter x_1
     */
    EWPTEntry ApplySubscript(EWPTAliasAnalysis& Analysis, const SCEV *Subscript, EWPTAliasAnalysisFrame& Frame, EWPTAliasAnalysisState& State) const;

    /**
     * Get the index for the given llvm::Value as free variable within this mapping entry.
     *
     * May add the variable as new free variable with new index to the mapping entry.
     */
    int GetIndexForFreeVariable(const llvm::Value *FreeVariable) {
        for(unsigned I = 0; I < FreeVariables.size(); I++) {
            if(FreeVariables[I] == FreeVariable) {
                return I;
            }
        }
        FreeVariables.push_back(FreeVariable);
        return FreeVariables.size() - 1;
    }

    void debugPrint(EWPTAliasAnalysis& Analysis);

    EWPTEntry clone() {
        EWPTEntry RetVal = *this;
        RetVal.Mapping = isl_basic_map_copy(Mapping);
        return RetVal;
    }

private:
    void InternalApplySubscript(EWPTAliasAnalysis& Analysis, const SCEV *Subscript, EWPTAliasAnalysisFrame &Frame, EWPTAliasAnalysisState& State);
};

EWPTEntry EWPTEntry::ApplySubscript(EWPTAliasAnalysis& Analysis, const SCEV* Subscript, EWPTAliasAnalysisFrame &Frame, EWPTAliasAnalysisState& State) const {
    EWPTEntry Copy = *this;
    Copy.Mapping = isl_basic_map_copy(Mapping);
    Copy.InternalApplySubscript(Analysis, Subscript, Frame, State);
    return Copy;
}

class EWPTRoot {
public:
    std::vector<EWPTEntry> Entries;

    EWPTRoot ApplySubscript(EWPTAliasAnalysis& Analysis, const SCEV *Subscript, EWPTAliasAnalysisFrame &Frame, EWPTAliasAnalysisState& State) {
        EWPTRoot RetVal;
        for(auto& Entry : Entries) {
            if(Entry.Depth > 0) {
                RetVal.Entries.push_back(Entry.ApplySubscript(Analysis, Subscript, Frame, State));
            }
        }
        return RetVal;
    }

    EWPTRoot merge(EWPTRoot& Other) {
        EWPTRoot RetVal = *this;
        for(auto Entry : Other.Entries) {
            RetVal.Entries.push_back(Entry);
        }
        return RetVal;
    }

    EWPTRoot clone() {
        EWPTRoot RetVal;
        for(auto& Entry : Entries) {
            RetVal.Entries.push_back(Entry.clone());
        }
        return RetVal;
    }

    bool equals(EWPTRoot& Other) {
        for(auto& Entry : Entries) {
            bool IsMatched = false;
            for(auto& OtherEntry : Other.Entries) {
                if(Entry.Depth == OtherEntry.Depth && Entry.SourceLocation == OtherEntry.SourceLocation) {
                    if(isl_basic_map_is_equal(Entry.Mapping, OtherEntry.Mapping)) {
                        IsMatched = true;
                        break;
                    }
                }
            }
            if(!IsMatched) {
                return false;
            }
        }
        return true;
    }
};

class EWPTAliasAnalysisState {
public:
    std::map<llvm::Value *, EWPTRoot> trackedRoots;

    EWPTAliasAnalysisState merge(EWPTAliasAnalysisState& Other) {
        EWPTAliasAnalysisState RetVal = *this;
        for(auto TrackedRootEntry : Other.trackedRoots) {
            llvm::Value *Key = TrackedRootEntry.first;
            EWPTRoot& Value = TrackedRootEntry.second;

            if(RetVal.trackedRoots.count(Key)) {
                RetVal.trackedRoots[Key] = RetVal.trackedRoots[Key].merge(Value);
            } else {
                RetVal.trackedRoots[Key] = Value;
            }
        }

        return RetVal;
    }

    EWPTAliasAnalysisState clone() {
        EWPTAliasAnalysisState RetVal;
        for(auto Pair : trackedRoots) {
            RetVal.trackedRoots[Pair.first] = Pair.second.clone();
        }
        return RetVal;
    }

    bool equals(EWPTAliasAnalysisState& Other) {
        for(auto Pair : trackedRoots) {
            auto Entry = Pair.second;
            auto OtherEntry = Other.trackedRoots[Pair.first];

            if(!Entry.equals(OtherEntry)) {
                return false;
            }
        }
        return true;
    }
};

class EWPTAliasAnalysisFrame {
public:
    EWPTAliasAnalysisFrame *SuperFrame;
    std::set<llvm::BasicBlock*> BeginBlocks;
    EWPTAliasAnalysisState EntryState;
    llvm::BasicBlock *Exit;
    llvm::Loop *RestrictToLoop;
    std::map<llvm::BasicBlock*, EWPTAliasAnalysisState> BlockOutStates;
    std::queue<llvm::BasicBlock*> BlocksToProcess;

    EWPTAliasAnalysisFrame() :
        SuperFrame(NULL), Exit(NULL), RestrictToLoop(NULL)
    { };

    std::vector<llvm::Value*> GetCurrentLoopIterators() {
        std::vector<llvm::Value*> RetVal;
        EWPTAliasAnalysisFrame *Current = this;
        while(Current->RestrictToLoop != NULL) {
            // This loop terminates properly because the outermost frame has no loop restrictions.
            RetVal.push_back(Current->RestrictToLoop->getCanonicalInductionVariable());
            Current = Current->SuperFrame;
        };
        return RetVal;
    }

    unsigned GetDepth() {
        return GetCurrentLoopIterators().size();
    }
};

class EWPTAliasAnalysis: public FunctionPass, public AliasAnalysis
{
    public:
        static char ID;

        ~EWPTAliasAnalysis()
        {
            isl_ctx_free(IslContext);
        }

        /// @brief Analysis passes used.
        //@{
        ScalarEvolution *SE;
        LoopInfo *LI;
        //@}

        isl_ctx *IslContext;

        EWPTAliasAnalysis() : FunctionPass(ID)
        {
            initializeEWPTAliasAnalysisPass(*PassRegistry::getPassRegistry());
            IslContext = isl_ctx_alloc();
            isl_options_set_on_error(IslContext, ISL_ON_ERROR_ABORT);
        }

        virtual bool runOnFunction(Function &F)
        {
            // Initialization.
            SE = &getAnalysis<ScalarEvolution>();
            LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();

            InitializeAliasAnalysis(this);

            // The actual analysis.
            EWPTAliasAnalysisFrame Frame;
            auto BeginBlock = &(F.getEntryBlock());
            Frame.BeginBlocks.insert(BeginBlock);
            Frame.RestrictToLoop = NULL;
            iterativeControlFlowAnalysis(Frame);

            return false;
        }

        bool arePredecessorsProcessed(EWPTAliasAnalysisFrame& Frame, BasicBlock* ToCheck) {
            bool AllPredecessorsComputed = true;
            for(auto PI = pred_begin(ToCheck), E = pred_end(ToCheck); PI != E; PI++) {
                auto Predecessor = *PI;
                if(!Frame.BlockOutStates.count(Predecessor)) {
                    AllPredecessorsComputed = false;
                    break;
                }
            }
            return AllPredecessorsComputed;
        }
        
        std::vector<EWPTAliasAnalysisState*> getPredecessorStates(EWPTAliasAnalysisFrame& Frame, BasicBlock *Current) {
            std::vector<EWPTAliasAnalysisState*> PredecessorStates;
            if(Frame.BeginBlocks.find(Current) != Frame.BeginBlocks.end()) {
                PredecessorStates.push_back(&Frame.EntryState);
                // TODO: figure out whether to return here or not
            }

            for(auto PI = pred_begin(Current), E = pred_end(Current); PI != E; PI++) {
                auto Predecessor = *PI;
                auto& PredecessorState = Frame.BlockOutStates[Predecessor];
                PredecessorStates.push_back(&PredecessorState);
            }
            return PredecessorStates;
        }

        void iterativeControlFlowAnalysis(EWPTAliasAnalysisFrame& Frame) {
            for(auto BeginBlock : Frame.BeginBlocks) {
                Frame.BlocksToProcess.push(BeginBlock);
            }
            while(Frame.BlocksToProcess.size()) {
                BasicBlock *Current = Frame.BlocksToProcess.front();
                Frame.BlocksToProcess.pop();

                auto StartWithState = MergeStates(getPredecessorStates(Frame, Current));
                Frame.BlockOutStates[Current] = runOnBlock(*Current, Frame, StartWithState);

                // Don't process the successors of an exit.
                if(Current == Frame.Exit) {
                    continue;
                }

                if(LI->isLoopHeader(Current)) {
                    Loop* LoopToAnalyze = LI->getLoopFor(Current);
                    Frame.BlockOutStates[Current] = handleLoop(Frame, *Current, *LoopToAnalyze);

                    // Only add the successors that are not part of the loop.
                    for(auto SI = succ_begin(Current), E = succ_end(Current); SI != E; SI++) {
                        // Check that this successor now has all requirements.
                        auto Successor = *SI;
                        // Only process the successor if it's actually within the current loop.
                        if(!LoopToAnalyze->contains(Successor)) {
                            Frame.BlocksToProcess.push(Successor);
                        }
                    }

                    continue;
                } else if(!arePredecessorsProcessed(Frame, Current)) {
                    llvm::errs() << "Trying to process block with unprocessed predecessors.";
                    exit(1);
                }

                // Once this frame is done, try processing successors
                for(auto SI = succ_begin(Current), E = succ_end(Current); SI != E; SI++) {
                    // Check that this successor now has all requirements.
                    auto Successor = *SI;
                    // Only process the successor if it's actually within the current loop.
                    if(!Frame.RestrictToLoop || Frame.RestrictToLoop->contains(Successor)) {
                        if(arePredecessorsProcessed(Frame, Successor) || LI->isLoopHeader(Successor)) {
                            Frame.BlocksToProcess.push(Successor);
                        }
                    }
                }
            }

            for(auto Pair : Frame.BlockOutStates) {
                llvm::outs() << "EWPTs for BB:\n";
                debugPrintEWPTs(Pair.second);
            }
        }

        llvm::Value *getUpperBoundForLoop(Loop& LoopToAnalyze) {
            BasicBlock* LoopHeader = LoopToAnalyze.getHeader();
            for(auto& Instruction : LoopHeader->getInstList()) {
                llvm::outs() << "Checking " << Instruction << "\n";
                if(auto Comparison = dyn_cast<ICmpInst>(&Instruction)) {
                    if(
                        Comparison->getOperand(0) == LoopToAnalyze.getCanonicalInductionVariable() &&
                        Comparison->isFalseWhenEqual()
                    ) {
                        return Comparison->getOperand(1);
                    }
                }
            }

            llvm::errs() << "No upper bound found for loop.\n";
            exit(1);
        }

        EWPTAliasAnalysisState handleLoop(EWPTAliasAnalysisFrame& SuperFrame, BasicBlock& LoopHeader, Loop& LoopToAnalyze) {
            // We can only handle loops of a specific type, check these properties first.

            // It must have a canonical induction variable, i.e. for(i = 0; i < n; i++)
            if(!LoopToAnalyze.getCanonicalInductionVariable()) {
                llvm::errs() << "No canonical induction variable found for loop " << LoopToAnalyze << ", consider prepending the -indvars pass.\n";
                exit(1);
            }

            // It must have exactly one back edge to the loop header.
            if(LoopToAnalyze.getNumBackEdges() != 1) {
                llvm::errs() << "Too many back edges for loop " << LoopToAnalyze << "\n";
                exit(1);
            }

            // The loop must also be dominated by its header and all edges from outside the loop
            // must point toward the loop header, but these are already requirements for "natural loops"
            // as recognized by LoopInfo.

            EWPTAliasAnalysisState ExitState;
            auto InductionVariable = LoopToAnalyze.getCanonicalInductionVariable();
            auto IVName = InductionVariable->getName().str();

            auto EntryState = MergeStates(getPredecessorStates(SuperFrame, &LoopHeader));

            bool FixedPointReached = false;
            for(unsigned I = 0; I < 3; I++) {
                // Create a new analysis frame for the analysis of the loop body.
                EWPTAliasAnalysisFrame SubFrame;
                SubFrame.EntryState = EntryState;
                SubFrame.RestrictToLoop = &LoopToAnalyze;
                SubFrame.SuperFrame = &SuperFrame;
                SubFrame.BlockOutStates = SuperFrame.BlockOutStates;
                SubFrame.Exit = &LoopHeader;

                // TODO: merge with the same check in iterativeControlFlowAnalysis()
                for(auto SI = succ_begin(&LoopHeader), E = succ_end(&LoopHeader); SI != E; SI++) {
                    auto Successor = *SI;
                    // Only process the successor if it's actually within the current loop.
                    if(SubFrame.RestrictToLoop->contains(Successor)) {
                        if(arePredecessorsProcessed(SubFrame, Successor) || LI->isLoopHeader(Successor)) {
                            SubFrame.BlocksToProcess.push(Successor);
                        }
                    }
                }

                // Start the sub-analysis with the loop header as "exit node"
                llvm::outs() << "Entering loop " << LoopToAnalyze << "\n";
                iterativeControlFlowAnalysis(SubFrame);
                llvm::outs() << "Exiting loop " << LoopToAnalyze << "\n";

                // Extract the out state of the loop header (later: all loop exits)
                ExitState = SubFrame.BlockOutStates[SubFrame.Exit];

                // Replace "i" by "i-" for the state of the loop header
                // Add a new "i"
                // Project out "i-"
                for(auto RootPair : ExitState.trackedRoots) {
                    auto& PointsToMapping = RootPair.second;
                    for(auto& Entry : PointsToMapping.Entries) {
                        llvm::outs() << "Mapping before aging: "; Entry.debugPrint(*this); llvm::outs() << "\n";

                        // Rename i to i- by adding a new param i- with ( i- = i) and projecting out i
                        auto Model = isl_space_params_alloc(IslContext, 2);
                        auto NewIVName = IVName + '-';
                        auto Identifier = isl_id_alloc(IslContext, IVName.c_str(), InductionVariable);
                        Model = isl_space_set_dim_id(Model, isl_dim_param, 0, Identifier);
                        Identifier = isl_id_alloc(IslContext, NewIVName.c_str(), InductionVariable);
                        Model = isl_space_set_dim_id(Model, isl_dim_param, 1, Identifier);
                        Entry.Mapping = isl_basic_map_align_params(Entry.Mapping, Model);

                        auto Constraint = isl_equality_alloc(isl_basic_map_get_local_space(Entry.Mapping));
                        Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_param, 0, -1);
                        Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_param, 1, 1);
                        Entry.Mapping = isl_basic_map_add_constraint(Entry.Mapping, Constraint);
                        llvm::outs() << "Mapping before projecting out: "; Entry.debugPrint(*this); llvm::outs() << "\n";
                        Entry.Mapping = isl_basic_map_project_out(Entry.Mapping, isl_dim_param, 0, 1);
                        llvm::outs() << "Mapping after renaming: "; Entry.debugPrint(*this); llvm::outs() << "\n";


                        // Add a new parameter i and add the constraint that i- < i
                        Model = isl_space_params_alloc(IslContext, 2);
                        Identifier = isl_id_alloc(IslContext, IVName.c_str(), InductionVariable);
                        Model = isl_space_set_dim_id(Model, isl_dim_param, 0, Identifier);
                        Identifier = isl_id_alloc(IslContext, NewIVName.c_str(), InductionVariable);
                        Model = isl_space_set_dim_id(Model, isl_dim_param, 1, Identifier);
                        Entry.Mapping = isl_basic_map_align_params(Entry.Mapping, Model);

                        Constraint = isl_inequality_alloc(isl_basic_map_get_local_space(Entry.Mapping));
                        Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_param, 0, 1);
                        Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_param, 1, -1);
                        Constraint = isl_constraint_set_constant_si(Constraint, -1);
                        Entry.Mapping = isl_basic_map_add_constraint(Entry.Mapping, Constraint);
                        Entry.Mapping = isl_basic_map_project_out(Entry.Mapping, isl_dim_param, 1, 1);

                        llvm::outs() << "Mapping after aging: "; Entry.debugPrint(*this); llvm::outs() << "\n";
                    }
                    llvm::outs() << "State after aging.\n";
                    ExitState.trackedRoots[RootPair.first] = PointsToMapping;
                    debugPrintEWPTs(ExitState);
                }

                if(ExitState.equals(EntryState)) {
                    llvm::outs() << "We have reached a fixed point.\n";
                    debugPrintEWPTs(ExitState);
                    EntryState = ExitState;
                    FixedPointReached = true;
                    break;
                }

                // Do another iteration to see if we're at a fixed point yet
                EntryState = ExitState;
            }

            if(FixedPointReached) {
                // Do binding.
                llvm::Value *UpperBound = getUpperBoundForLoop(LoopToAnalyze);
                auto UpperBoundName = UpperBound->getName().str();

                // i must be <= UpperBound

                for(auto RootPair : ExitState.trackedRoots) {
                    auto& PointsToMapping = RootPair.second;
                    for(auto& Entry : PointsToMapping.Entries) {
                        auto Model = isl_space_params_alloc(IslContext, 2);
                        auto Identifier = isl_id_alloc(IslContext, IVName.c_str(), InductionVariable);
                        Model = isl_space_set_dim_id(Model, isl_dim_param, 0, Identifier);
                        Identifier = isl_id_alloc(IslContext, UpperBoundName.c_str(), UpperBound);
                        Model = isl_space_set_dim_id(Model, isl_dim_param, 1, Identifier);
                        Entry.Mapping = isl_basic_map_align_params(Entry.Mapping, Model);

                        auto Constraint = isl_inequality_alloc(isl_basic_map_get_local_space(Entry.Mapping));
                        Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_param, 0, 1);
                        Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_param, 1, -1);
                        Entry.Mapping = isl_basic_map_add_constraint(Entry.Mapping, Constraint);
                        llvm::outs() << "Binding before projecting out: "; Entry.debugPrint(*this); llvm::outs() << "\n";
                        Entry.Mapping = isl_basic_map_project_out(Entry.Mapping, isl_dim_param, 0, 1);
                        llvm::outs() << "Binding after projecting out: "; Entry.debugPrint(*this); llvm::outs() << "\n";

                    }
                }

                return EntryState;
            }

            llvm::outs() << "Did not converge.\n";
            exit(1);
        }

        EWPTAliasAnalysisState MergeStates(std::vector<EWPTAliasAnalysisState*> StatesToMerge) {
            if(StatesToMerge.size() == 0) {
                return EWPTAliasAnalysisState();
            }
            EWPTAliasAnalysisState RetVal = *(StatesToMerge[0]);
            for(unsigned I = 1; I < StatesToMerge.size(); I++) {
                RetVal = RetVal.merge(*(StatesToMerge[I]));
            }
            return RetVal;
        }

        EWPTRoot MergeRoots(std::vector<EWPTRoot*> RootsToMerge) {
            if(RootsToMerge.size() == 0) {
                return EWPTRoot();
            }
            EWPTRoot RetVal = *(RootsToMerge[0]);
            for(unsigned I = 1; I < RootsToMerge.size(); I++) {
                RetVal = RetVal.merge(*(RootsToMerge[I]));
            }
            return RetVal;
        }

        void debugPrintEWPTs(EWPTAliasAnalysisState& State) {
            llvm::outs() << "EWPTs:\n";
            for(auto Pair : State.trackedRoots) {
                auto& RootValue = Pair.first;
                llvm::outs() << *RootValue << " [" << "\n";
                for(auto& Entry : Pair.second.Entries) {
                    llvm::outs() << "    " << *(Entry.SourceLocation) << " " << debugMappingToString(Entry.Mapping) << "\n";
                }
                llvm::outs() << " ]" << "\n";
            }
        }

        std::string debugSetToString(isl_basic_set *Set) {
            auto Printer = isl_printer_to_str(IslContext);
            isl_printer_print_basic_set(Printer, Set);
            char *Result = isl_printer_get_str(Printer);
            std::string RetVal(Result);
            isl_printer_free(Printer);
            free(Result);
            return RetVal;
        }

        std::string debugMappingToString(isl_basic_map *Map) {
            auto Printer = isl_printer_to_str(IslContext);
            Printer = isl_printer_print_basic_map(Printer, Map);
            char *Result = isl_printer_get_str(Printer);
            std::string RetVal(Result);
            isl_printer_free(Printer);
            free(Result);
            return RetVal;
        }

        void mergeParams(isl_basic_map*& First, isl_basic_map*& Second) {
            auto Space = isl_basic_map_get_space(First);
            Second = isl_basic_map_align_params(Second, Space);
            Space = isl_basic_map_get_space(Second);
            First = isl_basic_map_align_params(First, Space);
        }

        void mergeParams(isl_basic_set*& First, isl_basic_map*& Second) {
            auto Space = isl_basic_set_get_space(First);
            Second = isl_basic_map_align_params(Second, Space);
            Space = isl_basic_map_get_space(Second);
            First = isl_basic_set_align_params(First, Space);
        }

        /**
         * Create a mapping that embeds a smaller space into a larger space.
         *
         * For instance, we could embed the space (x_1, x_2) into the space (y_1, y_2, y_3)
         * with a mapping { (x_1, x_2) -> (x_1, x_2, _)
         *
         * Offset specifies from which index we should start embedding in the larger space. For instance,
         * if the offset is 1, then x_1 in the smaller space will be mapped to x_2 in the larger space
         * and so on.
         */
        isl_basic_map *constructEmbedderMapping(unsigned FromSize, unsigned ToSize, unsigned Offset = 0) {
            // Create the basic mapping itself
            auto EmbedderSpace = isl_space_alloc(IslContext, 0, FromSize, ToSize);
            auto EmbedderMapping = isl_basic_map_universe(EmbedderSpace);

            // Generate constraints that map each variable in the smaller space to the corresponding
            // variable in the larger space.
            // Some variables in the larger space will not be constrained.
            auto ConstraintSpace = isl_local_space_from_space(EmbedderSpace);
            for(unsigned VariableIndex = 0; VariableIndex < FromSize; VariableIndex++) {
                auto Constraint = isl_equality_alloc(isl_local_space_copy(ConstraintSpace));

                Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_in, VariableIndex, -1);
                Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_out, VariableIndex + Offset, 1);
                EmbedderMapping = isl_basic_map_add_constraint(EmbedderMapping, Constraint);
            }

            return EmbedderMapping;
        }

        /**
         * Generate a set of constraints for the subscript parameters of LeftHand under which
         * the heap object matches a heap object in RightHand.
         */
        isl_basic_set *generateAliasConstraints(EWPTEntry& LeftHand, EWPTEntry& RightHand) {
            if(LeftHand.SourceLocation != RightHand.SourceLocation) {
                auto IndexSpace = isl_space_alloc(IslContext, LeftHand.Depth, 0, 0);
                return isl_basic_set_empty(IndexSpace);
            }

            llvm::outs() << "LEFTHAND: " << debugMappingToString(LeftHand.Mapping) << "\n"; llvm::outs().flush();
            llvm::outs() << "RIGHTHAND: " << debugMappingToString(RightHand.Mapping) << "\n"; llvm::outs().flush();
            // Constrain the LeftHand mapping to those indices where it might map to a heap object in RightHand
            auto AliasMapping = isl_basic_map_intersect_range(isl_basic_map_copy(LeftHand.Mapping), isl_basic_map_range(isl_basic_map_copy(RightHand.Mapping)));
            llvm::outs() << "TEST: " << debugMappingToString(isl_basic_map_universe(isl_space_alloc(IslContext, 0, 1, 1))) << "\n"; llvm::outs().flush();

            llvm::outs() << "INTERSECTED:" << debugMappingToString(AliasMapping) << "\n"; llvm::outs().flush();


            // Extract the indices in this new constrained mapping as a set.
            auto AliasSet = isl_basic_map_domain(AliasMapping);
            return AliasSet;
        }

        /**
         * This function handles the meat of the transfer function p[x] = q
         *
         * With p[x] = q, what happens is the following:
         * - We look at each EWPT entry r pointing to p given some constraints
         * - We look at each EWPT entry s starting at q
         * - We create a new EWPT entry, combining the subscripts of r with a new subscript for x and the subscripts of s
         * - In this new EWPT entry, we apply the constraints for the subscripts of r to point to p
         * - We also carry over all the constraints for the subscripts of s
         * - We also add a constraint for x
         */
        EWPTEntry generateEntryFromHeapAssignment(int EntranceDepth, isl_basic_set *EntranceConstraints, EWPTEntry& AssigneeMapping, llvm::Value *BridgeValue) {
            llvm::outs() << "Generate Heap Assignment:: EntranceDepth = " << EntranceDepth << ", EntranceConstraints = " << debugSetToString(EntranceConstraints) << ", AssigneeMapping = " << debugMappingToString(AssigneeMapping.Mapping) << ", BridgeValue = " << *BridgeValue << "\n";

            // The new mapping will have the following subscripts:
            // - The subscripts from the entrance mapping
            // - One subscript for the bridge
            // - The subscripts from the assignee mapping
            auto InputSize = EntranceDepth + 1 + AssigneeMapping.Depth;
            auto NewSpace = isl_space_alloc(IslContext, 0, InputSize, AssigneeMapping.AmountOfIterators);
            auto NewMapping = isl_basic_map_universe(NewSpace);

            // Embed subscript parameters (x_1, ..., x_d) of our entrance mapping into the domain space.
            // For this we need to create a map (x_1, ..., x_d) -> (x_1, ..., x_d,  ...)

            // First we need to convert our set of constraints for the entrance mapping into a set of constraints
            // for the larger space of the new mapping. For this, we create an embedder mapping, which is just
            // an identity function from the smaller space into the larger space.
            auto AliasSetSize = isl_space_dim(isl_basic_set_get_space(EntranceConstraints), isl_dim_set);
            auto EmbedderMapping = constructEmbedderMapping(AliasSetSize, InputSize);

            mergeParams(EntranceConstraints, EmbedderMapping);
            auto FilterSpace = isl_basic_set_apply(isl_basic_set_copy(EntranceConstraints), EmbedderMapping);

            // Now we intersect our constraints for (x_1, ..., x_d) with the mapping, effectively adding these
            // constraints to the mapping we're generating.
            mergeParams(FilterSpace, NewMapping);
            NewMapping = isl_basic_map_intersect_domain(NewMapping, FilterSpace);

            // Next we add a bridge constraint to our mapping. The bridge constraint is the constraint for
            // 'x' in the expression p[x] = q
            if(auto BridgeConstant = dyn_cast<ConstantInt>(BridgeValue)) {
                auto BridgeConstraint = isl_equality_alloc(isl_local_space_from_space(isl_space_copy(isl_basic_map_get_space(NewMapping))));
                BridgeConstraint = isl_constraint_set_coefficient_si(BridgeConstraint, isl_dim_in, EntranceDepth, -1);
                BridgeConstraint = isl_constraint_set_constant_si(BridgeConstraint, BridgeConstant->getSExtValue());
                NewMapping = isl_basic_map_add_constraint(NewMapping, BridgeConstraint);
            } else {
                // TODO: parse the SCEV

                // First realign the isl map's parameters so that the free variable we're dealing with
                // becomes the first parameter.
                auto SubscriptValue = BridgeValue;
                auto ValueName = SubscriptValue->getName();
                auto Model = isl_space_params_alloc(IslContext, 1);
                auto Identifier = isl_id_alloc(IslContext, ValueName.str().c_str(), SubscriptValue);
                Model = isl_space_set_dim_id(Model, isl_dim_param, 0, Identifier);
                NewMapping = isl_basic_map_align_params(NewMapping, Model);
                // TODO: GetIndexForFreeVariable(SubscriptValue);

                // Next add a constraint for that parameter: x_d = param
                isl_local_space *LocalSpace = isl_local_space_from_space(isl_basic_map_get_space(NewMapping));
                isl_constraint *NewConstraint = isl_equality_alloc(LocalSpace);
                NewConstraint = isl_constraint_set_coefficient_si(NewConstraint, isl_dim_in, EntranceDepth, -1);
                NewConstraint = isl_constraint_set_coefficient_si(NewConstraint, isl_dim_param, 0, 1);
                NewMapping = isl_basic_map_add_constraint(NewMapping, NewConstraint);
            }

            // We need to embed the constraints of the asignee mapping into the mapping we're generating.
            // The assignee mapping has a range of (y_1, ..., y_k). We need the range to be our larger space,
            // so we simply prepend a projection to the assignee mapping, which projects
            // (x_1, ..., x_d, b, y_1, ..., y_k) to (y_1, ..., y_k). We can create this projection mapping
            // by inverting the equivalent embedder mapping that goes from
            // (y_1, ..., y_k) to (x_1, ..., x_d, b, y_1, ..., y_k)
            EmbedderMapping = constructEmbedderMapping(AssigneeMapping.Depth, InputSize, EntranceDepth + 1);
            EmbedderMapping = isl_basic_map_reverse(EmbedderMapping);
            // concatenate the functions: apply_range(g, f) = f(g)
            auto AssigneeMappingCopy = isl_basic_map_copy(AssigneeMapping.Mapping);
            mergeParams(EmbedderMapping, AssigneeMappingCopy);
            auto EmbeddedAssigneeMapping = isl_basic_map_apply_range(EmbedderMapping, AssigneeMappingCopy);

            llvm::outs() << "EmbeddedAssigneeMapping: " << debugMappingToString(EmbeddedAssigneeMapping) << "\n";
            llvm::outs().flush();
            llvm::outs() << "NewMapping: " << debugMappingToString(NewMapping) << "\n";
            llvm::outs().flush();
            // Now intersect this tail part into our generated mapping, essentially adding the constraints for
            // (y_1, ..., y_k)
            mergeParams(NewMapping, EmbeddedAssigneeMapping);
            NewMapping = isl_basic_map_intersect(NewMapping, EmbeddedAssigneeMapping);

            // Construct the EWPTEntry instance for the generated mapping.
            EWPTEntry NewEntry;
            NewEntry.AmountOfIterators = AssigneeMapping.AmountOfIterators;
            NewEntry.SourceLocation = AssigneeMapping.SourceLocation;
            NewEntry.Depth = InputSize;
            NewEntry.Mapping = NewMapping;

            llvm::outs() << "Result: " << debugMappingToString(NewMapping) << "\n";

            return NewEntry;
        }

        /**
         * Handle a heap assignment that involves a GEP, so something of the form
         * p[x] = q, where the address p[x] is calculated through a GEP instruction.
         */
        void handleGEPHeapAssignment(GetElementPtrInst *TargetGEP, llvm::Value *AssignedValue, EWPTAliasAnalysisState& State) {
            if(TargetGEP->getNumIndices() != 1) {
                // We can't deal with any number of indices but one.
                return; // TODO Error Handling
            }

            llvm::Value *Index = TargetGEP->idx_begin()->get();
            llvm::Value *BasePointer = TargetGEP->getPointerOperand()->stripPointerCasts();

            llvm::outs() << "Handling GEP Assignment" << *BasePointer << "[" << *Index << "] = " << *AssignedValue << "\n";

            // Check that we have an EWPT root associated with our base pointer.
            if(!State.trackedRoots.count(BasePointer)) {
                return; // TODO Error Handling
            }

            // Get all EWPT entries of depth 0.
            std::vector<EWPTEntry> ModifiedHeapObjects;
            if(!State.trackedRoots.count(BasePointer)) {
                return; // TODO: error handling
            }
            for(EWPTEntry& Entry : State.trackedRoots[BasePointer].Entries) {
                if(Entry.Depth == 0) {
                    llvm::outs() << "Found entry of depth 0 " << *(Entry.SourceLocation) << "\n";
                    ModifiedHeapObjects.push_back(Entry);
                }
            }

            // Find all EWPT entries that might alias with p
            // Generate a set of constraints under which the alias happens
            // Concatenate the found mapping under this set of constraints
            // with the EWPT of q

            for(EWPTEntry& ModifiedHeapObject : ModifiedHeapObjects) {
                for(auto& RootPair : State.trackedRoots) {
                    EWPTRoot& RootMapping = RootPair.second;

                    // Make a copy of the entries, as we may modify them.
                    auto Entries = RootMapping.Entries;
                    for(EWPTEntry& PossibleAlias : Entries) if(PossibleAlias.SourceLocation == ModifiedHeapObject.SourceLocation) {
                        auto EntranceConstraints = generateAliasConstraints(PossibleAlias, ModifiedHeapObject);
                        if(isl_basic_set_is_empty(EntranceConstraints)) {
                            continue;
                        }

                        llvm::outs() << "Found matching EWPT root " << *(RootPair.first) << " with constraints " << debugSetToString(EntranceConstraints) << "\n";
                        llvm::outs().flush();

                        // Now build new mappings from our set for aliasing x_1, ..., x_d, the
                        // transition subscript x_{d+1} = x, and each EWPT in q

                        // Make a copy, as we might be adding to these entries in the loop
                        if(!State.trackedRoots.count(AssignedValue)) {
                            // TODO: error message
                            return;
                        }
                        auto Entries = State.trackedRoots[AssignedValue].Entries;
                        for(EWPTEntry& TailMapping : Entries) {
                            llvm::outs() << "Found tail for " << *AssignedValue << ": "; TailMapping.debugPrint(*this); llvm::outs() << "\n"; llvm::outs().flush();
                            auto NewEntry = generateEntryFromHeapAssignment(PossibleAlias.Depth, EntranceConstraints, TailMapping, Index);
                            RootMapping.Entries.push_back(NewEntry);
                        }
                    }
                }
            }
        }

        void handleHeapAssignment(StoreInst *AssigningInstruction, EWPTAliasAnalysisState& State) {
            if(auto CurrentGEPInst = dyn_cast<GetElementPtrInst>(AssigningInstruction->getPointerOperand())) {
                handleGEPHeapAssignment(CurrentGEPInst, AssigningInstruction->getValueOperand()->stripPointerCasts(), State);
            }
        }

        void handleLoad(LoadInst *CurrentLoadInst, EWPTAliasAnalysisFrame &Frame, EWPTAliasAnalysisState& State) {
            llvm::outs() << "Handling Load\n";

            const SCEV *AccessFunction = SE->getSCEVAtScope(CurrentLoadInst->getPointerOperand(), Frame.RestrictToLoop);
            auto BasePointer = dyn_cast<SCEVUnknown>(SE->getPointerBase(AccessFunction));

            if (!BasePointer) {
                llvm::errs() << "Can not handle base pointer for " << *CurrentLoadInst << "\n";
                exit(1);
            }

            auto BaseValue = BasePointer->getValue();

            if (isa<UndefValue>(BaseValue)) {
                llvm::errs() << "Can not handle base value for " << *CurrentLoadInst << "\n";
                exit(1);
            }

            auto Offset = SE->getMinusSCEV(AccessFunction, BasePointer);

            // Check if we have an EWPT entry for our base pointer
            if (State.trackedRoots.count(BaseValue)) {
                auto LoadedFrom = State.trackedRoots[BaseValue];

                // We're indexing into the loaded EWPT, so apply a subscript
                EWPTRoot NewRoot = LoadedFrom.ApplySubscript(*this, Offset, Frame, State);
                State.trackedRoots[CurrentLoadInst] = NewRoot;
            }
        }

        EWPTAliasAnalysisState runOnBlock(BasicBlock &block, EWPTAliasAnalysisFrame& Frame, EWPTAliasAnalysisState& InState)
        {
            EWPTAliasAnalysisState RetValState = InState.clone();
            for(Instruction &CurrentInstruction : block.getInstList()) {
                llvm::outs() << "Handling instruction " << CurrentInstruction << "\n";

                // Case: p = q[x]
                if (LoadInst *CurrentLoadInst = dyn_cast<LoadInst>(&CurrentInstruction)) {
                    handleLoad(CurrentLoadInst, Frame, RetValState);
                }
                // Case: p[x] = q
                else if (StoreInst *CurrentStoreInst = dyn_cast<StoreInst>(&CurrentInstruction)) {
                    handleHeapAssignment(CurrentStoreInst, RetValState);
                }

                // Case: p = phi x, y
                else if (PHINode *CurrentPhiNode = dyn_cast<PHINode>(&CurrentInstruction)) {
                    // In the case of a phi node, we simply merge the EWPT tables of all
                    // incoming nodes. Note that the associated blocks must already have been
                    // processed by the iterative algorithm.

                    std::vector<EWPTRoot*> RootsToMerge;
                    for(unsigned I = 0; I < CurrentPhiNode->getNumIncomingValues(); I++) {
                        llvm::Value *IncomingValue = CurrentPhiNode->getIncomingValue(I);
                        EWPTRoot& Root = RetValState.trackedRoots[IncomingValue];
                        RootsToMerge.push_back(&Root);
                    }
                    EWPTRoot NewRoot = MergeRoots(RootsToMerge);
                    RetValState.trackedRoots[&CurrentInstruction] = NewRoot;
                }

                // Case: p = malloc();
                else if (llvm::isNoAliasCall(&CurrentInstruction)) {
                    // Create a new EWPT with just the one entry.
                    EWPTRoot Root;
                    EWPTEntry Entry;

                    auto Iterators = Frame.GetCurrentLoopIterators();

                    Entry.AmountOfIterators = Iterators.size();
                    Entry.SourceLocation = &CurrentInstruction;
                    Entry.Depth = 0;

                    auto Space = isl_space_alloc(IslContext, Entry.AmountOfIterators, 0, Entry.AmountOfIterators);

                    for(unsigned I = 0; I < Iterators.size(); I++) {
                        Entry.GetIndexForFreeVariable(Iterators[I]);

                        auto ValueName = Iterators[I]->getName();
                        auto Identifier = isl_id_alloc(IslContext, ValueName.str().c_str(), Iterators[I]);
                        Space = isl_space_set_dim_id(Space, isl_dim_param, I, Identifier);
                    }

                    Entry.Mapping = isl_basic_map_universe(isl_space_copy(Space));

                    for(unsigned I = 0; I < Iterators.size(); I++) {
                        // For each iterator i we need a constraint that
                        // a_i = i
                        auto Constraint = isl_equality_alloc(isl_local_space_from_space(isl_space_copy(Space)));

                        Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_param, I, -1);
                        Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_out, I, 1);
                        Entry.Mapping = isl_basic_map_add_constraint(Entry.Mapping, Constraint);
                    }

                    Root.Entries.push_back(Entry);
                    RetValState.trackedRoots[&CurrentInstruction] = Root;

                    llvm::outs() << "Added new 0 depth entry for " << CurrentInstruction << "\n";
                    llvm::outs() << "New constraints: " << debugMappingToString(Entry.Mapping) << "\n";
                }
            }

            return RetValState;
        }

        void getAnalysisUsage(AnalysisUsage &AU) const
        {
            AliasAnalysis::getAnalysisUsage(AU);
            AU.addRequired<AliasAnalysis>();
            AU.addRequired<LoopInfoWrapperPass>();
            AU.addRequired<ScalarEvolution>();
            AU.setPreservesAll();
        }

        void *getAdjustedAnalysisPointer(const void *ID) override
        {
            if (ID == &AliasAnalysis::ID) {
                return (AliasAnalysis *)this;
            }
            return this;
        }

        isl_ctx *getIslContext() {
            return IslContext;
        }
};

void EWPTEntry::InternalApplySubscript(EWPTAliasAnalysis& Analysis, const SCEV *Subscript, EWPTAliasAnalysisFrame &Frame, EWPTAliasAnalysisState& State) {
    // We need to substitute and project out the first parameter in the input dimension.

    llvm::outs() << "Attempting to apply subscript " << *Subscript << " to "; this->debugPrint(Analysis); llvm::outs() << "\n";

    if(auto SubscriptUnknown = dyn_cast<SCEVUnknown>(Subscript)) {
        auto SubscriptValue = SubscriptUnknown->getValue();
        if(auto ConstSubscript = dyn_cast<llvm::ConstantInt>(SubscriptValue)) {
            // Generate a constraint of the form x_1 = c, where c is a constant and x_1
            // is the first mapping parameter that we're projecting out.
            int64_t ConstValue = ConstSubscript->getSExtValue();
            llvm::outs() << "Adding constraint x_1=" << ConstValue << " to " << Analysis.debugMappingToString(Mapping) << "\n";
            isl_local_space *LocalSpace = isl_local_space_from_space(isl_basic_map_get_space(Mapping));
            isl_constraint *NewConstraint = isl_equality_alloc(LocalSpace);
            NewConstraint = isl_constraint_set_coefficient_si(NewConstraint, isl_dim_in, 0, -1);
            NewConstraint = isl_constraint_set_constant_si(NewConstraint, ConstValue);
            Mapping = isl_basic_map_add_constraint(Mapping, NewConstraint);
        }
        else {
            // TODO: parse the SCEV

            // Have to treat it as parameter.

            // First realign the isl map's parameters so that the free variable we're dealing with
            // becomes the first parameter.
            auto ValueName = SubscriptValue->getName();
            auto Model = isl_space_params_alloc(Analysis.IslContext, 1);
            auto Identifier = isl_id_alloc(Analysis.IslContext, ValueName.str().c_str(), SubscriptValue);
            Model = isl_space_set_dim_id(Model, isl_dim_param, 0, Identifier);
            Mapping = isl_basic_map_align_params(Mapping, Model);
            GetIndexForFreeVariable(SubscriptValue);

            // Next add a constraint for that first parameter: x_1 = param
            isl_local_space *LocalSpace = isl_local_space_from_space(isl_basic_map_get_space(Mapping));
            isl_constraint *NewConstraint = isl_equality_alloc(LocalSpace);
            NewConstraint = isl_constraint_set_coefficient_si(NewConstraint, isl_dim_in, 0, -1);
            NewConstraint = isl_constraint_set_coefficient_si(NewConstraint, isl_dim_param, 0, 1);
            Mapping = isl_basic_map_add_constraint(Mapping, NewConstraint);
        }
    }

    // Project out the first input dimension.
    Mapping = isl_basic_map_project_out(Mapping, isl_dim_in, 0, 1);
    Depth = Depth - 1;

    llvm::outs() << "After subscript application: "; this->debugPrint(Analysis); llvm::outs() << "\n";
}

void EWPTEntry::debugPrint(EWPTAliasAnalysis &Analysis) {
    llvm::outs() << "<" << *SourceLocation << " : " << Analysis.debugMappingToString(Mapping) << ">(Depth:" << Depth << ")\n";
}

char EWPTAliasAnalysis::ID = 0;

INITIALIZE_AG_PASS_BEGIN(EWPTAliasAnalysis, AliasAnalysis, "ewpt-aa",
                                   "Element-Wise-Points-To-Mapping based Alias Analysis",
                                                      false, true, false)
INITIALIZE_AG_PASS_END(EWPTAliasAnalysis, AliasAnalysis, "ewpt-aa",
                                           "Element-Wise-Points-To-Mapping based Alias Analysis",
                                                              false, true, false)
