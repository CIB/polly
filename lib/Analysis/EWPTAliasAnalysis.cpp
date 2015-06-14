#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instruction.h"

#include <isl/flow.h>
#include <isl/constraint.h>
#include <isl/ctx.h>
#include <isl/set.h>
#include <isl/map.h>
#include <isl/printer.h>
#include <isl/space.h>
#include <isl/local_space.h>
#include <isl/val.h>
#include <isl/aff.h>
#include <isl/options.h>

#include "polly/EWPTAliasAnalysis.h"


#define DEBUG_PRINT_ALIAS 1

using namespace llvm;

namespace ewpt {

// ============================
// HeapNameId
// ============================

bool operator<(const HeapNameId& l, const HeapNameId& r )
{
    return (l.hasType < r.hasType) ||
            ((l.hasType == r.hasType) && (l.SourceLocation < r.SourceLocation));
}

bool operator==(const HeapNameId& l, const HeapNameId& r )
{
    return (l.hasType == r.hasType) &&
           (l.SourceLocation == r.SourceLocation);
}

bool operator!=(const HeapNameId& l, const HeapNameId& r )
{
    return !(l == r);
}


// ============================
// EWPTEntry
// ============================

EWPTEntry::EWPTEntry(const EWPTEntry& Other) {
    *this = Other;
}

EWPTEntry::~EWPTEntry() {
    printf("Freeing %x\n", Mapping);
    isl_map_free(Mapping);
}

EWPTEntry& EWPTEntry::operator=(const EWPTEntry& Other) {
    this->Rank = Other.Rank;
    this->AmountOfIterators = Other.AmountOfIterators;
    this->HeapIdentifier = Other.HeapIdentifier;
    if(Other.Mapping != NULL) {
        this->Mapping = isl_map_copy(Other.Mapping);
        printf("Copying %x\n", Mapping);
    } else {
        this->Mapping = NULL;
    }
    return *this;
}

EWPTEntry EWPTEntry::merge(EWPTEntry& Other) {
    llvm::outs() << "Values: " << this->HeapIdentifier.toString() << " - " << Other.HeapIdentifier.toString() << "\n";
    llvm::outs() << "Ranks: " << this->Rank << " - " << Other.Rank << "\n";
    llvm::outs() << "Iters:" << this->AmountOfIterators << " - " << Other.AmountOfIterators << "\n";
    assert(Rank == Other.Rank && AmountOfIterators == Other.AmountOfIterators);

    EWPTEntry RetVal = *this;
    auto Mapping1 = isl_map_copy(Mapping);
    auto Mapping2 = isl_map_copy(Other.Mapping);
    isl_map_free(RetVal.Mapping);
    RetVal.Mapping = isl_map_union(Mapping1, Mapping2);
    return RetVal;
}

EWPTEntry EWPTEntry::intersect(EWPTEntry& Other) {
    assert(Rank == Other.Rank && AmountOfIterators == Other.AmountOfIterators);

    EWPTEntry RetVal = *this;
    auto Mapping1 = isl_map_copy(Mapping);
    auto Mapping2 = isl_map_copy(Other.Mapping);
    isl_map_free(RetVal.Mapping);
    RetVal.Mapping = isl_map_intersect(Mapping1, Mapping2);
    return RetVal;
}


bool EWPTEntry::ApplySubscript(EWPTAliasAnalysis& Analysis, const SCEV* Subscript, EWPTAliasAnalysisFrame &Frame, EWPTAliasAnalysisState& State, EWPTEntry& OutEntry) const {
    EWPTEntry Copy = *this;
    if(Copy.InternalApplySubscript(Analysis, Subscript, Frame, State)) {
        OutEntry = Copy;
        return true;
    } else {
        return false;
    }
}

bool EWPTEntry::InternalApplySubscript(EWPTAliasAnalysis& Analysis, const SCEV *Subscript, EWPTAliasAnalysisFrame &Frame, EWPTAliasAnalysisState& State) {
    // We need to substitute and project out the first parameter in the input dimension.

    llvm::outs() << "Attempting to apply subscript " << *Subscript << " to "; this->debugPrint(Analysis); llvm::outs() << "\n";

    isl_pw_aff *SubscriptAff = SCEVAffinator::getPwAff(&Analysis, Subscript, Analysis.IslContext);
    if(!SubscriptAff) {
        return false;
    }
    isl_set *SubscriptSet = isl_map_range(isl_map_from_pw_aff(SubscriptAff));

    // Currently we have a set of the form POINTER_SIZE * i, we need to convert this to just i
    // The division is possible because we ensured an alignment that is a multiple of the pointer size.
    std::string consString = "{ [i] -> [o] : i = " + std::to_string(Analysis.DL->getPointerSize()) + "* o}";
    auto DivisionMapping = isl_map_read_from_str(Analysis.IslContext, consString.c_str());
    SubscriptSet = isl_set_apply(SubscriptSet, DivisionMapping);

    auto EmbedderMapping = Analysis.constructEmbedderMapping(1, Rank, 0);
    SubscriptSet = isl_set_apply(SubscriptSet, EmbedderMapping);

    llvm::outs() << "Subscript set: " << Analysis.debugSetToString(SubscriptSet) << "\n";
    Analysis.mergeParams(SubscriptSet, Mapping);
    Mapping = isl_map_intersect_domain(Mapping, SubscriptSet);

    // Project out the first input dimension.
    Mapping = isl_map_project_out(Mapping, isl_dim_in, 0, 1);
    Rank = Rank - 1;

    llvm::outs() << "After subscript application: "; this->debugPrint(Analysis); llvm::outs() << "\n";

    return true;
}

void EWPTEntry::debugPrint(EWPTAliasAnalysis &Analysis) {
    llvm::outs() << "<" << HeapIdentifier.toString();
    if(Mapping != NULL) {
        llvm::outs() << " : " << Analysis.debugMappingToString(Mapping);
    }
    llvm::outs() << ">(Depth:" << Rank << ")\n";
}

bool EWPTEntry::isSingleValued() {
    return isl_map_is_single_valued(Mapping);
}

// ==============================
// EWPTRoot
// ==============================

bool EWPTRoot::ApplySubscript(EWPTAliasAnalysis& Analysis, const SCEV *Subscript, EWPTAliasAnalysisFrame &Frame, EWPTAliasAnalysisState& State, EWPTRoot& OutRoot) {
    EWPTRoot RetVal;
    for(auto& EntryPair : Entries) {
        auto NewKey = EntryPair.first;
        NewKey.first = NewKey.first - 1;
        auto& Entry = EntryPair.second;
        if(Entry.Rank > 0) {
            EWPTEntry Result;
            bool Success = Entry.ApplySubscript(Analysis, Subscript, Frame, State, Result);
            if(Success) {
                RetVal.Entries[NewKey] = Result;
            } else {
                return false;
            }
        }
    }
    OutRoot = RetVal;
    return true;
}

std::vector< std::pair<unsigned, HeapNameId> > EWPTRoot::getCombinedKeys(EWPTRoot& Other) {
    std::vector< std::pair<unsigned, HeapNameId> > AllKeys;
    for(auto& EntryPair : Entries) {
        AllKeys.push_back(EntryPair.first);
    }
    for(auto& EntryPair : Other.Entries) {
        AllKeys.push_back(EntryPair.first);
    }
    return AllKeys;
}

EWPTRoot EWPTRoot::merge(EWPTRoot& Other) {
    EWPTRoot RetVal;

    auto AllKeys = getCombinedKeys(Other);
    for(auto EntryKey : AllKeys) {
        EWPTEntry MergedEntry;
        if(!Entries.count(EntryKey)) {
            MergedEntry = Other.Entries[EntryKey];
        } else if(!Other.Entries.count(EntryKey)) {
            MergedEntry = Entries[EntryKey];
        } else {
            MergedEntry = Entries[EntryKey].merge(Other.Entries[EntryKey]);
        }
        RetVal.Entries[EntryKey] = MergedEntry;
    }
    return RetVal;
}

EWPTRoot EWPTRoot::intersect(EWPTRoot& Other, unsigned Rank) {
    EWPTRoot RetVal;

    auto AllKeys = getCombinedKeys(Other);
    for(auto EntryKey : AllKeys) {
        if(EntryKey.first != Rank) {
            continue;
        }
        if(!Entries.count(EntryKey) || !Other.Entries.count(EntryKey)) {
            continue;
        } else {
            auto IntersectedEntry = Entries[EntryKey].intersect(Other.Entries[EntryKey]);
            if(!isl_map_is_empty(IntersectedEntry.Mapping)) {
                RetVal.Entries[EntryKey] = IntersectedEntry;
            }
        }
    }
    return RetVal;
}

bool EWPTRoot::equals(EWPTRoot& Other) {
    auto AllKeys = getCombinedKeys(Other);
    for(auto& EntryKey : AllKeys) {
        if(!Entries.count(EntryKey) || !Other.Entries.count(EntryKey)) {
            return false;
        }
        if(!isl_map_is_equal(Entries[EntryKey].Mapping, Other.Entries[EntryKey].Mapping)) {
            return false;
        }
    }
    return true;
}

std::vector<EWPTEntry*> EWPTRoot::getEntriesAtRank(unsigned Rank) {
    std::vector<EWPTEntry*> RetVal;
    for(auto& Iter : Entries) {
        if(Iter.first.first == Rank) {
            RetVal.push_back(&Iter.second);
        }
    }
    return RetVal;
}

EWPTEntry *EWPTRoot::isSingleValued() {
    auto EntriesAtRankZero = getEntriesAtRank(0);
    if(EntriesAtRankZero.size() != 1) {
        return NULL;
    }
    if(EntriesAtRankZero[0]->isSingleValued()) {
        return EntriesAtRankZero[0];
    } else {
        return NULL;
    }
}

void EWPTRoot::debugPrint(EWPTAliasAnalysis &Analysis) {
    llvm::outs() << "{\n";
    for(auto& EntryPair : Entries) {
        auto& Entry = EntryPair.second;
        llvm::outs() << "    (" << Entry.HeapIdentifier.toString() << ", " << Entry.Rank << ":" << EntryPair.first.first << ")\t->\t" << Analysis.debugMappingToString(Entry.Mapping) << "\n";
    }
    llvm::outs() << "}" << "\n";
}

// ==================================
// EWPTAliasAnalysisState
// ==================================

EWPTAliasAnalysisState EWPTAliasAnalysisState::merge(EWPTAliasAnalysisState& Other) {
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

bool EWPTAliasAnalysisState::equals(EWPTAliasAnalysisState& Other) {
    for(auto& Pair : trackedRoots) {
        auto Entry = Pair.second;
        auto OtherEntry = Other.trackedRoots[Pair.first];

        if(!Entry.equals(OtherEntry)) {
            return false;
        }
    }
    return true;
}

// =======================================
// EWPTAliasAnalysisFrame
// =======================================

std::vector<llvm::Value*> EWPTAliasAnalysisFrame::GetCurrentLoopIterators() {
    std::vector<llvm::Value*> RetVal;
    EWPTAliasAnalysisFrame *Current = this;
    while(Current->SuperFrame != NULL) {
        RetVal.push_back(Current->RestrictToLoop->getCanonicalInductionVariable());
        Current = Current->SuperFrame;
    };
    return RetVal;
}

// =======================================
// EWPTAliasAnalysis
// =======================================

bool EWPTAliasAnalysis::runOnFunction(Function &F)
{
    llvm::outs() << "Runnoing on function " << F.getName() << "\n";

    // Clean up.
    Frame = EWPTAliasAnalysisFrame();

    // Initialization.
    SE = &getAnalysis<ScalarEvolution>();
    LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    DL = &getAnalysis<DataLayoutPass>().getDataLayout();

    InitializeAliasAnalysis(this);

    // The actual analysis.
    auto BeginBlock = &(F.getEntryBlock());
    Frame.BeginBlocks.insert(BeginBlock);
    Frame.RestrictToLoop = NULL;
    if(!iterativeControlFlowAnalysis(Frame)) {
        Frame.BlockOutStates.clear();
    }

    return false;
}

bool EWPTAliasAnalysis::arePredecessorsProcessed(EWPTAliasAnalysisFrame& Frame, BasicBlock* ToCheck) {
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

std::vector<EWPTAliasAnalysisState*> EWPTAliasAnalysis::getPredecessorStates(EWPTAliasAnalysisFrame& Frame, BasicBlock *Current) {
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

bool EWPTAliasAnalysis::iterativeControlFlowAnalysis(EWPTAliasAnalysisFrame& Frame) {
    for(auto BeginBlock : Frame.BeginBlocks) {
        Frame.BlocksToProcess.push(BeginBlock);
    }
    while(Frame.BlocksToProcess.size()) {
        BasicBlock *Current = Frame.BlocksToProcess.front();
        Frame.BlocksToProcess.pop();

        llvm::outs() << "Predecessor states:\n";
        for(auto State : getPredecessorStates(Frame, Current)) {
            debugPrintEWPTs(*State);
        }
        auto StartWithState = MergeStates(getPredecessorStates(Frame, Current));
        if(!runOnBlock(*Current, Frame, StartWithState, Frame.BlockOutStates[Current])) {
            return false;
        }

        // Don't process the successors of an exit.
        if(Current == Frame.Exit) {
            continue;
        }

        llvm::outs() << "LI->isLoopHeader(Current)" << LI->isLoopHeader(Current) << "\n";
        llvm::outs() << "LI " << LI << "\n";
        if(Frame.RestrictToLoop) {
            llvm::outs() << "Loop: " << *Frame.RestrictToLoop;
        }
        llvm::outs() << *Current << "\n";
        llvm::outs() << Current << "\n";

        if(LI->isLoopHeader(Current)) {
            llvm::outs() << "Previously queued: " << Frame.BlocksToProcess.size() << "\n";
            Loop* LoopToAnalyze = LI->getLoopFor(Current);
            bool Success = handleLoop(Frame, *Current, *LoopToAnalyze, Frame.BlockOutStates[Current]);
            if(!Success) {
                llvm::errs() << "Failed to handle loop\n";
                return false;
            }

            llvm::outs() << "Currently queued: " << Frame.BlocksToProcess.size() << "\n";
            if(Frame.BlocksToProcess.size()) {
                llvm::outs() << *Frame.BlocksToProcess.front() << "\n";
            }
            llvm::outs() << "Pushing successors of loop header.\n";

            // Only add the successors that are not part of the loop.
            for(auto SI = succ_begin(Current), E = succ_end(Current); SI != E; SI++) {
                // Check that this successor now has all requirements.
                auto Successor = *SI;
                // Only process the successor if it's not within the current loop.
                if(!LoopToAnalyze->contains(Successor)) {
                    llvm::outs() << *Successor << "\n";
                    Frame.BlocksToProcess.push(Successor);
                }
            }

            continue;
        } else if(!arePredecessorsProcessed(Frame, Current)) {
            llvm::outs() << "Trying to process block with unprocessed predecessors.";
            exit(1);
        } else {
            llvm::outs() << "Pushing successors of regular block.\n";
            // Once this frame is done, try processing successors
            for(auto SI = succ_begin(Current), E = succ_end(Current); SI != E; SI++) {
                // Check that this successor now has all requirements.
                auto Successor = *SI;
                // Only process the successor if it's actually within the current loop.
                if(!Frame.RestrictToLoop || Frame.RestrictToLoop->contains(Successor)) {
                    if(arePredecessorsProcessed(Frame, Successor) || LI->isLoopHeader(Successor)) {
                        llvm::outs() << *Successor << "\n";
                        Frame.BlocksToProcess.push(Successor);
                    }
                }
            }
        }
    }

    return true;
}

llvm::Value *EWPTAliasAnalysis::getUpperBoundForLoop(Loop& LoopToAnalyze) {
    BasicBlock* LoopHeader = LoopToAnalyze.getHeader();
    for(auto& Instruction : LoopHeader->getInstList()) {
        //llvm::outs() << "Checking " << Instruction << "\n";
        if(auto Comparison = dyn_cast<ICmpInst>(&Instruction)) {
            if(
                Comparison->getOperand(0) == LoopToAnalyze.getCanonicalInductionVariable() &&
                Comparison->isFalseWhenEqual()
            ) {
                return Comparison->getOperand(1);
            }
        }
    }

    llvm::outs() << "No upper bound found for loop.\n";
    exit(1);
}

bool EWPTAliasAnalysis::handleLoop(EWPTAliasAnalysisFrame& SuperFrame, BasicBlock& LoopHeader, Loop& LoopToAnalyze, EWPTAliasAnalysisState& RetVal) {
    // We can only handle loops of a specific type, check these properties first.

    // It must have a canonical induction variable, i.e. for(i = 0; i < n; i++)
    if(!LoopToAnalyze.getCanonicalInductionVariable()) {
        llvm::errs() << "No canonical induction variable found for loop " << LoopToAnalyze << ", consider prepending the -indvars pass.\n";
        return false;
    }

    // It must have exactly one back edge to the loop header.
    if(LoopToAnalyze.getNumBackEdges() != 1) {
        llvm::outs() << "Too many back edges for loop " << LoopToAnalyze << "\n";
        return false;
    }

    llvm::outs() << "(loop) Entering loop " << LoopHeader.getName() << "\n";

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
        //llvm::outs() << "Entering loop " << LoopToAnalyze << "\n";
        bool Success = iterativeControlFlowAnalysis(SubFrame);
        if(!Success) {
            llvm::outs() << "Control flow analysis in sub-frame failed\n";
            return false;
        }
        //llvm::outs() << "Exiting loop " << LoopToAnalyze << "\n";

        // Extract the out state of the loop header (later: all loop exits)
        ExitState = SubFrame.BlockOutStates[SubFrame.Exit];

        // Before aging and binding, we need to propagate all the states of the
        // loop body blocks to the super frame.
        for(auto& Pair : SubFrame.BlockOutStates) {
            if(!LoopToAnalyze.contains(Pair.first)) {
                continue;
            }
            if(Pair.first != &LoopHeader) {
                // Merge it into the super frame.
                if(!SuperFrame.BlockOutStates.count(Pair.first)) {
                    SuperFrame.BlockOutStates[Pair.first] = Pair.second;
                } else {
                    SuperFrame.BlockOutStates[Pair.first] = SuperFrame.BlockOutStates[Pair.first].merge(Pair.second);
                }
                llvm::outs() << "Propagating up \n" << Pair.first->getName() << ":::::\n";
                debugPrintEWPTs(SuperFrame.BlockOutStates[Pair.first]);
                llvm::outs() << "\n";
            }
        }

        //llvm::outs() << "State before aging.\n";
        //debugPrintEWPTs(ExitState);

        // Replace "i" by "i-" for the state of the loop header
        // Add a new "i"
        // Project out "i-"
        for(auto& RootPair : ExitState.trackedRoots) {
            auto& PointsToMapping = RootPair.second;
            for(auto& EntryPair : PointsToMapping.Entries) {
                auto& Entry = EntryPair.second;
                //llvm::outs() << "Mapping before aging: "; Entry.debugPrint(*this); llvm::outs() << "\n";

                // Rename i to i- by adding a new param i- with ( i- = i) and projecting out i
                auto Model = isl_space_params_alloc(IslContext, 2);
                auto NewIVName = IVName + '-';
                auto Identifier = isl_id_alloc(IslContext, IVName.c_str(), InductionVariable);
                Model = isl_space_set_dim_id(Model, isl_dim_param, 0, Identifier);
                Identifier = isl_id_alloc(IslContext, NewIVName.c_str(), InductionVariable);
                Model = isl_space_set_dim_id(Model, isl_dim_param, 1, Identifier);
                Entry.Mapping = isl_map_align_params(Entry.Mapping, Model);

                auto Constraint = isl_equality_alloc(isl_local_space_from_space(isl_map_get_space(Entry.Mapping)));
                Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_param, 0, -1);
                Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_param, 1, 1);
                Entry.Mapping = isl_map_add_constraint(Entry.Mapping, Constraint);
                //llvm::outs() << "Mapping before projecting out: "; Entry.debugPrint(*this); llvm::outs() << "\n";
                Entry.Mapping = isl_map_project_out(Entry.Mapping, isl_dim_param, 0, 1);
                //llvm::outs() << "Mapping after renaming: "; Entry.debugPrint(*this); llvm::outs() << "\n";


                // Add a new parameter i and add the constraint that i- < i
                Model = isl_space_params_alloc(IslContext, 2);
                Identifier = isl_id_alloc(IslContext, IVName.c_str(), InductionVariable);
                Model = isl_space_set_dim_id(Model, isl_dim_param, 0, Identifier);
                Identifier = isl_id_alloc(IslContext, NewIVName.c_str(), InductionVariable);
                Model = isl_space_set_dim_id(Model, isl_dim_param, 1, Identifier);
                Entry.Mapping = isl_map_align_params(Entry.Mapping, Model);

                Constraint = isl_inequality_alloc(isl_local_space_from_space(isl_map_get_space(Entry.Mapping)));
                Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_param, 0, 1);
                Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_param, 1, -1);
                Constraint = isl_constraint_set_constant_si(Constraint, -1);
                Entry.Mapping = isl_map_add_constraint(Entry.Mapping, Constraint);
                Entry.Mapping = isl_map_project_out(Entry.Mapping, isl_dim_param, 1, 1);

                // Project out parameter dimensions that aren't constant, unless they're the iterator.
                for(unsigned i = 0; i < isl_space_dim(isl_map_get_space(Entry.Mapping), isl_dim_param); i++) {
                    auto DimIdentifier = isl_space_get_dim_id(isl_map_get_space(Entry.Mapping), isl_dim_param, i);
                    llvm::Value *Variable = (llvm::Value*) isl_id_get_user(DimIdentifier);
                    isl_id_free(DimIdentifier);

                    // Check if it's constant
                    if(Variable == InductionVariable) {
                        continue;
                    }
                    if(!SubFrame.RestrictToLoop->isLoopInvariant(Variable)) {
                        // Not constant, must project it out.
                        Entry.Mapping = isl_map_project_out(Entry.Mapping, isl_dim_param, i, 1);
                        i--;
                    }
                }

                ExitState.trackedRoots[RootPair.first].Entries[EntryPair.first] = Entry;
            }
        }

        if(ExitState.equals(EntryState)) {
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

        for(auto& RootPair : EntryState.trackedRoots) {
            auto& PointsToMapping = RootPair.second;
            for(auto& EntryPair : PointsToMapping.Entries) {
                auto& Entry = EntryPair.second;
                auto Model = isl_space_params_alloc(IslContext, 2);
                auto Identifier = isl_id_alloc(IslContext, IVName.c_str(), InductionVariable);
                Model = isl_space_set_dim_id(Model, isl_dim_param, 0, Identifier);
                Identifier = isl_id_alloc(IslContext, UpperBoundName.c_str(), UpperBound);
                Model = isl_space_set_dim_id(Model, isl_dim_param, 1, Identifier);
                Entry.Mapping = isl_map_align_params(Entry.Mapping, Model);

                auto Constraint = isl_inequality_alloc(isl_local_space_from_space(isl_map_get_space(Entry.Mapping)));
                Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_param, 0, -1);
                Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_param, 1, 1);
                Entry.Mapping = isl_map_add_constraint(Entry.Mapping, Constraint);
                //llvm::outs() << "Binding before projecting out: "; Entry.debugPrint(*this); llvm::outs() << "\n";
                Entry.Mapping = isl_map_project_out(Entry.Mapping, isl_dim_param, 0, 1);
                //llvm::outs() << "Binding after projecting out: "; Entry.debugPrint(*this); llvm::outs() << "\n";

                EntryState.trackedRoots[RootPair.first].Entries[EntryPair.first] = Entry;
            }
        }

        llvm::outs() << "(loop) Exiting loop " << LoopHeader.getName() << "\n";
        RetVal = EntryState;
        return true;
    }

    llvm::errs() << "Did not converge.\n";
    return false;
}

EWPTAliasAnalysisState EWPTAliasAnalysis::MergeStates(std::vector<EWPTAliasAnalysisState*> StatesToMerge) {
    if(StatesToMerge.size() == 0) {
        return EWPTAliasAnalysisState();
    }
    EWPTAliasAnalysisState RetVal = *(StatesToMerge[0]);
    for(unsigned I = 1; I < StatesToMerge.size(); I++) {
        RetVal = RetVal.merge(*(StatesToMerge[I]));
    }
    return RetVal;
}

EWPTRoot EWPTAliasAnalysis::MergeRoots(std::vector<EWPTRoot> RootsToMerge) {
    if(RootsToMerge.size() == 0) {
        return EWPTRoot();
    }
    EWPTRoot RetVal = RootsToMerge[0];
    for(unsigned I = 1; I < RootsToMerge.size(); I++) {
        RetVal = RetVal.merge(RootsToMerge[I]);
    }
    return RetVal;
}

void EWPTAliasAnalysis::debugPrintEWPTs(EWPTAliasAnalysisState& State) {
    llvm::outs() << "EWPTs:\n";
    for(auto& Pair : State.trackedRoots) {
        if(Pair.second.Entries.size() == 0) {
            continue;
        }

        auto& RootValue = Pair.first;
        llvm::outs() << "<" << *RootValue << "> -> ";

        Pair.second.debugPrint(*this);
    }
}

isl_id *EWPTAliasAnalysis::getIslIdForValue(Value *val) {
    return isl_id_alloc(IslContext, val->getName().str().c_str(), val);
}

std::string EWPTAliasAnalysis::debugSetToString(isl_set *Set) {
    auto Printer = isl_printer_to_str(IslContext);
    isl_printer_print_set(Printer, Set);
    char *Result = isl_printer_get_str(Printer);
    std::string RetVal(Result);
    isl_printer_free(Printer);
    free(Result);
    return RetVal;
}

std::string EWPTAliasAnalysis::debugMappingToString(isl_map *Map) {
    auto Printer = isl_printer_to_str(IslContext);
    Printer = isl_printer_print_map(Printer, Map);
    char *Result = isl_printer_get_str(Printer);
    std::string RetVal(Result);
    isl_printer_free(Printer);
    free(Result);
    return RetVal;
}

void EWPTAliasAnalysis::mergeParams(isl_map*& First, isl_map*& Second) {
    auto Space = isl_map_get_space(First);
    Second = isl_map_align_params(Second, Space);
    Space = isl_map_get_space(Second);
    First = isl_map_align_params(First, Space);
}

void EWPTAliasAnalysis::mergeParams(isl_set*& First, isl_map*& Second) {
    auto Space = isl_set_get_space(First);
    Second = isl_map_align_params(Second, Space);
    Space = isl_map_get_space(Second);
    First = isl_set_align_params(First, Space);
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
isl_map *EWPTAliasAnalysis::constructEmbedderMapping(unsigned FromSize, unsigned ToSize, unsigned Offset) {
    // Create the basic mapping itself
    auto EmbedderSpace = isl_space_alloc(IslContext, 0, FromSize, ToSize);
    auto EmbedderMapping = isl_map_universe(EmbedderSpace);

    // Generate constraints that map each variable in the smaller space to the corresponding
    // variable in the larger space.
    // Some variables in the larger space will not be constrained.
    auto ConstraintSpace = isl_local_space_from_space(EmbedderSpace);
    for(unsigned VariableIndex = 0; VariableIndex < FromSize; VariableIndex++) {
        auto Constraint = isl_equality_alloc(isl_local_space_copy(ConstraintSpace));

        Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_in, VariableIndex, -1);
        Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_out, VariableIndex + Offset, 1);
        EmbedderMapping = isl_map_add_constraint(EmbedderMapping, Constraint);
    }

    return EmbedderMapping;
}

/**
 * Generate a set of constraints for the subscript parameters of LeftHand under which
 * the heap object matches a heap object in RightHand.
 */
isl_set *EWPTAliasAnalysis::generateAliasConstraints(EWPTEntry& LeftHand, EWPTEntry& RightHand) {
    if(LeftHand.HeapIdentifier != RightHand.HeapIdentifier) {
        auto IndexSpace = isl_space_alloc(IslContext, LeftHand.Rank, 0, 0);
        return isl_set_empty(IndexSpace);
    }

    if(LeftHand.HeapIdentifier.hasType != HeapNameId::MALLOC) {
        auto IndexSpace = isl_space_alloc(IslContext, LeftHand.Rank, 0, 0);
        return isl_set_universe(IndexSpace);
    }

    //llvm::outs() << "LEFTHAND: " << debugMappingToString(LeftHand.Mapping) << "\n"; llvm::outs().flush();
    //llvm::outs() << "RIGHTHAND: " << debugMappingToString(RightHand.Mapping) << "\n"; llvm::outs().flush();
    // Constrain the LeftHand mapping to those indices where it might map to a heap object in RightHand
    auto AliasMapping = isl_map_intersect_range(isl_map_copy(LeftHand.Mapping), isl_map_range(isl_map_copy(RightHand.Mapping)));
    //llvm::outs() << "TEST: " << debugMappingToString(isl_map_universe(isl_space_alloc(IslContext, 0, 1, 1))) << "\n"; llvm::outs().flush();

    //llvm::outs() << "INTERSECTED:" << debugMappingToString(AliasMapping) << "\n"; llvm::outs().flush();


    // Extract the indices in this new constrained mapping as a set.
    auto AliasSet = isl_map_domain(AliasMapping);
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
bool EWPTAliasAnalysis::generateEntryFromHeapAssignment(int EntranceDepth, isl_set *EntranceConstraints, EWPTEntry& AssigneeMapping, const llvm::SCEV *BridgeValue, EWPTEntry& RetVal) {
    //llvm::outs() << "Generate Heap Assignment:: EntranceDepth = " << EntranceDepth << ", EntranceConstraints = " << debugSetToString(EntranceConstraints) << ", AssigneeMapping = " << debugMappingToString(AssigneeMapping.Mapping) << ", BridgeValue = " << *BridgeValue << "\n";

    // The new mapping will have the following subscripts:
    // - The subscripts from the entrance mapping
    // - One subscript for the bridge
    // - The subscripts from the assignee mapping
    auto InputSize = EntranceDepth + 1 + AssigneeMapping.Rank;
    auto NewSpace = isl_space_alloc(IslContext, 0, InputSize, AssigneeMapping.AmountOfIterators);
    auto NewMapping = isl_map_universe(NewSpace);

    // Embed subscript parameters (x_1, ..., x_d) of our entrance mapping into the domain space.
    // For this we need to create a map (x_1, ..., x_d) -> (x_1, ..., x_d,  ...)

    // First we need to convert our set of constraints for the entrance mapping into a set of constraints
    // for the larger space of the new mapping. For this, we create an embedder mapping, which is just
    // an identity function from the smaller space into the larger space.
    auto AliasSetSize = isl_set_dim(EntranceConstraints, isl_dim_set);
    auto EmbedderMapping = constructEmbedderMapping(AliasSetSize, InputSize);

    mergeParams(EntranceConstraints, EmbedderMapping);
    auto FilterSpace = isl_set_apply(EntranceConstraints, EmbedderMapping);

    // Now we intersect our constraints for (x_1, ..., x_d) with the mapping, effectively adding these
    // constraints to the mapping we're generating.
    mergeParams(FilterSpace, NewMapping);
    NewMapping = isl_map_intersect_domain(NewMapping, FilterSpace);

    // Next we add a bridge constraint to our mapping. The bridge constraint is the constraint for
    // 'x' in the expression p[x] = q
    isl_pw_aff *SubscriptAff = SCEVAffinator::getPwAff(this, BridgeValue, IslContext);
    if(!SubscriptAff) {
        return false;
    }
    isl_set *SubscriptSet = isl_map_range(isl_map_from_pw_aff(SubscriptAff));

    // Currently we have a set of the form POINTER_SIZE * i, we need to convert this to just i
    // The division is possible because we ensured an alignment that is a multiple of the pointer size.
    std::string consString = "{ [i] -> [o] : i = " + std::to_string(DL->getPointerSize()) + "* o}";
    auto DivisionMapping = isl_map_read_from_str(IslContext, consString.c_str());
    SubscriptSet = isl_set_apply(SubscriptSet, DivisionMapping);

    // The SCEVAffinator gives us a mapping with a range of dimension 1.
    // We need to embed this dimension into the mapping we're generating, where this dimension
    // should align with the bridge dimension (at position InputSize).
    EmbedderMapping = constructEmbedderMapping(1, InputSize, EntranceDepth);
    SubscriptSet = isl_set_apply(SubscriptSet, EmbedderMapping);
    //llvm::outs() << "Subscript set: " << Analysis.debugSetToString(SubscriptSet) << "\n";
    mergeParams(SubscriptSet, NewMapping);
    NewMapping = isl_map_intersect_domain(NewMapping, SubscriptSet);

    // We need to embed the constraints of the asignee mapping into the mapping we're generating.
    // The assignee mapping has a range of (y_1, ..., y_k). We need the range to be our larger space,
    // so we simply prepend a projection to the assignee mapping, which projects
    // (x_1, ..., x_d, b, y_1, ..., y_k) to (y_1, ..., y_k). We can create this projection mapping
    // by inverting the equivalent embedder mapping that goes from
    // (y_1, ..., y_k) to (x_1, ..., x_d, b, y_1, ..., y_k)
    EmbedderMapping = constructEmbedderMapping(AssigneeMapping.Rank, InputSize, EntranceDepth + 1);
    EmbedderMapping = isl_map_reverse(EmbedderMapping);
    // concatenate the functions: apply_range(g, f) = f(g)
    auto AssigneeMappingCopy = isl_map_copy(AssigneeMapping.Mapping);
    mergeParams(EmbedderMapping, AssigneeMappingCopy);
    auto EmbeddedAssigneeMapping = isl_map_apply_range(EmbedderMapping, AssigneeMappingCopy);

    //llvm::outs() << "EmbeddedAssigneeMapping: " << debugMappingToString(EmbeddedAssigneeMapping) << "\n";
    //llvm::outs().flush();
    //llvm::outs() << "NewMapping: " << debugMappingToString(NewMapping) << "\n";
    //llvm::outs().flush();
    // Now intersect this tail part into our generated mapping, essentially adding the constraints for
    // (y_1, ..., y_k)
    mergeParams(NewMapping, EmbeddedAssigneeMapping);
    NewMapping = isl_map_intersect(NewMapping, EmbeddedAssigneeMapping);

    // Construct the EWPTEntry instance for the generated mapping.
    RetVal = EWPTEntry();
    RetVal.AmountOfIterators = AssigneeMapping.AmountOfIterators;
    RetVal.HeapIdentifier = AssigneeMapping.HeapIdentifier;
    RetVal.Rank = InputSize;
    RetVal.Mapping = NewMapping;

    //llvm::outs() << "Result: " << debugMappingToString(NewMapping) << "\n";

    return true;
}

bool EWPTAliasAnalysis::handleHeapAssignment(StoreInst *AssigningInstruction, EWPTAliasAnalysisState& State, EWPTAliasAnalysisFrame& Frame) {
    // Make sure we're storing to an aligned position and something of pointer size.
    if(AssigningInstruction->getAlignment() != DL->getPointerSize()) {
        llvm::errs() << "Storing to an address that isn't pointer aligned.\n";
        return false;
    }

    llvm::Value *AssignedValue = AssigningInstruction->getValueOperand();
    const SCEV *AccessFunction = SE->getSCEVAtScope(AssigningInstruction->getPointerOperand(), Frame.RestrictToLoop);
    auto BasePointer = dyn_cast<SCEVUnknown>(SE->getPointerBase(AccessFunction));

    if (!BasePointer) {
        llvm::errs() << "Can not handle base pointer for " << *AssigningInstruction << "\n";
        return false;
    }

    auto BasePointerValue = BasePointer->getValue();

    if (isa<UndefValue>(BasePointerValue)) {
        llvm::errs() << "Can not handle base value for " << *AssigningInstruction << "\n";
        return false;
    }

    auto Offset = SE->getMinusSCEV(AccessFunction, BasePointer);

    EWPTRoot AssignedMapping;
    // Get the appropriate EWPT mapping for the assigned value.
    // This could possibly be an ANY EWPT.
    getEWPTForValue(State, AssignedValue, AssignedMapping);

    // Get all EWPT entries of depth 0.
    std::vector<EWPTEntry> ModifiedHeapObjects;
    if(!State.trackedRoots.count(BasePointerValue)) {
        return false; // TODO: error handling
    }
    for(auto& EntryPair : State.trackedRoots[BasePointerValue].Entries) {
        auto& Entry = EntryPair.second;
        if(Entry.Rank == 0) {
            //llvm::outs() << "Found entry of depth 0 " << *(Entry.SourceLocation) << "\n";
            ModifiedHeapObjects.push_back(Entry);
        }
    }

    // Find all EWPT entries that might alias with p
    // Generate a set of constraints under which the alias happens
    // Concatenate the found mapping under this set of constraints
    // with the EWPT of q

    for(EWPTEntry& ModifiedHeapObject : ModifiedHeapObjects) {
        if(ModifiedHeapObject.HeapIdentifier.hasType == HeapNameId::ZERO) {
            // We're assigning to heap object zero. Assume that the programmer made sure
            // that this can not happen and ignore this entry.
            continue;
        }
        if(ModifiedHeapObject.HeapIdentifier.hasType == HeapNameId::ANY) {
            // We're assigning to ANY. Abort the analysis.
            llvm::errs() << "Aborting analysis because of potential write to ANY.\n";
            return false;
        }

        for(auto& RootPair : State.trackedRoots) {
            EWPTRoot& RootMapping = RootPair.second;

            // Make a copy of the entries, as we may modify them.
            auto Entries = RootMapping.Entries;
            for(auto& PossibleAliasPair : Entries) {
                auto& PossibleAlias = PossibleAliasPair.second;
                if(PossibleAlias.HeapIdentifier == ModifiedHeapObject.HeapIdentifier) {
                    auto EntranceConstraints = generateAliasConstraints(PossibleAlias, ModifiedHeapObject);
                    if(isl_set_is_empty(EntranceConstraints)) {
                        continue;
                    }

                    // Now build new mappings from our set for aliasing x_1, ..., x_d, the
                    // transition subscript x_{d+1} = x, and each EWPT in q

                    for(auto& TailMappingPair : AssignedMapping.Entries) {
                        auto& TailMapping = TailMappingPair.second;

                        // If we would build an EWPT entry for p that ends again in p, abort.
                        if(TailMapping.HeapIdentifier.hasType == HeapNameId::MALLOC &&
                           TailMapping.HeapIdentifier.SourceLocation == RootPair.first) {
                            llvm::errs() << "Cyclic heap memory graph detected, aborting.\n";
                            return false;
                        }

                        //llvm::outs() << "Found tail for " << *AssignedValue << ": "; TailMapping.debugPrint(*this); llvm::outs() << "\n"; llvm::outs().flush();
                        EWPTEntry NewEntry;
                        if(!generateEntryFromHeapAssignment(PossibleAlias.Rank, EntranceConstraints, TailMapping, Offset, NewEntry)) {
                            return false;
                        }
                        auto KeyForNewEntry = std::make_pair(NewEntry.Rank, NewEntry.HeapIdentifier);
                        RootMapping.Entries[KeyForNewEntry] = NewEntry; // TODO: merge it with existing entry
                    }
                }
            }
        }
    }

    return true;
}

bool EWPTAliasAnalysis::handleLoad(LoadInst *CurrentLoadInst, EWPTAliasAnalysisFrame &Frame, EWPTAliasAnalysisState& State) {
    //llvm::outs() << "Handling Load\n";

    // Make sure the alignment is a multiple of pointer size.
    if(CurrentLoadInst->getAlignment() % DL->getPointerSize() != 0) {
        llvm::errs() << "Load with alignment (" << CurrentLoadInst->getAlignment() <<
                        ") that's not a multiple of pointer size (" << DL->getPointerSize() << ")\n";
        return false;
    }

    const SCEV *AccessFunction = SE->getSCEVAtScope(CurrentLoadInst->getPointerOperand(), Frame.RestrictToLoop);
    auto BasePointer = dyn_cast<SCEVUnknown>(SE->getPointerBase(AccessFunction));

    if (!BasePointer) {
        llvm::errs() << "Can not handle base pointer for " << *CurrentLoadInst << "\n";
        return false;
    }

    auto BaseValue = BasePointer->getValue();

    if (isa<UndefValue>(BaseValue)) {
        llvm::errs() << "Can not handle base value for " << *CurrentLoadInst << "\n";
        return false;
    }

    auto Offset = SE->getMinusSCEV(AccessFunction, BasePointer);

    // Check if we have an EWPT entry for our base pointer
    if (State.trackedRoots.count(BaseValue)) {
        auto LoadedFrom = State.trackedRoots[BaseValue];

        // We're indexing into the loaded EWPT, so apply a subscript
        EWPTRoot NewRoot;
        if(!LoadedFrom.ApplySubscript(*this, Offset, Frame, State, NewRoot)) {
            return false;
        }
        State.trackedRoots[CurrentLoadInst] = NewRoot;
    }

    return true;
}

bool EWPTAliasAnalysis::getEWPTForValue(EWPTAliasAnalysisState& State, Value *PointerValBase, EWPTRoot& RetVal) {
    Value *PointerVal = PointerValBase->stripPointerCasts();
    if(State.trackedRoots.count(PointerVal)) {
        RetVal = State.trackedRoots[PointerVal];
        return true;
    }

    bool isNull = false;
    if(auto PointerConstInt = dyn_cast<ConstantInt>(PointerVal)) {
        if(PointerConstInt->isZero()) {
            isNull = true;
        }
    }
    else if(dyn_cast<ConstantPointerNull>(PointerVal)) {
        isNull = true;
    }
    if(isNull) {
        // Return an EWPT root representing the zero value.
        auto EmptySpace = isl_space_alloc(IslContext, 0, 0, 0);

        EWPTEntry Entry;
        Entry.HeapIdentifier = HeapNameId::getZero();
        Entry.AmountOfIterators = 0;
        Entry.Rank = 0;
        Entry.Mapping = isl_map_universe(EmptySpace);

        RetVal = EWPTRoot();
        auto Key = std::make_pair<unsigned, HeapNameId>(0, HeapNameId::getZero());
        RetVal.Entries[Key] = Entry;
        return true;
    }

    // No valid EWPT found, return an EWPT that can point to any value.
    auto EmptySpace = isl_space_alloc(IslContext, 0, 0, 0);

    EWPTEntry Entry;
    Entry.HeapIdentifier = HeapNameId::getAny();
    Entry.AmountOfIterators = 0;
    Entry.Rank = 0;
    Entry.Mapping = isl_map_universe(EmptySpace);

    RetVal = EWPTRoot();
    auto Key = std::make_pair<unsigned, HeapNameId>(0, HeapNameId::getAny());
    RetVal.Entries[Key] = Entry;

    return false;
}

bool EWPTAliasAnalysis::runOnBlock(BasicBlock &block, EWPTAliasAnalysisFrame& Frame, EWPTAliasAnalysisState& InState, EWPTAliasAnalysisState& RetValState)
{
    RetValState = InState;
    for(Instruction &CurrentInstruction : block.getInstList()) {
        //llvm::outs() << "Handling instruction " << CurrentInstruction << "\n";

        // Case: p = q[x]
        if (LoadInst *CurrentLoadInst = dyn_cast<LoadInst>(&CurrentInstruction)) {
            if(!handleLoad(CurrentLoadInst, Frame, RetValState)) {
                return false;
            }
        }
        // Case: p[x] = q
        else if (StoreInst *CurrentStoreInst = dyn_cast<StoreInst>(&CurrentInstruction)) {
            if(!handleHeapAssignment(CurrentStoreInst, RetValState, Frame)) {
                return false;
            }
        }

        // Case: p = phi x, y
        else if (PHINode *CurrentPhiNode = dyn_cast<PHINode>(&CurrentInstruction)) {
            // In the case of a phi node, we simply merge the EWPT tables of all
            // incoming nodes. Note that the associated blocks must already have been
            // processed by the iterative algorithm.

            std::vector<EWPTRoot> RootsToMerge;
            for(unsigned I = 0; I < CurrentPhiNode->getNumIncomingValues(); I++) {
                llvm::Value *IncomingValue = CurrentPhiNode->getIncomingValue(I);

                if(llvm::Instruction *IncomingInstruction = dyn_cast<llvm::Instruction>(IncomingValue)) {
                    // If we haven't processed the relevant block yet, skip it
                    // (If all works correctly, the reason we haven't processed it yet is
                    //  that we haven't iterated over a loop yet)
                    if(!Frame.BlockOutStates.count(IncomingInstruction->getParent())) {
                        continue;
                    }
                }
                EWPTRoot Root;
                bool Success = this->getEWPTForValue(RetValState, IncomingValue, Root);
                if(!Success) {
                    auto EmptySpace = isl_space_alloc(IslContext, 0, 0, 0);
                    EWPTEntry Entry;
                    Entry.HeapIdentifier = HeapNameId::getAny();
                    Entry.AmountOfIterators = 0;
                    Entry.Rank = 0;
                    Entry.Mapping = isl_map_universe(EmptySpace);

                    Root = EWPTRoot();
                    auto Key = std::make_pair<unsigned, HeapNameId>(0, HeapNameId::getAny());
                    Root.Entries[Key] = Entry;
                }
                RootsToMerge.push_back(Root);
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
            Entry.HeapIdentifier = HeapNameId::getMalloc(&CurrentInstruction);
            Entry.Rank = 0;

            auto Space = isl_space_alloc(IslContext, Entry.AmountOfIterators, 0, Entry.AmountOfIterators);

            for(unsigned I = 0; I < Iterators.size(); I++) {
                auto ValueName = Iterators[I]->getName();
                auto Identifier = isl_id_alloc(IslContext, ValueName.str().c_str(), Iterators[I]);
                Space = isl_space_set_dim_id(Space, isl_dim_param, I, Identifier);
            }

            Entry.Mapping = isl_map_universe(isl_space_copy(Space));

            for(unsigned I = 0; I < Iterators.size(); I++) {
                // For each iterator i we need a constraint that
                // a_i = i
                auto Constraint = isl_equality_alloc(isl_local_space_from_space(isl_space_copy(Space)));

                Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_param, I, -1);
                Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_out, I, 1);
                Entry.Mapping = isl_map_add_constraint(Entry.Mapping, Constraint);
            }

            isl_space_free(Space);

            auto KeyForNewEntry = std::make_pair(Entry.Rank, Entry.HeapIdentifier);
            Root.Entries[KeyForNewEntry] = Entry;
            RetValState.trackedRoots[&CurrentInstruction] = Root;

            printf("Root %x Entry %x\n", Root.Entries[KeyForNewEntry].Mapping, Entry.Mapping);

            //llvm::outs() << "Added new 0 depth entry for " << CurrentInstruction << "\n";
            //llvm::outs() << "New constraints: " << debugMappingToString(Entry.Mapping) << "\n";
        }

        llvm::outs() << "State after handling instruction " << CurrentInstruction << ":\n";
        debugPrintEWPTs(RetValState);
    }

    return true;
}

void EWPTAliasAnalysis::getAnalysisUsage(AnalysisUsage &AU) const
{
    AliasAnalysis::getAnalysisUsage(AU);
    AU.addRequired<AliasAnalysis>();
    AU.addRequired<DataLayoutPass>();
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequired<ScalarEvolution>();
    AU.setPreservesAll();
}

void *EWPTAliasAnalysis::getAdjustedAnalysisPointer(const void *ID)
{
    if (ID == &AliasAnalysis::ID) {
        return (AliasAnalysis *)this;
    }
    return this;
}

isl_ctx *EWPTAliasAnalysis::getIslContext() {
    return IslContext;
}

bool instructionIsHandled(Instruction *Instr) {
    return llvm::dyn_cast<llvm::LoadInst>(Instr) || llvm::dyn_cast<llvm::StoreInst>(Instr) || llvm::dyn_cast<llvm::PHINode>(Instr) || llvm::isNoAliasCall(Instr);
}

AliasAnalysis::AliasResult EWPTAliasAnalysis::alias(const Location& LocA, const Location& LocB) {
    auto PtrA = (Instruction*) llvm::dyn_cast<Instruction>(LocA.Ptr->stripPointerCasts());
    auto PtrB = (Instruction*) llvm::dyn_cast<Instruction>(LocB.Ptr->stripPointerCasts());

    if(!PtrA || !PtrB) {
#ifdef DEBUG_PRINT_ALIAS
        llvm::outs() << "Locations given aren't instructions, returning MayAlias\n";
#endif
        return AliasAnalysis::alias(LocA, LocB);
    }

    if(!instructionIsHandled(PtrA) || !instructionIsHandled(PtrB)) {
#ifdef DEBUG_PRINT_ALIAS
        llvm::outs() << "Instructions of unhandled type, returning MayAlias\n";
#endif
        return AliasAnalysis::alias(LocA, LocB);
    }

    BasicBlock* ContainerBlockA = (BasicBlock*) PtrA->getParent();
    BasicBlock* ContainerBlockB = (BasicBlock*) PtrB->getParent();

    if(!Frame.BlockOutStates.count(ContainerBlockA) ||
       !Frame.BlockOutStates.count(ContainerBlockB)) {
#ifdef DEBUG_PRINT_ALIAS
        llvm::outs() << "Incomplete analysis returning MayAlias\n";
#endif
        return AliasAnalysis::alias(LocA, LocB);
    }

    auto OutStateA = Frame.BlockOutStates[ContainerBlockA];
    auto OutStateB = Frame.BlockOutStates[ContainerBlockB];

    // Get EWPTs for A and B in that state.
    auto RootA = OutStateA.trackedRoots[PtrA];
    auto RootB = OutStateB.trackedRoots[PtrB];

#ifdef DEBUG_PRINT_ALIAS
    llvm::outs() << "Alias check for " << *PtrA << " and " << *PtrB << "(SV: " << RootA.isSingleValued() << " Match: " << RootA.equals(RootB) << ")\n";

    llvm::outs() << "Container block A: " << *ContainerBlockA << "\n";
    llvm::outs() << "Container block B: " << *ContainerBlockB << "\n";

    llvm::outs() << "EWPT A:";
    debugPrintEWPTs(OutStateA);
    llvm::outs() << "\n";
    llvm::outs() << "EWPT B:";
    debugPrintEWPTs(OutStateB);
    llvm::outs() << "\n";

    llvm::outs() << "RootA";
    RootA.debugPrint(*this);
    llvm::outs() << "RootB";
    RootB.debugPrint(*this);
#endif

    EWPTEntry *SingleValueA = RootA.isSingleValued();
    EWPTEntry *SingleValueB = RootB.isSingleValued();
    if(SingleValueA && SingleValueB) {
        if(SingleValueA->HeapIdentifier == SingleValueB->HeapIdentifier && isl_map_is_equal(SingleValueA->Mapping, SingleValueB->Mapping)) {
#ifdef DEBUG_PRINT_ALIAS
            llvm::outs() << "Returning MustAlias.\n";
#endif
            return AliasAnalysis::MustAlias;
        }
    }

    // Intersect EWPTs at rank 0.
    auto Intersection = RootA.intersect(RootB, 0);

    // Check how many elements there are in the intersection.
    // If there's none, NoAlias. Otherwise, mayalias.
    if(!Intersection.Entries.size()) {
#ifdef DEBUG_PRINT_ALIAS
        llvm::outs() << "Returning NoAlias.\n";
#endif
        return AliasAnalysis::NoAlias;
    } else {
#ifdef DEBUG_PRINT_ALIAS
        llvm::outs() << "Returning MayAlias.";
#endif
        return AliasAnalysis::alias(LocA, LocB);
    }
}

// SCEVAffinator
// ====================================

void SCEVAffinator::mergeParams(isl_pw_aff *&First, isl_pw_aff *&Second) {
    auto Space = isl_pw_aff_get_space(First);
    Second = isl_pw_aff_align_params(Second, Space);
    Space = isl_pw_aff_get_space(Second);
    First = isl_pw_aff_align_params(First, Space);
}

__isl_give isl_pw_aff *SCEVAffinator::getPwAff(EWPTAliasAnalysis *Analysis, const SCEV *Scev, isl_ctx *Ctx) {
  // TODO: initialize parameter dimension
  SCEVAffinator Affinator(Analysis);
  Affinator.Ctx = Ctx;
  auto RetVal = Affinator.visit(Scev);
  if(Affinator.Failed) {
      return nullptr;
  } else {
      return RetVal;
  }
}

__isl_give isl_val *isl_valFromAPInt(isl_ctx *Ctx, const APInt Int,
                                            bool IsSigned) {
  APInt Abs;
  isl_val *v;

  if (IsSigned)
    Abs = Int.abs();
  else
    Abs = Int;

  const uint64_t *Data = Abs.getRawData();
  unsigned Words = Abs.getNumWords();

  v = isl_val_int_from_chunks(Ctx, Words, sizeof(uint64_t), Data);

  if (IsSigned && Int.isNegative())
    v = isl_val_neg(v);

  return v;
}

__isl_give isl_pw_aff *SCEVAffinator::visit(const SCEV *Expr) {
  return SCEVVisitor<SCEVAffinator, isl_pw_aff *>::visit(Expr);
}

__isl_give isl_pw_aff *
SCEVAffinator::visitTruncateExpr(const SCEVTruncateExpr *Expr) {
    Failed = true;
    FailedReason = "SCEVAffinator: SCEVTruncateExpr not yet supported";
    return nullptr;
}

__isl_give isl_pw_aff *
SCEVAffinator::visitZeroExtendExpr(const SCEVZeroExtendExpr *Expr) {
    Failed = true;
    FailedReason = "SCEVAffinator: SCEVZeroExtendExpr not yet supported";
    return nullptr;
}

__isl_give isl_pw_aff *SCEVAffinator::visitUDivExpr(const SCEVUDivExpr *Expr) {
    Failed = true;
    FailedReason = "SCEVAffinator: SCEVUDivExpr not yet supported";
    return nullptr;
}

__isl_give isl_pw_aff *
SCEVAffinator::visitSignExtendExpr(const SCEVSignExtendExpr *Expr) {
  // Assuming the value is signed, a sign extension is basically a noop.
  // TODO: Reconsider this as soon as we support unsigned values.
  return visit(Expr->getOperand());
}

isl_pw_aff *SCEVAffinator::visitConstant(const SCEVConstant *Expr) {
    ConstantInt *Value = Expr->getValue();
    isl_val *v;
    // Assuming the value is signed should not lead to issues
    // for subscript expressions in any reasonable C programs.
    int MAX_SIGNED_INTEGER_32BIT = 1 << 30;
    assert(Value->getValue().getSExtValue() < MAX_SIGNED_INTEGER_32BIT);
    v = isl_valFromAPInt(Ctx, Value->getValue(), true);

    isl_space *Space = isl_space_set_alloc(Ctx, 0, 0);
    isl_local_space *ls = isl_local_space_from_space(Space);
    return isl_pw_aff_from_aff(isl_aff_val_on_domain(ls, v));
}

__isl_give isl_pw_aff *SCEVAffinator::visitAddExpr(const SCEVAddExpr *Expr) {
    isl_pw_aff *Sum = visit(Expr->getOperand(0));

    for (int i = 1, e = Expr->getNumOperands(); i < e; ++i) {
        isl_pw_aff *NextSummand = visit(Expr->getOperand(i));
        mergeParams(Sum, NextSummand);
        Sum = isl_pw_aff_add(Sum, NextSummand);
    }

    return Sum;
}

__isl_give isl_pw_aff *SCEVAffinator::visitMulExpr(const SCEVMulExpr *Expr) {
    isl_pw_aff *Product = visit(Expr->getOperand(0));

    for (int i = 1, e = Expr->getNumOperands(); i < e; ++i) {
        isl_pw_aff *NextOperand = visit(Expr->getOperand(i));

        if (!isl_pw_aff_is_cst(Product) && !isl_pw_aff_is_cst(NextOperand)) {
          isl_pw_aff_free(Product);
          isl_pw_aff_free(NextOperand);

          Failed = true;
          FailedReason = "SCEVAffinator: Expression isn't affine.";

          return nullptr;
        }

        mergeParams(Product, NextOperand);
        Product = isl_pw_aff_mul(Product, NextOperand);
    }

    return Product;
}

__isl_give isl_pw_aff *
SCEVAffinator::visitAddRecExpr(const SCEVAddRecExpr *Expr) {
  if(!Expr->isAffine()) {
      Failed = true;
      FailedReason = "SCEVAffinator: Only affine AddRecurrences allowed";
      return nullptr;
  }

  // Directly generate isl_pw_aff for Expr if 'start' is zero.
  if (Expr->getStart()->isZero()) {
    isl_pw_aff *Start = visit(Expr->getStart());
    isl_pw_aff *Step = visit(Expr->getOperand(1));

    if(!isl_pw_aff_is_cst(Step)) {
        Failed = true;
        FailedReason = "Stride isn't constant.";
        return nullptr;
    }

    isl_space *Space = isl_space_set_alloc(Ctx, 0, 0);

    auto LoopIndex = Expr->getLoop()->getCanonicalInductionVariable();
    auto LoopIndexId = Analysis->getIslIdForValue(LoopIndex);

    Space = isl_space_set_alloc(Ctx, 1, 0);
    isl_space_set_dim_id(Space, isl_dim_param, 0, LoopIndexId);
    isl_local_space *ls = isl_local_space_from_space(Space);
    isl_pw_aff *LPwAff = isl_pw_aff_var_on_domain(ls, isl_dim_param, 0);
    mergeParams(Start, Step);
    mergeParams(Start, LPwAff);

    // TODO: Do we need to check for NSW and NUW?
    return isl_pw_aff_add(Start, isl_pw_aff_mul(Step, LPwAff));
  }

  // Translate AddRecExpr from '{start, +, inc}' into 'start + {0, +, inc}'
  // if 'start' is not zero.
  ScalarEvolution *SE = Analysis->SE;
  const SCEV *ZeroStartExpr = SE->getAddRecExpr(
      SE->getConstant(Expr->getStart()->getType(), 0),
      Expr->getStepRecurrence(*SE), Expr->getLoop(), SCEV::FlagAnyWrap);

  isl_pw_aff *ZeroStartResult = visit(ZeroStartExpr);
  isl_pw_aff *Start = visit(Expr->getStart());

  mergeParams(ZeroStartResult, Start);
  return isl_pw_aff_add(ZeroStartResult, Start);
}

__isl_give isl_pw_aff *SCEVAffinator::visitSMaxExpr(const SCEVSMaxExpr *Expr) {
  isl_pw_aff *Max = visit(Expr->getOperand(0));

  for (int i = 1, e = Expr->getNumOperands(); i < e; ++i) {
    isl_pw_aff *NextOperand = visit(Expr->getOperand(i));
    mergeParams(Max, NextOperand);
    Max = isl_pw_aff_max(Max, NextOperand);
  }

  return Max;
}

__isl_give isl_pw_aff *SCEVAffinator::visitUMaxExpr(const SCEVUMaxExpr *Expr) {
    Failed = true;
    FailedReason = "SCEVAffinator: SCEVUMaxExpr not yet supported";
    return nullptr;
}

__isl_give isl_pw_aff *SCEVAffinator::visitSDivInstruction(Instruction *SDiv) {
  assert(SDiv->getOpcode() == Instruction::SDiv && "Assumed SDiv instruction!");
  auto *SE = Analysis->SE;

  auto *Divisor = SDiv->getOperand(1);
  auto *DivisorSCEV = SE->getSCEV(Divisor);
  auto *DivisorPWA = visit(DivisorSCEV);

  if(!isa<ConstantInt>(Divisor)) {
      Failed = true;
      FailedReason = "SCEVAffinator: RHS of division is non-constant.";
      return nullptr;
  }

  auto *Dividend = SDiv->getOperand(0);
  auto *DividendSCEV = SE->getSCEV(Dividend);
  auto *DividendPWA = visit(DividendSCEV);
  mergeParams(DividendPWA, DivisorPWA);
  return isl_pw_aff_tdiv_q(DividendPWA, DivisorPWA);
}

__isl_give isl_pw_aff *SCEVAffinator::visitUnknown(const SCEVUnknown *Expr) {
    auto UnknownValue = Expr->getValue();
    auto UnknownId = Analysis->getIslIdForValue(UnknownValue);
    isl_space *Space = isl_space_set_alloc(Ctx, 1, 0);
    isl_space_set_dim_id(Space, isl_dim_param, 0, UnknownId);

    isl_local_space *ls = isl_local_space_from_space(Space);
    return isl_pw_aff_var_on_domain(ls, isl_dim_param, 0);
}



} // namespace ewpt

using namespace ewpt;

char EWPTAliasAnalysis::ID = 0;

INITIALIZE_AG_PASS_BEGIN(EWPTAliasAnalysis, AliasAnalysis, "ewpt-aa",
                                   "Element-Wise-Points-To-Mapping based Alias Analysis",
                                                      false, true, false)
INITIALIZE_AG_PASS_END(EWPTAliasAnalysis, AliasAnalysis, "ewpt-aa",
                                           "Element-Wise-Points-To-Mapping based Alias Analysis",
                                                              false, true, false)
