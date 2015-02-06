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

using namespace llvm;

class IslTransformMapping {
    std::vector<int> dim_in_replacements;
    std::vector<int> dim_out_replacements;
    std::vector<int> dim_set_replacements;
};

class EWPTAliasAnalysis;

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
    EWPTEntry ApplySubscript(EWPTAliasAnalysis& Analysis, llvm::Value *Subscript) const;

    void debugPrint(EWPTAliasAnalysis& Analysis);

private:
    void InternalApplySubscript(EWPTAliasAnalysis& Analysis, llvm::Value *Subscript);
};

EWPTEntry EWPTEntry::ApplySubscript(EWPTAliasAnalysis& Analysis, llvm::Value *Subscript) const {
    EWPTEntry Copy = *this;
    Copy.Mapping = isl_basic_map_copy(Mapping);
    Copy.InternalApplySubscript(Analysis, Subscript);
    return Copy;
}

class EWPTRoot {
public:
    std::vector<EWPTEntry> Entries;

    EWPTRoot ApplySubscript(EWPTAliasAnalysis& Analysis, llvm::Value *Subscript) {
        EWPTRoot RetVal;
        for(auto& Entry : Entries) {
            if(Entry.Depth > 0) {
                RetVal.Entries.push_back(Entry.ApplySubscript(Analysis, Subscript));
            }
        }
        return RetVal;
    }
};

class EWPTAliasAnalysisState {
public:
    std::map<llvm::Value *, EWPTRoot> trackedRoots;
};

class EWPTAliasAnalysisFrame {
    llvm::BasicBlock *Entry;
    llvm::BasicBlock *Exit;
    std::map<llvm::BasicBlock*, EWPTAliasAnalysisState> BlockOutStates;
    std::vector<llvm::BasicBlock*> BlocksToProcess;
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
            LI = &getAnalysis<LoopInfo>();

            InitializeAliasAnalysis(this);

            EWPTAliasAnalysisState BeginState;
            EWPTAliasAnalysisState EndState;

            // The actual analysis.
            for(BasicBlock &Block : F) {
                EndState = runOnBlock(Block, BeginState);
            }

            debugPrintEWPTs(EndState);

            return false;
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
            // Constrain the LeftHand mapping to those indices where it might map to a heap object in RightHand
            auto AliasMapping = isl_basic_map_intersect_range(isl_basic_map_copy(LeftHand.Mapping), isl_basic_map_range(isl_basic_map_copy(RightHand.Mapping)));
            llvm::outs() << "TEST: " << debugMappingToString(isl_basic_map_universe(isl_space_alloc(IslContext, 0, 1, 1))) << "\n"; llvm::outs().flush();

            llvm::outs() << debugMappingToString(AliasMapping) << "\n"; llvm::outs().flush();


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
        EWPTEntry generateEntryFromHeapAssignment(int EntranceDepth, isl_basic_set *EntranceConstraints, EWPTEntry& AssigneeMapping, llvm::ConstantInt *BridgeValue) {
            llvm::outs() << "Generate Heap Assignment:: EntranceDepth = " << EntranceDepth << ", EntranceConstraints = " << debugSetToString(EntranceConstraints) << ", AssigneeMapping = " << debugMappingToString(AssigneeMapping.Mapping) << ", BridgeValue = " << BridgeValue->getSExtValue() << "\n";

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
            auto FilterSpace = isl_basic_set_apply(isl_basic_set_copy(EntranceConstraints), EmbedderMapping);

            // Now we intersect our constraints for (x_1, ..., x_d) with the mapping, effectively adding these
            // constraints to the mapping we're generating.
            NewMapping = isl_basic_map_intersect_domain(NewMapping, FilterSpace);

            // Next we add a bridge constraint to our mapping. The bridge constraint is the constraint for
            // 'x' in the expression p[x] = q
            auto BridgeConstraint = isl_equality_alloc(isl_local_space_copy(isl_local_space_from_space(NewSpace)));
            BridgeConstraint = isl_constraint_set_coefficient_si(BridgeConstraint, isl_dim_in, EntranceDepth, -1);
            BridgeConstraint = isl_constraint_set_constant_si(BridgeConstraint, BridgeValue->getSExtValue());
            NewMapping = isl_basic_map_add_constraint(NewMapping, BridgeConstraint);

            // We need to embed the constraints of the asignee mapping into the mapping we're generating.
            // The assignee mapping has a range of (y_1, ..., y_k). We need the range to be our larger space,
            // so we simply prepend a projection to the assignee mapping, which projects
            // (x_1, ..., x_d, b, y_1, ..., y_k) to (y_1, ..., y_k). We can create this projection mapping
            // by inverting the equivalent embedder mapping that goes from
            // (y_1, ..., y_k) to (x_1, ..., x_d, b, y_1, ..., y_k)
            EmbedderMapping = constructEmbedderMapping(AssigneeMapping.Depth, InputSize, EntranceDepth + 1);
            EmbedderMapping = isl_basic_map_reverse(EmbedderMapping);
            // concatenate the functions: apply_range(g, f) = f(g)
            auto EmbeddedAssigneeMapping = isl_basic_map_apply_range(EmbedderMapping, isl_basic_map_copy(AssigneeMapping.Mapping));

            llvm::outs() << "EmbeddedAssigneeMapping: " << debugMappingToString(EmbeddedAssigneeMapping) << "\n";
            llvm::outs().flush();
            llvm::outs() << "NewMapping: " << debugMappingToString(NewMapping) << "\n";
            llvm::outs().flush();
            // Now intersect this tail part into our generated mapping, essentially adding the constraints for
            // (y_1, ..., y_k)
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
            auto ConstantIndex = dyn_cast<llvm::ConstantInt>(Index);
            if(!ConstantIndex) {
                return; // TODO Error Handling
            }
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
                    for(EWPTEntry& PossibleAlias : Entries) {
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
                        llvm::outs() << "Starting to look for tails: " << &PossibleAlias << "\n";
                        for(EWPTEntry& TailMapping : Entries) {
                            llvm::outs() << "Found tail: " << debugMappingToString(PossibleAlias.Mapping) << "\n"; llvm::outs().flush();
                            PossibleAlias.debugPrint(*this); llvm::outs().flush();
                            auto NewEntry = generateEntryFromHeapAssignment(PossibleAlias.Depth, EntranceConstraints, TailMapping, ConstantIndex);
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

        EWPTAliasAnalysisState runOnBlock(BasicBlock &block, EWPTAliasAnalysisState& InState)
        {
            EWPTAliasAnalysisState RetValState = InState;
            for(Instruction &CurrentInstruction : block.getInstList()) {
                if (LoadInst *CurrentLoadInst = dyn_cast<LoadInst>(&CurrentInstruction)) {
                    llvm::outs() << "Handling Load\n";
                    if(auto CurrentGEPInst = dyn_cast<GetElementPtrInst>(CurrentLoadInst->getPointerOperand())) {
                        if(CurrentGEPInst->getNumIndices() != 1) {
                            // We can't deal with any number of indices but one.
                            llvm::errs() << "Too many indices in GEP\n"; // TODO Error Handling
                            exit(1);
                        }
                        // Look for the base-pointer we're loading from
                        auto BasePointer = CurrentGEPInst->getPointerOperand()->stripPointerCasts();
                        auto Index = CurrentGEPInst->idx_begin()->get();
                        llvm::outs() << "Handling load " << *BasePointer << "[" << *Index << "]\n";

                        // Check if we have an EWPT entry for our base pointer
                        if (RetValState.trackedRoots.count(BasePointer)) {
                            auto LoadedFrom = RetValState.trackedRoots[BasePointer];

                            // We're indexing into the loaded EWPT, so apply a subscript
                            EWPTRoot NewRoot = LoadedFrom.ApplySubscript(*this, Index);
                            RetValState.trackedRoots[&CurrentInstruction] = NewRoot;
                        }
                    }
                }
                // Case: p[x] = q
                else if (StoreInst *CurrentStoreInst = dyn_cast<StoreInst>(&CurrentInstruction)) {
                    handleHeapAssignment(CurrentStoreInst, RetValState);
                }

                // Case: p = malloc();
                else if (llvm::isNoAliasCall(&CurrentInstruction)) {
                    // Create a new EWPT with just the one entry.
                    EWPTRoot Root;
                    EWPTEntry Entry;

                    // TODO: deal with iterators
                    Entry.AmountOfIterators = 0;
                    Entry.SourceLocation = &CurrentInstruction;
                    Entry.Depth = 0;
                    auto space = isl_space_alloc(IslContext, 0, 0, 0);
                    Entry.Mapping = isl_basic_map_universe(space);
                    Root.Entries.push_back(Entry);
                    RetValState.trackedRoots[&CurrentInstruction] = Root;

                    llvm::outs() << "Added new 0 depth entry for " << &CurrentInstruction << "\n";
                }
            }

            return RetValState;
        }

        void getAnalysisUsage(AnalysisUsage &AU) const
        {
            AliasAnalysis::getAnalysisUsage(AU);
            AU.addRequired<AliasAnalysis>();
            AU.addRequired<LoopInfo>();
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

void EWPTEntry::InternalApplySubscript(EWPTAliasAnalysis& Analysis, llvm::Value *Subscript) {
    // We need to substitute and project out the first parameter in the input dimension.
    if(auto ConstSubscript = dyn_cast<llvm::ConstantInt>(Subscript)) {
        // Generate a constraint of the form x_1 = c, where c is a constant and x_1
        // is the first mapping parameter that we're projecting out.
        int64_t ConstValue = ConstSubscript->getSExtValue();
        llvm::outs() << "Adding constraint x_1=" << ConstValue << " to " << Analysis.debugMappingToString(Mapping) << "\n";
        isl_local_space *LocalSpace = isl_local_space_from_space(isl_basic_map_get_space(Mapping));
        isl_constraint *NewConstraint = isl_equality_alloc(LocalSpace);
        NewConstraint = isl_constraint_set_coefficient_si(NewConstraint, isl_dim_in, 0, -1);
        NewConstraint = isl_constraint_set_constant_val(NewConstraint, isl_val_int_from_si(Analysis.getIslContext(), ConstValue));
        Mapping = isl_basic_map_add_constraint(Mapping, NewConstraint);
    }

    // Project out the first parameter
    Mapping = isl_basic_map_project_out(Mapping, isl_dim_in, 0, 1);
    Depth = Depth - 1;
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
