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
    EWPTEntry ApplySubscript(llvm::Value *Subscript) const;

private: 
    void ApplySubscript(EWPTAliasAnalysis& Analysis, llvm::Value *Subscript);
};

EWPTEntry EWPTEntry::ApplySubscript(llvm::Value *Subscript) const {
    EWPTEntry Copy = *this;
    Copy.ApplySubscript(Subscript);
    return Copy;
}

class EWPTRoot {
public:
    std::vector<EWPTEntry> Entries;
};


class EWPTAliasAnalysis: public FunctionPass, public AliasAnalysis
{
    public:
        static char ID;

        /**
         * The llvm::Value's for which we are tracking EWPT roots.
         */
        std::map<llvm::Value *, EWPTRoot> trackedRoots;

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
        }

        virtual bool runOnFunction(Function &F)
        {
            // Initialization.
            SE = &getAnalysis<ScalarEvolution>();
            LI = &getAnalysis<LoopInfo>();

            InitializeAliasAnalysis(this);

            // The actual analysis.
            for(BasicBlock &Block : F) {
                runOnBlock(Block);
            }

            return false;
        }

        /**
         * Create a mapping that embeds a smaller space into a larger space.
         *
         * For instance, we could embed the space (x_1, x_2) into the space (y_1, y_2, y_3)
         * with a mapping { (x_1, x_2) -> (x_1, x_2, _)
         */
        isl_basic_map *constructEmbedderMapping(unsigned FromSize, unsigned ToSize, unsigned Offset) {
            auto EmbedderSpace = isl_space_alloc(IslContext, 0, FromSize, ToSize);
            auto EmbedderMapping = isl_basic_map_universe(EmbedderSpace);

            auto ConstraintSpace = isl_local_space_from_space(EmbedderSpace);
            for(unsigned VariableIndex = 0; VariableIndex < FromSize; VariableIndex++) {
                auto Constraint = isl_equality_alloc(isl_local_space_copy(ConstraintSpace));

                isl_constraint_set_coefficient_si(Constraint, isl_dim_in, VariableIndex, -1);
                isl_constraint_set_coefficient_si(Constraint, isl_dim_out, VariableIndex + Offset, 1);
                isl_basic_map_add_constraint(EmbedderMapping, Constraint);
            }

            return EmbedderMapping;
        }

        isl_basic_map *generateAliasConstraints(EWPTEntry& LeftHand, EWPTEntry& RightHand) {
            if(PossibleAlias.SourceLocation != LeftHandEntry->SourceLocation) {
                continue;
            }

            // We have a_1, ..., a_k representing our p. Intersect our possible alias with this p.
            auto AliasMapping = isl_basic_map_intersect_range(PossibleAlias.Mapping, isl_basic_map_range(LeftHandEntry->Mapping));

            // We now have constrained our possible mapping to indices that alias our p.
            // Get a set representing the vectors x_1, ..., x_d that we need to apply as subscripts
            // to our possible mapping to get to q.

            auto AliasSet = isl_basic_map_domain(AliasMapping);
        }

        void handleGEPHeapAssignment(GetElementPtrInst *TargetGEP, llvm::Value *AssignedValue) {
            if(TargetGEP->getNumIndices() != 1) {
                // We can't deal with any number of indices but one.
                return; // TODO Error Handling
            }

            llvm::Value *Index = TargetGEP->idx_begin()->get();
            llvm::Value *BasePointer = TargetGEP->getPointerOperand()->stripPointerCasts();

            // Check that we have an EWPT root associated with our base pointer.
            if(!trackedRoots.count(BasePointer)) {
                return; // TODO Error Handling
            }

            // Get all EWPT entries of depth 0.
            std::vector<EWPTEntry*> LeftHandEntries;
            for(EWPTEntry& Entry : trackedRoots[BasePointer].Entries) {
                if(Entry.Depth == 0) {
                    LeftHandEntries.push_back(&Entry);
                }
            }

            // Find all EWPT entries that might alias with p
            // Generate a set of constraints under which the alias happens
            // Concatenate the found mapping under this set of constraints
            // with the EWPT of q

            for(EWPTEntry* LeftHandEntry : LeftHandEntries) {
                for(auto& RootPair : trackedRoots) {
                    EWPTRoot& RootMapping = RootPair.second;
                    for(EWPTEntry& PossibleAlias : RootMapping.Entries) {
                        if(PossibleAlias.SourceLocation != LeftHandEntry->SourceLocation) {
                            continue;
                        }

                        // We have a_1, ..., a_k representing our p. Intersect our possible alias with this p.
                        auto AliasMapping = isl_basic_map_intersect_range(PossibleAlias.Mapping, isl_basic_map_range(LeftHandEntry->Mapping));

                        // We now have constrained our possible mapping to indices that alias our p.
                        // Get a set representing the vectors x_1, ..., x_d that we need to apply as subscripts
                        // to our possible mapping to get to q.

                        auto AliasSet = isl_basic_map_domain(AliasMapping);

                        // Now build new mappings from our set for aliasing x_1, ..., x_d, the
                        // transition subscript x_{d+1} = x, and each EWPT in q

                        for(EWPTEntry& RightHandEntry : trackedRoots[AssignedValue].Entries) {
                            auto InputSize = PossibleAlias.Depth + 1 + RightHandEntry.Depth;
                            auto NewSpace = isl_space_alloc(IslContext, 0, InputSize, RightHandEntry.AmountOfIterators);
                            // (x_1, ..., x_d, x_t, y_1, ..., y_n) -> (a_1, ..., a_k)
                            // x_1, ..., x_d in AliasSet (INTERSECT DOMAIN)
                            // x_t = e
                            // (y_1, ..., y_n) -> (a_1, ..., a_k) in RightHandEntry (INTERSECT WITH MAP)
                            auto NewMapping = isl_basic_map_universe(NewSpace);

                            // Embed Alias Set of parameters x_1, ... x_d into our domain space, that is, x_1, ..., x_d, x_t, y_1, ..., y_n
                            // For this we need to create a map (x_1, ..., x_d) -> (x_1, ..., y_n)
                            auto AliasSetSize = isl_space_dim(isl_basic_set_get_space(AliasSet), isl_dim_set);

                            auto EmbedderMapping = constructEmbedderMapping(AliasSetSize, InputSize, 0);
                            auto FilterSpace = isl_basic_set_apply(AliasSet, EmbedderMapping);
                            NewMapping = isl_basic_map_intersect_domain(NewMapping, FilterSpace);

                            auto BridgeConstraint = isl_equality_alloc(isl_local_space_from_space(NewSpace));
                            BridgeConstraint = isl_constraint_set_coefficient_si(BridgeConstraint, isl_dim_in, PossibleAlias.Depth, 1);
                            BridgeConstraint = isl_constraint_set_constant_si(BridgeConstraint, 0xBEEF);
                            NewMapping = isl_basic_map_add_constraint(NewMapping, BridgeConstraint);

                            isl_basic_map_free(EmbedderMapping);
                            EmbedderMapping = constructEmbedderMapping(RightHandEntry.Depth, InputSize, PossibleAlias.Depth + 1);
                            EmbedderMapping = isl_basic_map_reverse(EmbedderMapping);
                            auto EmbeddedMapping = isl_basic_map_apply_domain(RightHandEntry.Mapping, EmbedderMapping);

                            NewMapping = isl_basic_map_intersect(NewMapping, EmbeddedMapping);
                            EWPTEntry NewEntry;
                            NewEntry.AmountOfIterators = RightHandEntry.AmountOfIterators;
                            NewEntry.SourceLocation = RightHandEntry.SourceLocation;
                            NewEntry.Depth = InputSize;
                            NewEntry.Mapping = NewMapping;
                            RootMapping.Entries.push_back(NewEntry);
                        }
                    }
                }
            }
        }

        void handleHeapAssignment(StoreInst *AssigningInstruction) {
            if(auto CurrentGEPInst = dyn_cast<GetElementPtrInst>(AssigningInstruction->getPointerOperand())) {
                handleGEPHeapAssignment(CurrentGEPInst, AssigningInstruction->getValueOperand());
            }
        }

        void runOnBlock(BasicBlock &block)
        {
            for(Instruction &CurrentInstruction : block.getInstList()) {                
                if (LoadInst *CurrentLoadInst = dyn_cast<LoadInst>(&CurrentInstruction)) {
                }
                // Case: p[x] = q
                else if (StoreInst *CurrentStoreInst = dyn_cast<StoreInst>(&CurrentInstruction)) {
                    handleHeapAssignment(CurrentStoreInst);
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
                    trackedRoots[&CurrentInstruction] = Root;
                }
            }
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

void EWPTEntry::ApplySubscript(EWPTAliasAnalysis& Analysis, llvm::Value *Subscript) {
    // We need to substitute and project out the first parameter in the input dimension. 
    if(auto ConstSubscript = dyn_cast<llvm::ConstantInt>(Subscript)) {
        // Generate a constraint of the form x_1 = c, where c is a constant and x_1
        // is the first mapping parameter that we're projecting out.
        int64_t ConstValue = ConstSubscript->getSExtValue();
        isl_local_space *LocalSpace = isl_local_space_from_space(isl_basic_map_get_space(Mapping));
        isl_constraint *NewConstraint = isl_equality_alloc(LocalSpace);
        isl_constraint_set_coefficient_val(NewConstraint, isl_dim_in, 0, isl_val_one(Analysis.getIslContext()));
        isl_constraint_set_constant_val(NewConstraint, isl_val_int_from_si(Analysis.getIslContext(), ConstValue));
        isl_basic_map_add_constraint(Mapping, NewConstraint);
    }
    
    // Project out the first parameter
    isl_basic_map_project_out(Mapping, isl_dim_in, 0, 1);
}

char EWPTAliasAnalysis::ID = 0;

INITIALIZE_AG_PASS_BEGIN(EWPTAliasAnalysis, AliasAnalysis, "ewpt-aa",
                                   "Element-Wise-Points-To-Mapping based Alias Analysis",
                                                      false, true, false)
INITIALIZE_AG_PASS_END(EWPTAliasAnalysis, AliasAnalysis, "ewpt-aa",
                                           "Element-Wise-Points-To-Mapping based Alias Analysis",
                                                              false, true, false)
