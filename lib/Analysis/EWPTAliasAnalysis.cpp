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

using namespace llvm;

/**
 * An EWPT mapping entry of the form 
 * <N_s[a_1, ..., a_k], c>(x_1, ..., x_d), where s is the source
 * location of a heap object, a_i represent the iteration vector of
 * the heap object, x_i represent variables of subscript expressions,
 * and c is a system of linear constraints over a_i and x_i.
 */
class EWPTEntry {
public:
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
    EWPTEntry ApplySubscript(llvm::Value *Subscript);
};

EWPTEntry EWPTEntry::ApplySubscript(llvm::Value *Subscript) {
    // We need to substitute and project out the first parameter in the input dimension. 
    if(auto ConstSubscript = dyn_cast<llvm::ConstantInt>(Subscript)) {
        uint64_t ConstValue = ConstSubscript->getSExtValue();
        isl_local_space *LocalSpace = isl_local_space_from_space(isl_
    } 
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

        void runOnBlock(BasicBlock &block)
        {
            for(Instruction &CurrentInstruction : block.getInstList()) {                
                if (LoadInst *CurrentLoadInst = dyn_cast<LoadInst>(&CurrentInstruction)) {
                }
                // Case: p[x] = q
                else if (StoreInst *CurrentStoreInst = dyn_cast<StoreInst>(&CurrentInstruction)) {
                    if(auto CurrentGEPInst = dyn_cast<GetElementPtrInst>(CurrentStoreInst->getPointerOperand())) {
                        if(CurrentGEPInst->getNumIndices() != 1) {
                            // We can't deal with any number of indices but one.
                            return; // TODO Error Handling
                        }

                        llvm::Value *Index = CurrentGEPInst->idx_begin()->get();
                        llvm::Value *BasePointer = CurrentGEPInst->getPointerOperand()->stripPointerCasts();

                        // Check that we have an EWPT root associated with our base pointer.
                        if(!trackedRoots.count(BasePointer)) {
                            return; // TODO Error Handling
                        }

                        // Apply Index as subscript to the EWPT we found.
                        // Store the new EWPT into our map of EWPTs.
                        // TODO
                    }
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
                    isl_space *EmptySpace = isl_space_alloc(IslContext, 0, 0, 0);
                    Entry.Mapping = isl_basic_map_universe(EmptySpace);
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
};

char EWPTAliasAnalysis::ID = 0;

INITIALIZE_AG_PASS_BEGIN(EWPTAliasAnalysis, AliasAnalysis, "ewpt-aa",
                                   "Element-Wise-Points-To-Mapping based Alias Analysis",
                                                      false, true, false)
INITIALIZE_AG_PASS_END(EWPTAliasAnalysis, AliasAnalysis, "ewpt-aa",
                                           "Element-Wise-Points-To-Mapping based Alias Analysis",
                                                              false, true, false)
