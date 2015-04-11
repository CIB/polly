#ifndef EWPT_ALIAS_ANALYSIS_H
#define EWPT_ALIAS_ANALYSIS_H

#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "isl/options.h"
#include <queue>

namespace llvm {
    class PassRegistry;
    void initializeEWPTAliasAnalysisPass(llvm::PassRegistry &);
}

using namespace llvm;

// Forward declarations.
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
     * The amount of subscript parameters x_1, x_2, ..., x_d,
     * where d is the rank of this entry.
     */
    unsigned Rank;

    /**
     * The amount of iteration indices a_1, ..., a_k by which the heap
     * object is identified, k being this value.
     */
    unsigned AmountOfIterators;

    /**
     * The source location of the heap object mapped by this entry.
     */
    llvm::Value *SourceLocation;

    /**
     * Set of constraints over x_i, a_i and our free variables,
     * mapping x_i to a_i with additional requirements to free variables.
     */
    isl_map *Mapping;

    /**
     * Apply the given llvm::Value as subscript expression to the first
     * parameter x_1
     */
    EWPTEntry ApplySubscript(EWPTAliasAnalysis& Analysis, const llvm::SCEV *Subscript, EWPTAliasAnalysisFrame& Frame, EWPTAliasAnalysisState& State) const;

    void debugPrint(EWPTAliasAnalysis& Analysis);

    EWPTEntry clone();

    EWPTEntry merge(EWPTEntry& Other);

    EWPTEntry intersect(EWPTEntry& Other);

    bool isSingleValued();

private:
    void InternalApplySubscript(EWPTAliasAnalysis& Analysis, const llvm::SCEV *Subscript, EWPTAliasAnalysisFrame &Frame, EWPTAliasAnalysisState& State);
};


class EWPTRoot {
public:
    std::map< std::pair<unsigned, llvm::Value*>, EWPTEntry> Entries;

    EWPTRoot ApplySubscript(EWPTAliasAnalysis& Analysis, const llvm::SCEV *Subscript,
                            EWPTAliasAnalysisFrame &Frame, EWPTAliasAnalysisState& State);

    std::vector< std::pair<unsigned, llvm::Value*> > getCombinedKeys(EWPTRoot& Other);

    EWPTRoot merge(EWPTRoot& Other);

    EWPTRoot intersect(EWPTRoot& Other, unsigned Rank);

    EWPTRoot clone();

    bool equals(EWPTRoot& Other);

    bool isSingleValued();

    std::vector<EWPTEntry*> getEntriesAtRank(unsigned Rank);
};


class EWPTAliasAnalysisState {
public:
    std::map<llvm::Value *, EWPTRoot> trackedRoots;

    EWPTAliasAnalysisState merge(EWPTAliasAnalysisState& Other);

    EWPTAliasAnalysisState clone();

    bool equals(EWPTAliasAnalysisState& Other);
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

    std::vector<llvm::Value*> GetCurrentLoopIterators();

    unsigned GetDepth() {
        return GetCurrentLoopIterators().size();
    }
};


class EWPTAliasAnalysis: public FunctionPass, public AliasAnalysis
{
    public:
        static char ID;

        /// @brief Analysis passes used.
        //@{
        llvm::ScalarEvolution *SE;
        llvm::LoopInfo *LI;
        //@}

        isl_ctx *IslContext;

        EWPTAliasAnalysisFrame Frame;

        EWPTAliasAnalysis() : FunctionPass(ID)
        {
            initializeEWPTAliasAnalysisPass(*PassRegistry::getPassRegistry());
            IslContext = isl_ctx_alloc();
        }

        ~EWPTAliasAnalysis()
        {
            isl_ctx_free(IslContext);
        }

        virtual bool runOnFunction(Function &F);

        bool arePredecessorsProcessed(EWPTAliasAnalysisFrame& Frame, BasicBlock* ToCheck);

        std::vector<EWPTAliasAnalysisState*> getPredecessorStates(EWPTAliasAnalysisFrame& Frame, BasicBlock *Current);

        bool iterativeControlFlowAnalysis(EWPTAliasAnalysisFrame& Frame);

        llvm::Value *getUpperBoundForLoop(Loop& LoopToAnalyze);

        bool handleLoop(EWPTAliasAnalysisFrame& SuperFrame, BasicBlock& LoopHeader, Loop& LoopToAnalyze, EWPTAliasAnalysisState& RetVal);

        EWPTAliasAnalysisState MergeStates(std::vector<EWPTAliasAnalysisState*> StatesToMerge);

        EWPTRoot MergeRoots(std::vector<EWPTRoot*> RootsToMerge);

        void debugPrintEWPTs(EWPTAliasAnalysisState& State);

        std::string debugSetToString(isl_set *Set);

        std::string debugMappingToString(isl_map *Map);

        void mergeParams(isl_map*& First, isl_map*& Second);

        void mergeParams(isl_set*& First, isl_map*& Second);

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
        isl_map *constructEmbedderMapping(unsigned FromSize, unsigned ToSize, unsigned Offset = 0);

        /**
         * Generate a set of constraints for the subscript parameters of LeftHand under which
         * the heap object matches a heap object in RightHand.
         */
        isl_set *generateAliasConstraints(EWPTEntry& LeftHand, EWPTEntry& RightHand);

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
        EWPTEntry generateEntryFromHeapAssignment(int EntranceDepth, isl_set *EntranceConstraints, EWPTEntry& AssigneeMapping, llvm::Value *BridgeValue);

        /**
         * Handle a heap assignment that involves a GEP, so something of the form
         * p[x] = q, where the address p[x] is calculated through a GEP instruction.
         */
        bool handleGEPHeapAssignment(GetElementPtrInst *TargetGEP, llvm::Value *AssignedValue, EWPTAliasAnalysisState& State);

        bool handleHeapAssignment(StoreInst *AssigningInstruction, EWPTAliasAnalysisState& State);

        bool handleLoad(LoadInst *CurrentLoadInst, EWPTAliasAnalysisFrame &Frame, EWPTAliasAnalysisState& State);

        bool runOnBlock(BasicBlock &block, EWPTAliasAnalysisFrame& Frame, EWPTAliasAnalysisState& InState, EWPTAliasAnalysisState& RetValState);

        void getAnalysisUsage(AnalysisUsage &AU) const;

        void *getAdjustedAnalysisPointer(const void *ID) override;

        isl_ctx *getIslContext();

        AliasAnalysis::AliasResult alias(const Location& LocA, const Location& LocB);
};


#endif // EWPT_ALIAS_ANALYSIS_H