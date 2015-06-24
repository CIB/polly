#ifndef EWPT_ALIAS_ANALYSIS_H
#define EWPT_ALIAS_ANALYSIS_H

#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "isl/options.h"
#include "isl/aff.h"
#include <queue>

namespace llvm {
    class PassRegistry;
    void initializeEWPTAliasAnalysisPass(llvm::PassRegistry &);
}

using namespace llvm;


namespace ewpt {

// Forward declarations.
class EWPTAliasAnalysis;
class EWPTAliasAnalysisState;
class EWPTAliasAnalysisFrame;

/// Translate a 'const SCEV *' expression in an isl_pw_aff.
struct SCEVAffinator : public SCEVVisitor<SCEVAffinator, isl_pw_aff *> {
public:
  /// @brief Translate a 'const SCEV *' to an isl_pw_aff.
  ///
  /// @param Stmt The location at which the scalar evolution expression
  ///             is evaluated.
  /// @param Expr The expression that is translated.
  static __isl_give isl_pw_aff *getPwAff(EWPTAliasAnalysis* Analysis, const SCEV *Expr, isl_ctx *Ctx);

  SCEVAffinator(EWPTAliasAnalysis *Analysis)
    : Analysis(Analysis), Failed(false) { }

private:
  isl_ctx *Ctx;
  int getLoopDepth(const Loop *L);
  EWPTAliasAnalysis *Analysis;
  bool Failed;
  std::string FailedReason;
  void mergeParams(isl_pw_aff*& First, isl_pw_aff*& Second);

  __isl_give isl_pw_aff *visit(const SCEV *Expr);
  __isl_give isl_pw_aff *visitConstant(const SCEVConstant *Expr);
  __isl_give isl_pw_aff *visitTruncateExpr(const SCEVTruncateExpr *Expr);
  __isl_give isl_pw_aff *visitZeroExtendExpr(const SCEVZeroExtendExpr *Expr);
  __isl_give isl_pw_aff *visitSignExtendExpr(const SCEVSignExtendExpr *Expr);
  __isl_give isl_pw_aff *visitAddExpr(const SCEVAddExpr *Expr);
  __isl_give isl_pw_aff *visitMulExpr(const SCEVMulExpr *Expr);
  __isl_give isl_pw_aff *visitUDivExpr(const SCEVUDivExpr *Expr);
  __isl_give isl_pw_aff *visitAddRecExpr(const SCEVAddRecExpr *Expr);
  __isl_give isl_pw_aff *visitSMaxExpr(const SCEVSMaxExpr *Expr);
  __isl_give isl_pw_aff *visitUMaxExpr(const SCEVUMaxExpr *Expr);
  __isl_give isl_pw_aff *visitUnknown(const SCEVUnknown *Expr);
  __isl_give isl_pw_aff *visitSDivInstruction(Instruction *SDiv);

  friend struct SCEVVisitor<SCEVAffinator, isl_pw_aff *>;
};

/**
 * The first (non-integer) part of a heap name.
 */
struct HeapNameId {
    enum Type {
        ZERO,
        ANY,
        MALLOC
    };

    Type hasType;
    llvm::Value *SourceLocation;

    static HeapNameId getMalloc(llvm::Value *SourceLocation) {
        HeapNameId RetVal;
        RetVal.hasType = MALLOC;
        RetVal.SourceLocation = SourceLocation;
        return RetVal;
    }

    static HeapNameId getAny() {
        HeapNameId RetVal;
        RetVal.hasType = ANY;
        RetVal.SourceLocation = nullptr;
        return RetVal;
    }

    static HeapNameId getZero() {
        HeapNameId RetVal;
        RetVal.hasType = ZERO;
        RetVal.SourceLocation = nullptr;
        return RetVal;
    }

    std::string toString() {
        if(hasType == ZERO) {
            return "NULL";
        } else if(hasType == ANY) {
            return "ANY";
        } else {
            std::string RetVal;
            raw_string_ostream Stream(RetVal);
            Stream << *SourceLocation;
            RetVal = Stream.str();
            return RetVal;
        }
    }
};

bool operator<(const HeapNameId& l, const HeapNameId& r );

bool operator==(const HeapNameId& l, const HeapNameId& r );

bool operator!=(const HeapNameId& l, const HeapNameId& r );

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
        : Mapping(nullptr)
    { }

    EWPTEntry(const EWPTEntry& Other);

    ~EWPTEntry();

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

    HeapNameId HeapIdentifier;

    /**
     * Set of constraints over x_i, a_i and our free variables,
     * mapping x_i to a_i with additional requirements to free variables.
     */
    isl_map *Mapping;

    /**
     * Apply the given llvm::Value as subscript expression to the first
     * parameter x_1
     */
    bool ApplySubscript(EWPTAliasAnalysis& Analysis, const llvm::SCEV *Subscript, EWPTAliasAnalysisFrame& Frame, EWPTAliasAnalysisState& State, EWPTEntry& OutEntry) const;

    void debugPrint(EWPTAliasAnalysis& Analysis);

    EWPTEntry& operator=(const EWPTEntry& Other);

    EWPTEntry merge(EWPTEntry& Other);

    EWPTEntry intersect(EWPTEntry& Other);

    bool isSingleValued();

private:
    bool InternalApplySubscript(EWPTAliasAnalysis& Analysis, const llvm::SCEV *Subscript, EWPTAliasAnalysisFrame &Frame, EWPTAliasAnalysisState& State);
};


class EWPTRoot {
public:
    std::map< std::pair<unsigned, HeapNameId>, EWPTEntry> Entries;

    bool ApplySubscript(EWPTAliasAnalysis& Analysis, const llvm::SCEV *Subscript,
                            EWPTAliasAnalysisFrame &Frame, EWPTAliasAnalysisState& State, EWPTRoot& OutRoot);

    std::vector< std::pair<unsigned, HeapNameId> > getCombinedKeys(EWPTRoot& Other);

    EWPTRoot merge(EWPTRoot& Other);

    EWPTRoot intersect(EWPTRoot& Other, unsigned Rank);

    bool equals(EWPTRoot& Other);

    EWPTEntry *isSingleValued();

    std::vector<EWPTEntry*> getEntriesAtRank(unsigned Rank);

    void debugPrint(EWPTAliasAnalysis& Analysis);
};


class EWPTAliasAnalysisState {
public:
    std::map<llvm::Value *, EWPTRoot> trackedRoots;

    EWPTAliasAnalysisState merge(EWPTAliasAnalysisState& Other);

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
        const llvm::DataLayout *DL;
        //@}

        isl_ctx *IslContext;

        EWPTAliasAnalysisFrame Frame;

        EWPTAliasAnalysis() : FunctionPass(ID)
        {
            initializeEWPTAliasAnalysisPass(*PassRegistry::getPassRegistry());
            IslContext = isl_ctx_alloc();
            isl_options_set_on_error(IslContext, ISL_ON_ERROR_WARN);
        }

        ~EWPTAliasAnalysis()
        {
            Frame.BlockOutStates.clear();
            Frame.EntryState.trackedRoots.clear();
            isl_ctx_free(IslContext);
        }

        virtual bool runOnFunction(Function &F);

        bool arePredecessorsProcessed(EWPTAliasAnalysisFrame& Frame, BasicBlock* ToCheck);

        std::vector<EWPTAliasAnalysisState*> getPredecessorStates(EWPTAliasAnalysisFrame& Frame, BasicBlock *Current);

        bool iterativeControlFlowAnalysis(EWPTAliasAnalysisFrame& Frame);

        llvm::Value *getUpperBoundForLoop(Loop& LoopToAnalyze);

        bool handleLoop(EWPTAliasAnalysisFrame& SuperFrame, BasicBlock& LoopHeader, Loop& LoopToAnalyze, EWPTAliasAnalysisState& RetVal);

        EWPTAliasAnalysisState MergeStates(std::vector<EWPTAliasAnalysisState*> StatesToMerge);

        EWPTRoot MergeRoots(std::vector<EWPTRoot> RootsToMerge);

        void debugPrintEWPTs(EWPTAliasAnalysisState& State);

        std::string debugSetToString(isl_set *Set);

        std::string debugMappingToString(isl_map *Map);

        __isl_give isl_id *getIslIdForValue(Value *val);

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
        bool generateEntryFromHeapAssignment(int EntranceDepth, isl_set *EntranceConstraints, EWPTEntry& AssigneeMapping, const llvm::SCEV *BridgeValue, EWPTEntry &RetVal);

        bool handleHeapAssignment(StoreInst *AssigningInstruction, EWPTAliasAnalysisState& State, EWPTAliasAnalysisFrame& Frame);

        bool handleLoad(LoadInst *CurrentLoadInst, EWPTAliasAnalysisFrame &Frame, EWPTAliasAnalysisState& State);

        bool getEWPTForValue(EWPTAliasAnalysisState& State, llvm::Value *Key, EWPTRoot& RetVal);

        bool runOnBlock(BasicBlock &block, EWPTAliasAnalysisFrame& Frame, EWPTAliasAnalysisState& InState, EWPTAliasAnalysisState& RetValState);

        void getAnalysisUsage(AnalysisUsage &AU) const;

        void *getAdjustedAnalysisPointer(const void *ID) override;

        isl_ctx *getIslContext();

        AliasResult alias(const MemoryLocation& LocA, const MemoryLocation& LocB);
};

} // namespace ewpt

#endif // EWPT_ALIAS_ANALYSIS_H