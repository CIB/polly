#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"

using namespace llvm;

namespace llvm {
    void initializeEWPTAliasAnalysisPass(PassRegistry& registry);
}

/**
 * References an induction variable.
 */
class EWPTInductionVariable
{
    public:
        /** Whether the constraint is of the form b = i or b < i */
        const bool isPreviousIndex;

        /** The induction variable we're referring to, 0 is the outermost loop. */
        const unsigned inductionVariable;

        EWPTInductionVariable() : isPreviousIndex(false), inductionVariable(0) { };

        EWPTInductionVariable(unsigned inductionVariable, bool isPreviousIndex) 
                : isPreviousIndex(isPreviousIndex), inductionVariable(inductionVariable)
        {

        }
};

class EWPTConstraint
{
    public:

        enum ConstraintType {
            EQUALS_CONSTANT,
            EQUALS_INDUCTION_VARIABLE
        };
        
        ConstraintType TypeOfConstraint;

        /** The index of the variable this constraint applies to. */
        const int appliedVariable;
        
        /** The constant integer we constrain this variable to. */
        const APInt Constant;

        /** The bound variable we constrain this variable to. */
        const EWPTInductionVariable InductionVariable;

        EWPTConstraint(unsigned appliedVariable, APInt constant) :
            TypeOfConstraint(EQUALS_CONSTANT),
            appliedVariable(appliedVariable),
            Constant(constant) { }

        EWPTConstraint(unsigned appliedVariable, EWPTInductionVariable InductionVariable) :
            TypeOfConstraint(EQUALS_INDUCTION_VARIABLE),
            appliedVariable(appliedVariable),
            InductionVariable(InductionVariable) { }
        
        friend raw_ostream& operator<<(raw_ostream& os, const EWPTConstraint& Constraint);
};

raw_ostream& operator<<(raw_ostream& os, const EWPTConstraint& Constraint) {
    os << Constraint.appliedVariable << " = ";
    if(Constraint.TypeOfConstraint == EWPTConstraint::EQUALS_CONSTANT) {
        os << Constraint.Constant;
    } else if(Constraint.TypeOfConstraint == EWPTConstraint::EQUALS_INDUCTION_VARIABLE) {
        os << "i" << Constraint.InductionVariable.inductionVariable;
        if(Constraint.InductionVariable.isPreviousIndex) {
            os << "-";
        }
    }
    return os;
}

class EWPTTableEntry
{
    public:
        /**
         * The statement describing the memory object we're
         * referencing in this mapping, for instance this could
         * be a `malloc()` call.
         */
        const llvm::Value *Statement;

        /**
         * The basic block in which @Statement was found.
         */
        const BasicBlock *ContainingBlock;

        /**
         * The nesting level of the loops containing @Statement
         */
        const unsigned nestingLevel;

        /**
         * The rank of the ewpt mapping, that is, the amount of its
         * parameters. For instance, in p(x1, x2), the rank would be
         * 2.
         */
        const unsigned rank;

        /**
         * Number of bound variables currently present in this table entry.
         */
        unsigned countBoundVariables;

        std::vector<EWPTConstraint> constraints;

        int getSubscriptVariable(int index) const
        {
            return index;
        }

        int getParameterVariable(int index) const
        {
            return nestingLevel + index;
        }

        EWPTTableEntry(const llvm::Value *Statement, const BasicBlock* ContainingBlock, int nestingLevel, int rank)
            : Statement(Statement), ContainingBlock(ContainingBlock), nestingLevel(nestingLevel), rank(rank)
        {

            assert(llvm::isNoAliasCall(Statement) &&
                   "Trying to create EWPT table entry with a value that is not an alias call!");
        }

        void addConstraint(int variableIndex, APInt constantValue)
        {
            constraints.push_back(EWPTConstraint(variableIndex, constantValue));
        }

        friend raw_ostream& operator<<(raw_ostream& os, const EWPTTableEntry& Entry);
};

raw_ostream& operator<<(raw_ostream& os, const EWPTTableEntry& Entry) {
            os << "[";
            for(auto iter = Entry.constraints.begin(); iter != Entry.constraints.end(); iter++) {
                os << *iter;
                if(iter + 1 != Entry.constraints.end()) {
                    os << ", ";
                }
            }
            os << " = " << *Entry.Statement << "]";
            return os;
}

class ElementWisePointsToMapping
{
    public:
        std::vector<EWPTTableEntry> tableEntries;

        ElementWisePointsToMapping()
        {
        }

        void intersect(const ElementWisePointsToMapping& Other, 
                        std::vector<EWPTTableEntry&>& LeftIntersection, 
                        std::vector<EWPTTableEntry&>& RightIntersection,
                        std::vector<Value&>& LeftIndices,
                        std::vector<Value&>& RightIndices);
};

void ElementWisePointsToMapping::intersect(const ElementWisePointsToMapping& Other,
                std::vector<EWPTTableEntry&>& LeftIntersection,
                std::vector<EWPTTableEntry&>& RightIntersection,
                std::vector<Value&>& LeftIndices,
                std::vector<Value&>& RightIndices) {
     
}

Value *getPointerOperand(Instruction &Inst)
{
    if (LoadInst *load = dyn_cast<LoadInst>(&Inst)) {
        return load->getPointerOperand();
    } else if (StoreInst *store = dyn_cast<StoreInst>(&Inst)) {
        return store->getPointerOperand();
    } else if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(&Inst)) {
        return gep->getPointerOperand();
    }

    return 0;
}


class EWPTAliasAnalysis: public FunctionPass, public AliasAnalysis
{
    public:
        static char ID;

        std::map<const llvm::Value *, ElementWisePointsToMapping *> ewpts;

        ~EWPTAliasAnalysis()
        {
            for(auto KeyValuePair : ewpts) {
                delete KeyValuePair.second;
            }
        }

        /// @brief Analysis passes used.
        //@{
        ScalarEvolution *SE;
        LoopInfo *LI;
        //@}

        EWPTAliasAnalysis() : FunctionPass(ID)
        {
            initializeEWPTAliasAnalysisPass(*PassRegistry::getPassRegistry());
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

        Value *getBasePointer(Instruction *MemoryAccess)
        {
            Value *Ptr = getPointerOperand(*MemoryAccess);
            Loop *L = LI->getLoopFor(MemoryAccess->getParent());
            const SCEV *AccessFunction = SE->getSCEVAtScope(Ptr, L);
            const SCEVUnknown *BasePointer;
            Value *BaseValue;

            BasePointer = dyn_cast<SCEVUnknown>(SE->getPointerBase(AccessFunction));

            if (!BasePointer) {
                return NULL;
            }

            BaseValue = BasePointer->getValue();
            return BaseValue;
        }

        /**
         * Check for loops surrounding this block and build an iteration vector containing
         * Value's representing the induction variables.
         */
        std::vector<llvm::Value*> getIterationVector(const BasicBlock& block) const {
            // Try to find surrounding loops.
            std::vector<llvm::Value*> IterationVector;
            auto Loop = LI->getLoopFor(&block);
            while(Loop) {
                llvm::Value* Iterator = Loop->getCanonicalInductionVariable();
                if(!Iterator) {
                    llvm::outs() << "Can't handle loop without canonical induction variable.\n";
                    return IterationVector;
                }
                llvm::outs() << "Found canonical induction variable: " << *Iterator << "(" << Iterator << ")\n";
                IterationVector.push_back(Iterator);
                Loop = Loop->getParentLoop();
            }
            
            // We want them sorted from outer to inner, but it was sorted from inner to outer. Reverse.
            std::reverse(IterationVector.begin(), IterationVector.end());

            return IterationVector;
        }

        void runOnBlock(BasicBlock &block)
        {
            for(Instruction &CurrentInstruction : block.getInstList()) {
                if (StoreInst *CurrentStoreInst = dyn_cast<StoreInst>(&CurrentInstruction)) {
                    // Recursively via GEPs find out what we're storing to,
                    // e.g. in foo[x][y] = z we want foo, not &foo[x][y]
                    //
                    // Once we found the Base, check if it's an EWPT.
                    // If it's not, create a new EWPT associated with the base.
                    //
                    // "depth" is the number of GEPs/loads we had to go through to find the base.
                    // Also figure out the indices of the GEPs/loads used.
                    //
                    // Check if the value of the store is a malloc or a different value.
                    // If it's a different value, but the number of GEPs/loads does not match
                    // the depth of the EWPT, error.
                    //
                    // Create a new EWPT table entry, at the found depth, with constraints for
                    // the found indices.

                    llvm::Value *ValueOperand = CurrentStoreInst->getValueOperand()->stripPointerCasts();

                    // First check what we're storing. If it's not a no-alias call, such as malloc,
                    // or "0", representing the NULL-pointer, we're not really interested.
                    if(!llvm::isNoAliasCall(ValueOperand)) {
                        continue;
                    }

                    std::vector<Value *> Indices;
                    const Value *Base = findBaseEWPT(*CurrentStoreInst->getPointerOperand(), Indices);

                    std::vector<Value*> IterationVector = getIterationVector(block);

                    if(Base) {
                        // Debug: print the indices.
                        llvm::outs() << "Finding EWPT for store " << *CurrentStoreInst << " [";
                        for(Value *value : Indices) {
                            llvm::outs() << *value << ", ";
                        }
                        llvm::outs() << "] " << *Base << " \n";

                        if(!ewpts.count(Base)) {
                            ewpts[Base] = new ElementWisePointsToMapping();
                        }

                        EWPTTableEntry entry(ValueOperand, &block, 0, Indices.size());
                        // Generate constraints for each index.
                        for(unsigned IndexPosition = 0; IndexPosition < Indices.size(); IndexPosition++) {
                            int constraintVariable = entry.getSubscriptVariable(IndexPosition);

                            Value *IndexValue = Indices[IndexPosition];
                            if(llvm::ConstantInt *ConstIntIndex = dyn_cast<ConstantInt>(IndexValue)) {
                                entry.addConstraint(constraintVariable, ConstIntIndex->getValue());
                            } else if(std::find(IterationVector.begin(), IterationVector.end(), IndexValue) != IterationVector.end()) {
                                llvm::outs() << "Yay, found iteration vector!\n";
                                int IteratorIndex = std::find(IterationVector.begin(), IterationVector.end(), IndexValue) - IterationVector.begin();
                                
                                // Build constraint
                                entry.constraints.push_back(EWPTConstraint(constraintVariable, EWPTInductionVariable(IteratorIndex, false)));
                            } else {
                                llvm::outs() << "Can't handle index " << *IndexValue << "(" << IndexValue << ")\n";
                            }
                        }

                        llvm::outs() << "Constraints: ";
                        for(EWPTConstraint &constraint : entry.constraints) {
                            llvm::outs() << constraint.appliedVariable << " = " << constraint.Constant << " ";
                        }
                        llvm::outs() << "\n";

                        ewpts[Base]->tableEntries.push_back(entry);
                    }
                }
            }
        }

        /**
         * Try to follow a GEP/load chain to find the base EWPT.
         *
         * Anything that isn't itself retrieved from a load can be
         * considered an EWPT.
         *
         * TODO: Instead of collecting indices, this function should probably collect *constraints* for indices.
         *
         * @param myPointer The pointer for which to get the base EWPT.
         * @param indices A reference to a vector in which we'll store the indices used.
         */
        const Value *findBaseEWPT(const Value &myPointer, std::vector<Value *> &Indices)
        {
            if (const GetElementPtrInst *CurrentGEPInst = dyn_cast<GetElementPtrInst>(&myPointer)) {
                // Remember the index of the GEP
                for(User::const_op_iterator IndexIterator = CurrentGEPInst->idx_begin();
                    IndexIterator != CurrentGEPInst->idx_end(); IndexIterator++) {
                    Value *Index = IndexIterator->get();
                    Indices.push_back(Index);
                }

                // Check what we're GEP'ing into
                if(const LoadInst *CurrentLoadInst = dyn_cast<LoadInst>
                                                     (CurrentGEPInst->getPointerOperand()->stripPointerCasts())) {
                    // Okay, it's a load, recursively try to find the root EWPT.
                    return findBaseEWPT(*CurrentLoadInst->getPointerOperand()->stripPointerCasts(), Indices);
                } else {
                    // Nope, not a load, treat this as root EWPT.
                    return CurrentGEPInst->getPointerOperand()->stripPointerCasts();
                }
            }

            // Not a GEP, we can't follow this pointer!
            return NULL;
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

        /**
         * To check whether two pointers alias:
         * - Attempt to convert the pointers to EWPTs+indices into these EWPTs
         * - For each combination of table entries of the EWPTs:
         *      - If they don't refer to the same statement, they can't alias.
         *      - If they refer to the same statement, apply the index constraints to each,
         *        see if they intersect.
         *      - If there are no constraints on the indices for intersection, they MustAlias.
         *        If there are constraints on the indices for intersection, they MayAlias.
         *        If the constraints on indices for intersection are not satisfiable, NoAlias.
         * - If all table entries MustAlias all table entries, MustAlias. If all table entries
         *   NoAlias all table entries, NoAlias. Otherwise, MayAlias.
         */
        AliasAnalysis::AliasResult alias(const Location &LocA, const Location &LocB) override
        {
            // When all you have is a hammer, everything starts looking like a nail.
            // Let's see if we can't make an EWPT out of LocA or LocB.

            llvm::outs() << "Calling our alias analysis!\n";

            AliasAnalysis::AliasResult LocAResult = ewptCheck(*LocA.Ptr, *LocB.Ptr);
            AliasResult rval;
            if(LocAResult != MayAlias) {
                rval = LocAResult;
            } else {
                rval = ewptCheck(*LocB.Ptr, *LocA.Ptr);
            }

            llvm::outs() << "Result for " << *LocA.Ptr << " / " << *LocB.Ptr << " : " << rval << "\n";

            return rval;
        }

        AliasResult ewptCheck(const Value &ewptValue, const Value &containedValue)
        {
            std::vector<Value *> LocAIndices;
            const Value *LocABase = findBaseEWPT(ewptValue, LocAIndices);

            llvm::outs() << "Trying to find base EWPT for " << ewptValue << "\n";

            if(LocABase) {
                llvm::outs() << "Found base value :" << *LocABase << "\n";
                if(ewpts.count(LocABase)) {
                    llvm::outs() << "Found EWPT\n";
                    ElementWisePointsToMapping *container = ewpts[LocABase];
                    return contains(*container, LocAIndices, containedValue);
                }
            }

            llvm::outs() << "No EWPT found.\n";

            return AliasResult::MayAlias;
        }

        /**
         * Check whether the given EWPT may contain the given pointer.
         */
        AliasResult contains(const ElementWisePointsToMapping &ewpt, const std::vector<Value *> &Indices,
                             const Value &Ptr) const
        {
            // Keep track of whether we get MustAlias for *all* the table entries.
            bool ContainedInAll = true;
            // Keep track of whether we get NoAlias for *all* the table entries.
            bool ContainedInNone = true;

            for(EWPTTableEntry Entry : ewpt.tableEntries) {
                AliasResult IsContained = contains(Entry, Indices, Ptr);
                llvm::outs() << "Checking whether " << Ptr << " is contained in " << Entry << " Result: " << (unsigned) IsContained << "\n";
                if(IsContained != AliasResult::MustAlias) {
                    // We now have at least one entry which might not contain our Ptr.
                    ContainedInAll = false;
                }
                if(IsContained != AliasResult::NoAlias) {
                    ContainedInNone = false;
                }
            }

            if(ContainedInNone) {
                return AliasResult::NoAlias;
            } else if(ContainedInAll) {
                return AliasResult::MustAlias;
            } else {
                return AliasResult::MayAlias;
            }
        }

        AliasResult contains(const EWPTTableEntry Entry, const std::vector<Value *> &Indices,
                             const Value &Ptr) const
        {
            // See if the entry contains our llvm Value
            // Note that llvm values are just instructions, independent of e.g.
            // loop iteration, so they actually represent *multiple possible values*,
            // depending on program state. Checking that the values are equal is just
            // a preliminary check.

            if(&Ptr == Entry.Statement) {
                llvm::outs() << "Found matching entry for value " << Ptr << "[";
                for(const Value* index : Indices) {
                    if(const ConstantInt *ConstantIndex = dyn_cast<ConstantInt>(index)) {
                        llvm::outs() << *ConstantIndex << ", ";
                    }
                }
                llvm::outs() << "]: " << Entry << "\n";
                // Now that we know that the values are equivalent, we need to check whether the
                // given indices can match our constraints.

                if(Entry.rank != Indices.size()) {
                    // Number of indices doesn't match rank of entry, next!
                    return AliasResult::NoAlias;
                }

                // Get surrounding loop iteration vector.
                std::vector<Value*> IterationVector = getIterationVector(*Entry.ContainingBlock);

                // Track whether all indices are guaranteed to be correct.
                bool AllIndicesMatch = true;
                for(unsigned IndexPosition = 0; IndexPosition < Indices.size(); IndexPosition++) {
                    // Check whether our value at that index matches the constraint.
                    Value *AssociatedIndex = Indices[IndexPosition];
                    const EWPTConstraint &Constraint = Entry.constraints[IndexPosition];

                    // TODO: this will have to become a lot more complex once more than constant constraints
                    //       are allowed
                    if(Constraint.TypeOfConstraint == Constraint.EQUALS_CONSTANT) {
                        if(ConstantInt *ConstantIndex = dyn_cast<ConstantInt>(AssociatedIndex)) {
                            if(ConstantIndex->getValue() != Constraint.Constant) {
                                // We have an explicit value for our index, and an explicit value for our constraint, and
                                // they don't match -> Thus there's no intersection.
                                llvm::outs() << "One index doesn't match, NoAlias.\n";
                                return AliasResult::NoAlias;
                            }
                        } else {
                            // It's not a constant, so it may or may not match.
                            AllIndicesMatch = false;
                        }
                    } else if(Constraint.TypeOfConstraint == Constraint.EQUALS_INDUCTION_VARIABLE) {
                        /**
                        if(AssociatedIndex != IterationVector[Constraint.InductionVariable.inductionVariable]) {
                            llvm::outs() << "Index " << *AssociatedIndex << " doesn't match constraint " << Constraint << "(" << *IterationVector[Constraint.InductionVariable.inductionVariable] << ")" << "\n";
                            AllIndicesMatch = false;
                        } else {
                            llvm::outs() << "Index " << *AssociatedIndex << " matches constraint " << Constraint << "(" << *IterationVector[Constraint.InductionVariable.inductionVariable] << ")\n";
                        }*/
                        // Just assume we assigned it for *all* indices for now.
                    }
                }
                if(AllIndicesMatch) {
                    llvm::outs() << "All indices match, must alias.\n";
                    return AliasResult::MustAlias;
                } else {
                    llvm::outs() << "Indices might match, may alias.\n";
                    return AliasResult::MayAlias;
                }
            } else {
                return AliasResult::NoAlias;
            }
        }
};

char EWPTAliasAnalysis::ID = 0;

INITIALIZE_AG_PASS_BEGIN(EWPTAliasAnalysis, AliasAnalysis, "ewpt-aa",
                                   "Element-Wise-Points-To-Mapping based Alias Analysis",
                                                      false, true, false)
INITIALIZE_AG_PASS_END(EWPTAliasAnalysis, AliasAnalysis, "ewpt-aa",
                                           "Element-Wise-Points-To-Mapping based Alias Analysis",
                                                              false, true, false)
