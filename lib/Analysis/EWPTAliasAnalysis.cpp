#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Pass.h"

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

#define DEBUG_TYPE "ewpt"
STATISTIC(TooManyLoopBackEdges, "EWPT Analysis: Too many loop back edges");
STATISTIC(LoopDidNotConverge, "EWPT Analysis: Loop did not converge");
STATISTIC(NoScevForBasePointer, "EWPT Analysis: Could not convert base pointer for store to known SCEV");
STATISTIC(WriteToAny, "EWPT Analysis: Potential write to ANY heap object");
STATISTIC(CyclicHeapMemoryGraph, "EWPT Analysis: Heap memory graph has potential cycles");
STATISTIC(CouldNotAffinateSCEV, "EWPT Analysis: SCEVAffinator failed on SCEV");
STATISTIC(SuccessfulFunctionAnalysis, "EWPT Analysis: Function successfully analyzed");
STATISTIC(FailedFunctionAnalysis, "EWPT Analysis: Function analysis failed");
STATISTIC(SuccessfulRankOneEWPT, "EWPT Analysis: Depth two EWPT found");
STATISTIC(LoopExitOutsideLoopHeader, "EWPT Analysis: Loop exit outside of loop header");
STATISTIC(NonLoopCycle, "EWPT Analysis: Cycle that is not a loop as detected by LoopInfo");

STATISTIC(AnySource_NON_ZERO_CONSTANT, "EWPT Analysis: Source of Any - NON_ZERO_CONSTANT");
STATISTIC(AnySource_UNALIGNED_STORE, "EWPT Analysis: Source of Any - UNALIGNED_STORE");
STATISTIC(AnySource_NON_LINEAR_LOAD, "EWPT Analysis: Source of Any - NON_LINEAR_LOAD");
STATISTIC(AnySource_NON_POINTER_LOAD, "EWPT Analysis: Source of Any - NON_POINTER_LOAD");
STATISTIC(AnySource_PARAMETER, "EWPT Analysis: Source of Any - PARAMETER");
STATISTIC(AnySource_VALUE_NOT_ANALYZED, "EWPT Analysis: Source of Any - VALUE_NOT_ANALYZED");
STATISTIC(AnySource_UNKNOWN_OPERATION, "EWPT Analysis: Source of Any - UNKNOWN_OPERATION");

namespace ewpt {

void IncrementStatisticForAnySource(HeapNameId::AnyReason Source) {
    switch(Source) {
    case HeapNameId::NON_ZERO_CONSTANT:
        AnySource_NON_ZERO_CONSTANT++;
        break;
    case HeapNameId::UNALIGNED_STORE:
        AnySource_UNALIGNED_STORE++;
        break;
    case HeapNameId::NON_LINEAR_LOAD:
        AnySource_NON_LINEAR_LOAD++;
        break;
    case HeapNameId::NON_POINTER_LOAD:
        AnySource_NON_POINTER_LOAD++;
        break;
    case HeapNameId::PARAMETER:
        AnySource_PARAMETER++;
        break;
    case HeapNameId::VALUE_NOT_ANALYZED:
        AnySource_VALUE_NOT_ANALYZED++;
        break;
    case HeapNameId::UNKNOWN_OPERATION:
        AnySource_UNKNOWN_OPERATION++;
        break;
    }
}

bool instructionIsHandled(Instruction *Instr) {
    return llvm::dyn_cast<llvm::LoadInst>(Instr) || llvm::dyn_cast<llvm::StoreInst>(Instr) || llvm::dyn_cast<llvm::PHINode>(Instr) || llvm::isNoAliasCall(Instr);
}

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
    Mapping = nullptr;
    *this = Other;
}

EWPTEntry::~EWPTEntry() {
    //printf("Freeing %x\n", Mapping);
    isl_map_free(Mapping);
}

EWPTEntry& EWPTEntry::operator=(const EWPTEntry& Other) {
    this->Rank = Other.Rank;
    this->AmountOfIterators = Other.AmountOfIterators;
    this->HeapIdentifier = Other.HeapIdentifier;

    if(this->Mapping != Other.Mapping) {
        if(this->Mapping != NULL) {
            isl_map_free(this->Mapping);
        }

        if(Other.Mapping != NULL) {
            this->Mapping = isl_map_copy(Other.Mapping);
            //printf("Copying %x\n", Mapping);
        } else {
            this->Mapping = NULL;
        }
    }
    return *this;
}

EWPTEntry EWPTEntry::merge(EWPTEntry& Other) {
    //llvm::outs() << "Values: " << this->HeapIdentifier.toString() << " - " << Other.HeapIdentifier.toString() << "\n";
    ////llvm::outs() << "Ranks: " << this->Rank << " - " << Other.Rank << "\n";
    ////llvm::outs() << "Iters:" << this->AmountOfIterators << " - " << Other.AmountOfIterators << "\n";
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

    if(HeapIdentifier.hasType == HeapNameId::ANY) {
        *this = EWPTEntry::getAny(Analysis, HeapIdentifier.ReasonForAny);
        return true;
    }

    //llvm::outs() << "Attempting to apply subscript " << *Subscript << " to "; this->debugPrint(Analysis); //llvm::outs() << "\n";

    bool IsPointerAligned;
    isl_pw_aff *SubscriptAff = Analysis.getSubscriptSetForOffset(Subscript, Analysis.DL->getPointerSize(), IsPointerAligned);
    if(!SubscriptAff || !IsPointerAligned) {
        *this = EWPTEntry::getAny(Analysis, HeapIdentifier.NON_LINEAR_LOAD);
        return true;
    }
    isl_set *SubscriptSet = isl_map_range(isl_map_from_pw_aff(SubscriptAff));

    // Currently we have a set of the form POINTER_SIZE * i, we need to convert this to just i
    // The division is possible because we ensured an alignment that is a multiple of the pointer size.
    std::string consString = "{ [i] -> [o] : i = " + std::to_string(Analysis.DL->getPointerSize()) + "* o}";
    auto DivisionMapping = isl_map_read_from_str(Analysis.IslContext, consString.c_str());
    SubscriptSet = isl_set_apply(SubscriptSet, DivisionMapping);

    auto EmbedderMapping = Analysis.constructEmbedderMapping(1, Rank, 0);
    SubscriptSet = isl_set_apply(SubscriptSet, EmbedderMapping);

    //llvm::outs() << "Subscript set: " << Analysis.debugSetToString(SubscriptSet) << "\n";
    Analysis.mergeParams(SubscriptSet, Mapping);
    Mapping = isl_map_intersect_domain(Mapping, SubscriptSet);

    if(isl_set_is_empty(isl_map_domain(Mapping))) {
        return false;
    }

    // Project out the first input dimension.
    Mapping = isl_map_project_out(Mapping, isl_dim_in, 0, 1);
    Rank = Rank - 1;

    //llvm::outs() << "After subscript application: "; this->debugPrint(Analysis); //llvm::outs() << "\n";

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

EWPTEntry EWPTEntry::getAny(const EWPTAliasAnalysis& Analysis, HeapNameId::AnyReason Reason) {
    auto EmptySpace = isl_space_alloc(Analysis.IslContext, 0, 0, 0);

    EWPTEntry Entry;
    Entry.HeapIdentifier = HeapNameId::getAny(Reason);
    Entry.AmountOfIterators = 0;
    Entry.Rank = 0;
    Entry.Mapping = isl_map_universe(EmptySpace);

    return Entry;
}

EWPTEntry EWPTEntry::getNull(const EWPTAliasAnalysis& Analysis) {
    auto EmptySpace = isl_space_alloc(Analysis.IslContext, 0, 0, 0);

    EWPTEntry Entry;
    Entry.HeapIdentifier = HeapNameId::getZero();
    Entry.AmountOfIterators = 0;
    Entry.Rank = 0;
    Entry.Mapping = isl_map_universe(EmptySpace);

    return Entry;
}

// ==============================
// EWPTRoot
// ==============================

EWPTRoot EWPTRoot::Any(const EWPTAliasAnalysis& Analysis, HeapNameId::AnyReason Reason) {
    EWPTEntry Entry = EWPTEntry::getAny(Analysis, Reason);

    EWPTRoot RetVal = EWPTRoot();
    auto Key = std::make_pair<unsigned, HeapNameId>(0, HeapNameId::getAny(Reason));
    RetVal.Entries[Key] = Entry;

    return RetVal;
}

EWPTRoot EWPTRoot::Null(const EWPTAliasAnalysis& Analysis) {
    EWPTEntry Entry = EWPTEntry::getNull(Analysis);

    EWPTRoot RetVal = EWPTRoot();
    auto Key = std::make_pair<unsigned, HeapNameId>(0, HeapNameId::getZero());
    RetVal.Entries[Key] = Entry;

    return RetVal;
}

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
        RetVal.push_back(Current->RestrictToLoop->getHeader());
        Current = Current->SuperFrame;
    };
    return RetVal;
}

// =======================================
// EWPTAliasAnalysis
// =======================================

bool EWPTAliasAnalysis::runOnFunction(Function &F)
{
    //llvm::outs() << "Runnoing on function " << F.getName() << "\n";

    // Clean up.
    Frame = EWPTAliasAnalysisFrame();

    // Initialization.
    SE = &getAnalysis<ScalarEvolution>();
    LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    DL = &(F.getParent()->getDataLayout());

    InitializeAliasAnalysis(this, DL);

      for(auto& Block : F) {
        for(auto& Value : Block) {
            if(SE->isSCEVable(Value.getType())) {
                llvm::outs() << "SCEV: " << *SE->getSCEV(&Value) << "\n";
            }
        }
    }

    // The actual analysis.
    auto BeginBlock = &(F.getEntryBlock());
    Frame.BeginBlocks.insert(BeginBlock);
    Frame.RestrictToLoop = NULL;
    Frame.AnalyzedFunction = &F;
    if(!iterativeControlFlowAnalysis(Frame)) {
        // Ensure that no aliasing info is provided.
        FailedFunctionAnalysis++;
        Frame.BlockOutStates.clear();
    } else {
        SuccessfulFunctionAnalysis++;
        bool RankOneEntry = false;
        for(auto& OutStatePair : Frame.BlockOutStates) {
            llvm::outs() << "OutState for block " << OutStatePair.first->getName() << "\n";
            debugPrintEWPTs(OutStatePair.second);
            for(auto& RootPair : OutStatePair.second.trackedRoots) {
                for(auto& EntryPair : RootPair.second.Entries) {
                    auto& Entry = EntryPair.second;
                    if(Entry.Rank >= 1) {
                        RankOneEntry = true;
                        llvm::outs() << "Rank one EWPT:\n";
                        debugPrintEWPTs(OutStatePair.second);
                        llvm::outs() << "In Function:\n";
                        llvm::outs() << F;
                    }
                }
            }
        }

        if(RankOneEntry) {
            SuccessfulRankOneEWPT++;
        }
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
        return PredecessorStates;
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
        llvm::outs() << "Handling block " << *Current << "\n";
        Frame.BlocksToProcess.pop();

        llvm::outs() << "Loop for" << Current->getName() << ": " << LI->getLoopFor(Current) << "\n";

        if(LI->isLoopHeader(Current) && LI->getLoopFor(Current) != Frame.RestrictToLoop) {
            //llvm::outs() << "Previously queued: " << Frame.BlocksToProcess.size() << "\n";
            Loop* LoopToAnalyze = LI->getLoopFor(Current);
            llvm::outs() << "Handling loop" << Current->getName() << "with header " << LI->getLoopFor(Current)->getHeader()->getName() << "(" << LI->isLoopHeader(LI->getLoopFor(Current)->getHeader()) << ")\n";
            bool Success = handleLoop(Frame, *Current, *LoopToAnalyze, Frame.BlockOutStates[Current]);
            llvm::outs() << "Done with loop" << Current->getName() << "\n";
            if(!Success) {
                //llvm::errs() << "Failed to handle loop\n";
                return false;
            }

            //llvm::outs() << "Currently queued: " << Frame.BlocksToProcess.size() << "\n";
            if(Frame.BlocksToProcess.size()) {
                //llvm::outs() << *Frame.BlocksToProcess.front() << "\n";
            }
            //llvm::outs() << "Pushing successors of loop header.\n";

            // Once we're done, process successors outside the loop.
            for(auto SI = succ_begin(Current), E = succ_end(Current); SI != E; SI++) {
                // Check that this successor now has all requirements.
                auto Successor = *SI;

                // Make sure the successor is in the current loop.
                if(LoopToAnalyze->contains(Successor)) {
                   continue;
                }

                if(arePredecessorsProcessed(Frame, Successor) || LI->isLoopHeader(Successor)) {
                    Frame.BlocksToProcess.push(Successor);
                }
            }

            continue;
        } else if(!arePredecessorsProcessed(Frame, Current)) {
            //llvm::outs() << "Trying to process block with unprocessed predecessors.";
            NonLoopCycle++;
            return false;
        } else {
            auto StartWithState = MergeStates(getPredecessorStates(Frame, Current));
            if(!runOnBlock(*Current, Frame, StartWithState, Frame.BlockOutStates[Current])) {
                return false;
            }

            // Once this frame is done, try processing successors
            for(auto SI = succ_begin(Current), E = succ_end(Current); SI != E; SI++) {
                // Check that this successor now has all requirements.
                auto Successor = *SI;

                // Make sure the successor is in the current loop.
                bool LoopContainsSuccessor = !Frame.RestrictToLoop || Frame.RestrictToLoop->contains(Successor);
                if(!LoopContainsSuccessor) {
                    // If current is the loop header, we simply ignore "exit" edges.
                    if(Current == Frame.RestrictToLoop->getHeader()) {
                        continue;
                    } else {
                        // Otherwise we have something like a break, error
                        LoopExitOutsideLoopHeader++;
                        return false;
                    }
                }

                // If the successor is the loop header, it's the back edge. Ignore.
                if(Frame.RestrictToLoop && Successor == Frame.RestrictToLoop->getHeader()) {
                    continue;
                }

                // If the next block has already been processed, we have a non-loop cycle
                if(Frame.BlockOutStates[Successor].trackedRoots.size()) {
                    llvm::outs() << "Block " << Successor->getName() << " has already been processed.\n";
                    NonLoopCycle++;
                    return false;
                }

                // Delay processing of this successor block until all successors are processed.
                if(arePredecessorsProcessed(Frame, Successor) || LI->isLoopHeader(Successor)) {
                    llvm::outs() << "Pushing successor for " << Current->getName() << ": " << Successor->getName() << "\n";
                    Frame.BlocksToProcess.push(Successor);
                }
            }
        }
    }

    // Make sure all blocks were processed.
    std::vector<const BasicBlock*> Blocks;
    if(Frame.RestrictToLoop) {
        for(auto& Block : Frame.RestrictToLoop->getBlocks()) {
            Blocks.push_back(Block);
        }
    } else {
        for(auto& Block : Frame.AnalyzedFunction->getBasicBlockList()) {
            Blocks.push_back(&Block);
        }
    }
    for(const BasicBlock* Block : Blocks) {
        if(!Frame.BlockOutStates.count(Block)) {
            // The reason a block may not have been processed is that we will "delay"
            // the processing of blocks that still have unprocessed predecessors.
            // However, if there's a cycle, there will always be an unprocessed predecessor,
            // and the loop will never be processed.
            NonLoopCycle++;
            return false;
        }
    }

    return true;
}

bool EWPTAliasAnalysis::handleLoop(EWPTAliasAnalysisFrame& SuperFrame, BasicBlock& LoopHeader, Loop& LoopToAnalyze, EWPTAliasAnalysisState& RetVal) {
    // We can only handle loops of a specific type, check these properties first.

    // It must have exactly one back edge to the loop header.
    if(LoopToAnalyze.getNumBackEdges() != 1) {
        ++TooManyLoopBackEdges;
        //llvm::errs() << "Too many back edges for loop " << LoopToAnalyze << "\n";
        return false;
    }

    // The loop must also be dominated by its header and all edges from outside the loop
    // must point toward the loop header, but these are already requirements for "natural loops"
    // as recognized by LoopInfo.

    EWPTAliasAnalysisState ExitState;
    auto InductionVariable = LoopToAnalyze.getHeader();
    auto IVName = InductionVariable->getName().str();

    auto EntryState = MergeStates(getPredecessorStates(SuperFrame, &LoopHeader));

    std::vector<EWPTAliasAnalysisFrame> SubFrames;

    bool FixedPointReached = false;
    for(unsigned I = 0; I < 3; I++) {
        // Create a new analysis frame for the analysis of the loop body.
        EWPTAliasAnalysisFrame SubFrame;
        SubFrame.EntryState = EntryState;
        SubFrame.RestrictToLoop = &LoopToAnalyze;
        SubFrame.SuperFrame = &SuperFrame;
        SubFrame.BlockOutStates = SuperFrame.BlockOutStates;

        SubFrame.BeginBlocks.insert(&LoopHeader);

        // Start the sub-analysis with the loop header as "exit node"
        bool Success = iterativeControlFlowAnalysis(SubFrame);
        if(!Success) {
            llvm::outs() << "Control flow analysis in sub-frame failed\n";
            return false;
        }

        // Extract the out state of all predecessors of the loop header that come
        // from within the loop.
        // TODO: this is redundant with code in getPredecessorStates
        std::vector<EWPTAliasAnalysisState*> PredecessorStates;
        for(auto PI = pred_begin(&LoopHeader), E = pred_end(&LoopHeader); PI != E; PI++) {
            auto Predecessor = *PI;
            if(!SubFrame.RestrictToLoop->contains(Predecessor)) {
                continue;
            }
            auto& PredecessorState = SubFrame.BlockOutStates[Predecessor];
            PredecessorStates.push_back(&PredecessorState);
        }
        ExitState = MergeStates(PredecessorStates);

        llvm::outs() << "Before aging\n";
        debugPrintEWPTs(ExitState);

        // Replace "i" by "i-" for the state of the loop header
        // Add a new "i"
        // Project out "i-"
        for(auto& RootPair : ExitState.trackedRoots) {
            auto& PointsToMapping = RootPair.second;
            for(auto& EntryPair : PointsToMapping.Entries) {
                auto& Entry = EntryPair.second;

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
                Entry.Mapping = isl_map_project_out(Entry.Mapping, isl_dim_param, 0, 1);

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

                // We furthermore know that 0 <= i-
                Constraint = isl_inequality_alloc(isl_local_space_from_space(isl_map_get_space(Entry.Mapping)));
                Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_param , 1, 0);
                Entry.Mapping = isl_map_add_constraint(Entry.Mapping, Constraint);

                //llvm::outs() << "Mapping before projecting out: " << debugMappingToString(Entry.Mapping) << "\n";
                Entry.Mapping = isl_map_project_out(Entry.Mapping, isl_dim_param, 1, 1);
                //llvm::outs() << "Mapping after projecting out: " << debugMappingToString(Entry.Mapping) << "\n";

                // Project out parameter dimensions that aren't constant, unless they're the iterator.
                for(unsigned i = 0; i < isl_space_dim(isl_map_get_space(Entry.Mapping), isl_dim_param); i++) {
                    auto DimIdentifier = isl_space_get_dim_id(isl_map_get_space(Entry.Mapping), isl_dim_param, i);
                    llvm::Value *Variable = (llvm::Value*) isl_id_get_user(DimIdentifier);
                    isl_id_free(DimIdentifier);

                    // Check if it's a loop induction variable. If it is, it must either be the
                    // loop induction variable of this loop (we don't project that one out), or
                    // of an outer loop (which is constant during this loop).
                    if(isa<llvm::BasicBlock>(Variable)) {
                        continue;
                    }

                    // If it's a regular LLVM value, we just ask the loop whether it's invariant.
                    if(!SubFrame.RestrictToLoop->isLoopInvariant(Variable)) {
                        // Not constant, must project it out.
                        Entry.Mapping = isl_map_project_out(Entry.Mapping, isl_dim_param, i, 1);
                        i--;
                    }
                }

                ExitState.trackedRoots[RootPair.first].Entries[EntryPair.first] = Entry;
            }
        }

        llvm::outs() << "After aging\n";
        debugPrintEWPTs(ExitState);

        if(ExitState.equals(EntryState)) {
            EntryState = ExitState;
            FixedPointReached = true;
            break;
        }

        // Do another iteration to see if we're at a fixed point yet
        EntryState = ExitState;
        SubFrames.push_back(SubFrame);
    }

    if(FixedPointReached) {
        // Do binding.

        llvm::outs() << "Before binding\n";
        debugPrintEWPTs(EntryState);

        // Compute a set containing the upper bound as single point.
        const SCEV *UpperBoundSCEV = SE->getBackedgeTakenCount(&LoopToAnalyze);
        if(isa<llvm::SCEVCouldNotCompute>(UpperBoundSCEV)) {
            CouldNotAffinateSCEV++;
            return false;
        }

        isl_pw_aff *UpperBound = SCEVAffinator::getPwAff(this, UpperBoundSCEV, IslContext);
        if(!UpperBound) {
            return false;
        }
        isl_set *BoundSet = isl_map_range(isl_map_from_pw_aff(UpperBound));
        llvm::outs() << "Upper bound set: " << debugSetToString(BoundSet) << "\n";

        // Add the constraint that the iterator be smaller than the upper bound.
        auto Identifier = isl_id_alloc(IslContext, IVName.c_str(), InductionVariable);
        auto Model = isl_space_params_alloc(IslContext, 1);
        Model = isl_space_set_dim_id(Model, isl_dim_param, 0, Identifier);
        BoundSet = isl_set_align_params(BoundSet, Model);

        // i <= UpperBound
        auto Constraint = isl_inequality_alloc(isl_local_space_from_space(isl_set_get_space(BoundSet)));
        Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_param, 0, -1);
        Constraint = isl_constraint_set_coefficient_si(Constraint, isl_dim_set, 0, 1);
        // Add the constant 1, as we want an upper bound for the first iterator that is not executed,
        // rather than an upper bound for the last iterator that is executed.
        Constraint = isl_constraint_set_constant_si(Constraint, 1);
        BoundSet = isl_set_add_constraint(BoundSet, Constraint);

        // Project out the set dimension.
        BoundSet = isl_set_project_out(BoundSet, isl_dim_set, 0, 1);
        llvm::outs() << "Bound set: " << debugSetToString(BoundSet) << "\n";

        // i must be <= UpperBound

        for(auto& RootPair : EntryState.trackedRoots) {
            auto& PointsToMapping = RootPair.second;
            for(auto& EntryPair : PointsToMapping.Entries) {
                auto& Entry = EntryPair.second;

                isl_set *BoundSetTmp = isl_set_copy(BoundSet);
                mergeParams(BoundSetTmp, Entry.Mapping);
                llvm::outs() << "Mapping: " << debugMappingToString(Entry.Mapping) << "\n";
                Entry.Mapping = isl_map_intersect_params(Entry.Mapping, BoundSetTmp);
                llvm::outs() << "Mapping 2: " << debugMappingToString(Entry.Mapping) << "\n";

                // We know that the induction variable is at parameter position 0 because we aligned
                // the UpperBoundSet that way.
                Entry.Mapping = isl_map_project_out(Entry.Mapping, isl_dim_param, 0, 1);
                llvm::outs() << "Mapping after: " << debugMappingToString(Entry.Mapping) << "\n";

                EntryState.trackedRoots[RootPair.first].Entries[EntryPair.first] = Entry;
            }
        }

        isl_set_free(BoundSet);

        llvm::outs() << "After binding\n";
        debugPrintEWPTs(EntryState);

        RetVal = EntryState;

        // After binding, propagate the states within the loop up to the super frame.
        // For this we merge the states of all the subframes we produced.
        for(auto& Pair : SubFrames[0].BlockOutStates) {
            if(!LoopToAnalyze.contains(Pair.first) || LoopToAnalyze.getHeader() == Pair.first) {
                continue;
            }

            // Merge together all states of this subframe
            std::vector<EWPTAliasAnalysisState*> States;
            for(auto& SubFrame : SubFrames) {
                States.push_back(&SubFrame.BlockOutStates[Pair.first]);
            }
            auto MergedState = MergeStates(States);

            // Propagate it up into the super frame.
            SuperFrame.BlockOutStates[Pair.first] = MergedState;
        }

        return true;
    } else {
        // We did not converge after a certain amount of iterations.
        ++LoopDidNotConverge;
        return false;
    }

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

isl_pw_aff *EWPTAliasAnalysis::getSubscriptSetForOffset(const SCEV *Offset, int Alignment, bool& IsPointerAligned) {
    isl_pw_aff *SubscriptAff = SCEVAffinator::getPwAff(this, Offset, IslContext);
    if(!SubscriptAff) {
        IsPointerAligned = false;
        return NULL;
    }

    // Check if we can always divide the offset by the system's pointer width
    isl_pw_aff *Remainder = isl_pw_aff_mod_val(isl_pw_aff_copy(SubscriptAff), isl_val_int_from_si(IslContext, Alignment));
    isl_set *TestSet = isl_pw_aff_zero_set(Remainder);

    // If the zero set is universe, then the access is pointer aligned.
    // If the complement is empty, then the set is also pointer aligned.
    TestSet = isl_set_complement(TestSet);
    IsPointerAligned = isl_set_is_empty(TestSet);
    isl_set_free(TestSet);

    return SubscriptAff;
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

    ////llvm::outs() << "LEFTHAND: " << debugMappingToString(LeftHand.Mapping) << "\n"; //llvm::outs().flush();
    ////llvm::outs() << "RIGHTHAND: " << debugMappingToString(RightHand.Mapping) << "\n"; //llvm::outs().flush();
    // Constrain the LeftHand mapping to those indices where it might map to a heap object in RightHand
    auto AliasMapping = isl_map_intersect_range(isl_map_copy(LeftHand.Mapping), isl_map_range(isl_map_copy(RightHand.Mapping)));
    ////llvm::outs() << "TEST: " << debugMappingToString(isl_map_universe(isl_space_alloc(IslContext, 0, 1, 1))) << "\n"; //llvm::outs().flush();

    ////llvm::outs() << "INTERSECTED:" << debugMappingToString(AliasMapping) << "\n"; //llvm::outs().flush();


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
bool EWPTAliasAnalysis::generateEntryFromHeapAssignment(int EntranceDepth, isl_set *EntranceConstraints, EWPTEntry& AssigneeMapping, isl_set *SubscriptSet, EWPTEntry& RetVal) {
    ////llvm::outs() << "Generate Heap Assignment:: EntranceDepth = " << EntranceDepth << ", EntranceConstraints = " << debugSetToString(EntranceConstraints) << ", AssigneeMapping = " << debugMappingToString(AssigneeMapping.Mapping) << ", BridgeValue = " << *BridgeValue << "\n";

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

    // The SCEVAffinator gives us a mapping with a range of dimension 1.
    // We need to embed this dimension into the mapping we're generating, where this dimension
    // should align with the bridge dimension (at position InputSize).
    EmbedderMapping = constructEmbedderMapping(1, InputSize, EntranceDepth);
    SubscriptSet = isl_set_apply(SubscriptSet, EmbedderMapping);
    ////llvm::outs() << "Subscript set: " << Analysis.debugSetToString(SubscriptSet) << "\n";
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

    ////llvm::outs() << "EmbeddedAssigneeMapping: " << debugMappingToString(EmbeddedAssigneeMapping) << "\n";
    ////llvm::outs().flush();
    ////llvm::outs() << "NewMapping: " << debugMappingToString(NewMapping) << "\n";
    ////llvm::outs().flush();
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

    return true;
}

bool EWPTAliasAnalysis::handleHeapAssignment(StoreInst *AssigningInstruction, EWPTAliasAnalysisState& State, EWPTAliasAnalysisFrame& Frame) {
    llvm::Value *AssignedValue = AssigningInstruction->getValueOperand();
    /*llvm::outs() << "In Loop " << Frame.RestrictToLoop << "\n";
    llvm::outs() << "Surrounding loop" << LI->getLoopFor(AssigningInstruction->getParent()) << "\n";*/

    const SCEV *AccessFunction = SE->getSCEVAtScope(AssigningInstruction->getPointerOperand(), Frame.RestrictToLoop);
    auto BasePointer = dyn_cast<SCEVUnknown>(SE->getPointerBase(AccessFunction));

    if (!BasePointer) {
        NoScevForBasePointer++;
        //llvm::errs() << "Can not handle base pointer for " << *AssigningInstruction << "\n";
        return false;
    }

    auto BasePointerValue = BasePointer->getValue();

    if (isa<UndefValue>(BasePointerValue)) {
        NoScevForBasePointer++;
        //llvm::errs() << "Can not handle base value for " << *AssigningInstruction << "\n";
        return false;
    }

    auto Offset = SE->getMinusSCEV(AccessFunction, BasePointer);
    /*llvm::outs() << "Access Function: ";
    AccessFunction->dump();
    llvm::outs() << "\n";*/

    EWPTRoot AssignedMapping;
    // Get the appropriate EWPT mapping for the assigned value.
    // This could possibly be an ANY EWPT.
    getEWPTForValue(State, AssignedValue, AssignedMapping);

    // Get all EWPT entries of depth 0.
    std::vector<EWPTEntry> ModifiedHeapObjects;
    if(!State.trackedRoots.count(BasePointerValue)) {
        WriteToAny++;
        if(isa<Argument>(BasePointerValue)) {
            AnySource_PARAMETER++;
        } else {
            AnySource_VALUE_NOT_ANALYZED++;
        }
        return false;
    }
    for(auto& EntryPair : State.trackedRoots[BasePointerValue].Entries) {
        auto& Entry = EntryPair.second;
        if(Entry.Rank == 0) {
            ////llvm::outs() << "Found entry of depth 0 " << *(Entry.SourceLocation) << "\n";
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
            WriteToAny++;
            IncrementStatisticForAnySource(ModifiedHeapObject.HeapIdentifier.ReasonForAny);
            //llvm::errs() << "Aborting analysis because of potential write to ANY.\n";
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

                    // If the store is pointer aligned, we only need to generate one new EWPT entry.
                    // However, if the store isn't pointer aligned, we need to generate one "ANY" EWPT entry
                    // for each pointer cell that is overwritten.

                    // Compute the indices within the assignee heap object at which we're inserting
                    // the new tail EWPT.
                    //
                    // If the store is pointer aligned, we need only consider one index
                    // (the same index that we're storing the pointer value to).
                    //
                    // If the store isn't pointer aligned, we need to consider all indices that overlap
                    // the memory region that is modified by the store.

                    bool AccessIsPointerAligned;
                    isl_pw_aff *SubscriptAff = this->getSubscriptSetForOffset(Offset, DL->getPointerSize(), AccessIsPointerAligned);

                    if(!SubscriptAff) {
                        return false;
                    }

                    AccessIsPointerAligned = AccessIsPointerAligned && AssigningInstruction->getValueOperand()->getType()->getScalarSizeInBits() <= DL->getPointerSizeInBits();
                    //llvm::outs() << "Bit size for instruction " << *AssigningInstruction << ": " << AssigningInstruction->getValueOperand()->getType()->getScalarSizeInBits() << " (<= " << DL->getPointerSizeInBits() << ")\n";
                    //htllvm::outs() << "Zero set " << debugSetToString(TestSet) << "\n";

                    isl_set *SubscriptSet = isl_map_range(isl_map_from_pw_aff(SubscriptAff));

                    // Currently we have a set of the form POINTER_SIZE * i, we need to convert this to just i
                    std::string consString = "{ [i] -> [o] : i = " + std::to_string(DL->getPointerSize()) + "* o}";
                    auto DivisionMapping = isl_map_read_from_str(IslContext, consString.c_str());
                    SubscriptSet = isl_set_apply(SubscriptSet, DivisionMapping);

                    EWPTEntry NewEntry;

                    // Check if we're storing to an aligned position.
                    if(!AccessIsPointerAligned) {
                        // TODO: recursive ANY

                        unsigned Alignment = AssigningInstruction->getAlignment();

                        // Convert SubscriptSet from a single point to a range.
                        consString = "[n] -> { [x] -> [] : n = x }";
                        isl_map *ConvertToParams = isl_map_read_from_str(IslContext, consString.c_str());
                        SubscriptSet = isl_set_apply(SubscriptSet, ConvertToParams);

                        int AmountOfPointersOverwritten =
                                (int) ceil((float) Alignment / DL->getPointerSize());
                        consString = (std::string) "[n] -> { [i] : n <= i <= n + " + std::to_string(AmountOfPointersOverwritten) + " }";
                        auto RangeSet = isl_set_read_from_str(IslContext, consString.c_str());

                        SubscriptSet = isl_set_intersect_params(RangeSet, SubscriptSet);

                        // We no longer need the parameter n
                        SubscriptSet = isl_set_project_out(SubscriptSet, isl_dim_param, 0, 1);
                        llvm::outs() << "subscript set: " << debugSetToString(SubscriptSet) << "\n";

                        EWPTEntry AnyEntry = EWPTEntry::getAny(*this, HeapNameId::UNALIGNED_STORE);

                        if(!generateEntryFromHeapAssignment(PossibleAlias.Rank, isl_set_copy(EntranceConstraints), AnyEntry, SubscriptSet, NewEntry)) {
                            return false;
                        }

                        NewEntry.debugPrint(*this);
                    } else {
                        for(auto& TailMappingPair : AssignedMapping.Entries) {
                            auto& TailMapping = TailMappingPair.second;

                            // If we would build an EWPT entry for p that ends again in p, abort.
                            if(TailMapping.HeapIdentifier.hasType == HeapNameId::MALLOC &&
                               TailMapping.HeapIdentifier.SourceLocation == RootPair.first) {
                                CyclicHeapMemoryGraph++;
                                //llvm::errs() << "Cyclic heap memory graph detected, aborting.\n";
                                return false;
                            }

                            if(!generateEntryFromHeapAssignment(PossibleAlias.Rank, isl_set_copy(EntranceConstraints), TailMapping, SubscriptSet, NewEntry)) {
                                return false;
                            }
                        }
                    }

                    auto KeyForNewEntry = std::make_pair(NewEntry.Rank, NewEntry.HeapIdentifier);
                    if(!RootMapping.Entries.count(KeyForNewEntry)) {
                        RootMapping.Entries[KeyForNewEntry] = NewEntry;
                    } else {
                        RootMapping.Entries[KeyForNewEntry].debugPrint(*this);
                        NewEntry.debugPrint(*this);
                        RootMapping.Entries[KeyForNewEntry] = RootMapping.Entries[KeyForNewEntry].merge(NewEntry);
                    }

                    //RootMapping.Entries[KeyForNewEntry].debugPrint(*this);

                    isl_set_free(EntranceConstraints);
                }
            }
        }
    }

    return true;
}

bool EWPTAliasAnalysis::handleLoad(LoadInst *CurrentLoadInst, EWPTAliasAnalysisFrame &Frame, EWPTAliasAnalysisState& State) {
    ////llvm::outs() << "Handling Load\n";

    if(!CurrentLoadInst->getPointerOperand()->getType()->isPointerTy()) {
        State.trackedRoots[CurrentLoadInst] = EWPTRoot::Any(*this, HeapNameId::NON_POINTER_LOAD);
        return true;
    }

    const SCEV *AccessFunction = SE->getSCEVAtScope(CurrentLoadInst->getPointerOperand(), Frame.RestrictToLoop);
    auto BasePointer = dyn_cast<SCEVUnknown>(SE->getPointerBase(AccessFunction));

    if (!BasePointer) {
        State.trackedRoots[CurrentLoadInst] = EWPTRoot::Any(*this, HeapNameId::NON_LINEAR_LOAD);
        return true;
    }

    auto BaseValue = BasePointer->getValue();

    if (isa<UndefValue>(BaseValue)) {
        State.trackedRoots[CurrentLoadInst] = EWPTRoot::Any(*this, HeapNameId::NON_LINEAR_LOAD);
        return true;
    }

    auto Offset = SE->getMinusSCEV(AccessFunction, BasePointer);

    // Check if we have an EWPT entry for our base pointer
    if (State.trackedRoots.count(BaseValue)) {
        auto LoadedFrom = State.trackedRoots[BaseValue];

        // We're indexing into the loaded EWPT, so apply a subscript
        EWPTRoot NewRoot;
        LoadedFrom.ApplySubscript(*this, Offset, Frame, State, NewRoot);
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
        RetVal = EWPTRoot::Null(*this);
        return true;
    }

    // No valid EWPT found, return an EWPT that can point to any value.
    if(isa<llvm::Argument>(PointerValBase)) {
        RetVal = EWPTRoot::Any(*this, HeapNameId::PARAMETER);
    } else if(!isa<llvm::Instruction>(PointerValBase) || !instructionIsHandled(dyn_cast<Instruction>(PointerValBase))) {
        RetVal = EWPTRoot::Any(*this, HeapNameId::UNKNOWN_OPERATION);
    } else {
        RetVal = EWPTRoot::Any(*this, HeapNameId::VALUE_NOT_ANALYZED);
    }

    return false;
}

bool EWPTAliasAnalysis::runOnBlock(BasicBlock &block, EWPTAliasAnalysisFrame& Frame, EWPTAliasAnalysisState& InState, EWPTAliasAnalysisState& RetValState)
{
    RetValState = InState;
    for(Instruction &CurrentInstruction : block.getInstList()) {
        ////llvm::outs() << "Handling instruction " << CurrentInstruction << "\n";

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
                this->getEWPTForValue(RetValState, IncomingValue, Root);
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

            //printf("Root %x Entry %x\n", Root.Entries[KeyForNewEntry].Mapping, Entry.Mapping);

            ////llvm::outs() << "Added new 0 depth entry for " << CurrentInstruction << "\n";
            ////llvm::outs() << "New constraints: " << debugMappingToString(Entry.Mapping) << "\n";
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

AliasResult EWPTAliasAnalysis::alias(const MemoryLocation& LocA, const MemoryLocation& LocB) {
    auto PtrA = (Instruction*) llvm::dyn_cast<Instruction>(LocA.Ptr->stripPointerCasts());
    auto PtrB = (Instruction*) llvm::dyn_cast<Instruction>(LocB.Ptr->stripPointerCasts());

    if(!PtrA || !PtrB) {
#ifdef DEBUG_PRINT_ALIAS
        //llvm::outs() << "Locations given aren't instructions, returning MayAlias\n";
#endif
        return AliasAnalysis::alias(LocA, LocB);
    }

    if(!instructionIsHandled(PtrA) || !instructionIsHandled(PtrB)) {
#ifdef DEBUG_PRINT_ALIAS
        //llvm::outs() << "Instructions of unhandled type, returning MayAlias\n";
#endif
        return AliasAnalysis::alias(LocA, LocB);
    }

    BasicBlock* ContainerBlockA = (BasicBlock*) PtrA->getParent();
    BasicBlock* ContainerBlockB = (BasicBlock*) PtrB->getParent();

    if(!Frame.BlockOutStates.count(ContainerBlockA) ||
       !Frame.BlockOutStates.count(ContainerBlockB)) {
#ifdef DEBUG_PRINT_ALIAS
        //llvm::outs() << "Incomplete analysis returning MayAlias\n";
#endif
        return AliasAnalysis::alias(LocA, LocB);
    }

    auto OutStateA = Frame.BlockOutStates[ContainerBlockA];
    auto OutStateB = Frame.BlockOutStates[ContainerBlockB];

    // Get EWPTs for A and B in that state.
    auto RootA = OutStateA.trackedRoots[PtrA];
    auto RootB = OutStateB.trackedRoots[PtrB];

#ifdef DEBUG_PRINT_ALIAS
    //llvm::outs() << "Alias check for " << *PtrA << " and " << *PtrB << "(SV: " << RootA.isSingleValued() << " Match: " << RootA.equals(RootB) << ")\n";

    //llvm::outs() << "Container block A: " << *ContainerBlockA << "\n";
    //llvm::outs() << "Container block B: " << *ContainerBlockB << "\n";

    //llvm::outs() << "EWPT A:";
    //debugPrintEWPTs(OutStateA);
    //llvm::outs() << "\n";
    //llvm::outs() << "EWPT B:";
    //debugPrintEWPTs(OutStateB);
    //llvm::outs() << "\n";

    //llvm::outs() << "RootA";
    RootA.debugPrint(*this);
    //llvm::outs() << "RootB";
    RootB.debugPrint(*this);
#endif

    EWPTEntry *SingleValueA = RootA.isSingleValued();
    EWPTEntry *SingleValueB = RootB.isSingleValued();
    if(SingleValueA && SingleValueB) {
        if(SingleValueA->HeapIdentifier == SingleValueB->HeapIdentifier && isl_map_is_equal(SingleValueA->Mapping, SingleValueB->Mapping)) {
#ifdef DEBUG_PRINT_ALIAS
            //llvm::outs() << "Returning MustAlias.\n";
#endif
            return MustAlias;
        }
    }

    // Intersect EWPTs at rank 0.
    auto Intersection = RootA.intersect(RootB, 0);

    // Check how many elements there are in the intersection.
    // If there's none, NoAlias. Otherwise, mayalias.
    if(!Intersection.Entries.size()) {
#ifdef DEBUG_PRINT_ALIAS
        //llvm::outs() << "Returning NoAlias.\n";
#endif
        return NoAlias;
    } else {
#ifdef DEBUG_PRINT_ALIAS
        //llvm::outs() << "Returning MayAlias.";
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
  //llvm::outs() << "SCEV: " << *Scev << "\n";

  // TODO: initialize parameter dimension
  SCEVAffinator Affinator(Analysis);
  Affinator.Ctx = Ctx;
  auto RetVal = Affinator.visit(Scev);
  if(Affinator.Failed) {
      CouldNotAffinateSCEV++;
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
        isl_pw_aff_free(Start);
        isl_pw_aff_free(Step);

        Failed = true;
        FailedReason = "Stride isn't constant.";
        return nullptr;
    }

    isl_space *Space = isl_space_set_alloc(Ctx, 0, 0);

    auto LoopIndex = Expr->getLoop()->getHeader();
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

  if(!isa<ConstantInt>(Divisor)) {
      Failed = true;
      FailedReason = "SCEVAffinator: RHS of division is non-constant.";
      return nullptr;
  }

  auto *DivisorSCEV = SE->getSCEV(Divisor);
  auto *DivisorPWA = visit(DivisorSCEV);

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
