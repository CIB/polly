//=== ScopDetectionDiagnostic.h -- Diagnostic for ScopDetection -*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Small set of diagnostic helper classes to encapsulate any errors occurred
// during the detection of Scops.
//
// The ScopDetection defines a set of error classes (via Statistic variables)
// that groups a number of individual errors into a group, e.g. non-affinity
// related errors.
// On error we generate an object that carries enough additional information
// to diagnose the error and generate a helpful error message.
//
//===----------------------------------------------------------------------===//
#ifndef POLLY_SCOP_DETECTION_DIAGNOSTIC_H
#define POLLY_SCOP_DETECTION_DIAGNOSTIC_H

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/AliasSetTracker.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Value.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Support/Casting.h"

#include <string>
#include <memory>

using namespace llvm;

namespace llvm {
class SCEV;
class BasicBlock;
class Value;
class Region;
}

namespace polly {

/// @brief Get the location of a region from the debug info.
///
/// @param R The region to get debug info for.
/// @param LineBegin The first line in the region.
/// @param LineEnd The last line in the region.
/// @param FileName The filename where the region was defined.
void getDebugLocation(const Region *R, unsigned &LineBegin, unsigned &LineEnd,
                      std::string &FileName);

// Discriminator for LLVM-style RTTI (dyn_cast<> et al.)
enum RejectReasonKind {
  // CFG Category
  rrkCFG,
  rrkNonBranchTerminator, rrkCondition,

  // Non-Affinity
  rrkAffFunc,
  rrkUndefCond, rrkInvalidCond, rrkUndefOperand, rrkNonAffBranch,
  rrkNoBasePtr, rrkUndefBasePtr, rrkVariantBasePtr, rrkNonAffineAccess,

  // IndVar
  rrkIndVar,
  rrkPhiNodeRefInRegion, rrkNonCanonicalPhiNode, rrkLoopHeader,

  rrkIndEdge,

  rrkLoopBound,

  rrkFuncCall,

  rrkAlias,

  rrkSimpleLoop,

  // Other
  rrkOther,
  rrkIntToPtr, rrkAlloca, rrkUnknownInst, rrkPHIinExit, rrkEntry
};

//===----------------------------------------------------------------------===//
/// @brief Base class of all reject reasons found during Scop detection.
///
/// Subclasses of RejectReason should provide means to capture enough
/// diagnostic information to help clients figure out what and where something
/// went wrong in the Scop detection.
class RejectReason {
  //===--------------------------------------------------------------------===//
public:
private:
  const RejectReasonKind Kind;

public:
  RejectReasonKind getKind() const { return Kind; }

  RejectReason(RejectReasonKind K) : Kind(K) {}

  virtual ~RejectReason() {};

  /// @brief Generate a reasonable diagnostic message describing this error.
  ///
  /// @return A debug message representing this error.
  virtual std::string getMessage() const = 0;
};

typedef std::shared_ptr<RejectReason> RejectReasonPtr;

/// @brief Stores all errors that ocurred during the detection.
class RejectLog {
  Region *R;
  llvm::SmallVector<RejectReasonPtr, 1> ErrorReports;

public:
  explicit RejectLog(Region *R) : R(R) {};

  typedef llvm::SmallVector<RejectReasonPtr, 1>::iterator iterator;

  iterator begin() { return ErrorReports.begin(); }
  iterator end() { return ErrorReports.end(); }
  size_t size() { return ErrorReports.size(); }

  void print(raw_ostream &OS, int level = 0) const;

  const Region *region() const { return R; }
  void report(RejectReasonPtr Reject) { ErrorReports.push_back(Reject); }
};

//===----------------------------------------------------------------------===//
/// @brief Base class for CFG related reject reasons.
///
/// Scop candidates that violate structural restrictions can be grouped under
/// this reject reason class.
class ReportCFG : public RejectReason {
  //===--------------------------------------------------------------------===//
public:
  ReportCFG(const RejectReasonKind K);
};

class ReportNonBranchTerminator : public ReportCFG {
  BasicBlock *BB;

public:
  ReportNonBranchTerminator(BasicBlock *BB)
      : ReportCFG(rrkNonBranchTerminator), BB(BB) {};

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkNonBranchTerminator;
  }
  /// @name RejectReason interface
  //@{
  virtual std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures a not well-structured condition within the CFG.
class ReportCondition : public ReportCFG {
  //===--------------------------------------------------------------------===//

  // The BasicBlock we found the broken condition in.
  BasicBlock *BB;

public:
  ReportCondition(BasicBlock *BB) : ReportCFG(rrkCondition), BB(BB) {};

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkCondition;
  }

  /// @name RejectReason interface
  //@{
  virtual std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Base class for non-affine reject reasons.
///
/// Scop candidates that violate restrictions to affinity are reported under
/// this class.
class ReportAffFunc : public RejectReason {
  //===--------------------------------------------------------------------===//
public:
  ReportAffFunc(const RejectReasonKind K);
};

//===----------------------------------------------------------------------===//
/// @brief Captures a condition that is based on an 'undef' value.
class ReportUndefCond : public ReportAffFunc {
  //===--------------------------------------------------------------------===//

  // The BasicBlock we found the broken condition in.
  BasicBlock *BB;

public:
  ReportUndefCond(BasicBlock *BB) : ReportAffFunc(rrkUndefCond), BB(BB) {};

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkAffFunc;
  }

  /// @name RejectReason interface
  //@{
  virtual std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures an invalid condition
///
/// Conditions have to be either constants or icmp instructions.
class ReportInvalidCond : public ReportAffFunc {
  //===--------------------------------------------------------------------===//

  // The BasicBlock we found the broken condition in.
  BasicBlock *BB;

public:
  ReportInvalidCond(BasicBlock *BB) : ReportAffFunc(rrkInvalidCond), BB(BB) {};

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkInvalidCond;
  }
  
  /// @name RejectReason interface
  //@{
  virtual std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures an undefined operand.
class ReportUndefOperand : public ReportAffFunc {
  //===--------------------------------------------------------------------===//

  // The BasicBlock we found the undefined operand in.
  BasicBlock *BB;

public:
  ReportUndefOperand(BasicBlock *BB)
      : ReportAffFunc(rrkUndefOperand), BB(BB) {};

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkUndefOperand;
  }
  
  /// @name RejectReason interface
  //@{
  virtual std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures a non-affine branch.
class ReportNonAffBranch : public ReportAffFunc {
  //===--------------------------------------------------------------------===//

  // The BasicBlock we found the non-affine branch in.
  BasicBlock *BB;

  /// @brief LHS & RHS of the failed condition.
  //@{
  const SCEV *LHS;
  const SCEV *RHS;
  //@}

public:
  ReportNonAffBranch(BasicBlock *BB, const SCEV *LHS, const SCEV *RHS)
      : ReportAffFunc(rrkNonAffBranch), BB(BB), LHS(LHS), RHS(RHS) {};

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkNonAffBranch;
  }

  const SCEV *lhs() { return LHS; }
  const SCEV *rhs() { return RHS; }

  /// @name RejectReason interface
  //@{
  virtual std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures a missing base pointer.
class ReportNoBasePtr : public ReportAffFunc {
  //===--------------------------------------------------------------------===//
public:
  ReportNoBasePtr() : ReportAffFunc(rrkNoBasePtr) {}

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkNoBasePtr;
  }
  
  /// @name RejectReason interface
  //@{
  virtual std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures an undefined base pointer.
class ReportUndefBasePtr : public ReportAffFunc {
  //===--------------------------------------------------------------------===//
public:
  ReportUndefBasePtr() : ReportAffFunc(rrkUndefBasePtr) {}

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkUndefBasePtr;
  }
  
  /// @name RejectReason interface
  //@{
  virtual std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures a base pointer that is not invariant in the region.
class ReportVariantBasePtr : public ReportAffFunc {
  //===--------------------------------------------------------------------===//

  // The variant base pointer.
  Value *BaseValue;

public:
  ReportVariantBasePtr(Value *BaseValue)
      : ReportAffFunc(rrkVariantBasePtr), BaseValue(BaseValue) {};

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkVariantBasePtr;
  }
  
  /// @name RejectReason interface
  //@{
  virtual std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures a non-affine access function.
class ReportNonAffineAccess : public ReportAffFunc {
  //===--------------------------------------------------------------------===//

  // The non-affine access function.
  const SCEV *AccessFunction;

public:
  ReportNonAffineAccess(const SCEV *AccessFunction)
      : ReportAffFunc(rrkNonAffineAccess), AccessFunction(AccessFunction) {};

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkNonAffineAccess;
  }
  
  const SCEV *get() { return AccessFunction; }

  /// @name RejectReason interface
  //@{
  virtual std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Base class for reject reasons related to induction variables.
///
//  ReportIndVar reject reasons are generated when the ScopDetection finds
/// errors in the induction variable(s) of the Scop candidate.
class ReportIndVar : public RejectReason {
  //===--------------------------------------------------------------------===//
public:
  ReportIndVar(const RejectReasonKind K);
};

//===----------------------------------------------------------------------===//
/// @brief Captures a phi node that refers to SSA names in the current region.
class ReportPhiNodeRefInRegion : public ReportIndVar {
  //===--------------------------------------------------------------------===//

  // The offending instruction.
  Instruction *Inst;

public:
  ReportPhiNodeRefInRegion(Instruction *Inst)
      : ReportIndVar(rrkPhiNodeRefInRegion), Inst(Inst) {};

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkPhiNodeRefInRegion;
  }
  
  /// @name RejectReason interface
  //@{
  virtual std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures a non canonical phi node.
class ReportNonCanonicalPhiNode : public ReportIndVar {
  //===--------------------------------------------------------------------===//

  // The offending instruction.
  Instruction *Inst;

public:
  ReportNonCanonicalPhiNode(Instruction *Inst)
      : ReportIndVar(rrkNonCanonicalPhiNode), Inst(Inst) {};

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkNonCanonicalPhiNode;
  }
  
  /// @name RejectReason interface
  //@{
  virtual std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures a non canonical induction variable in the loop header.
class ReportLoopHeader : public ReportIndVar {
  //===--------------------------------------------------------------------===//

  // The offending loop.
  Loop *L;

public:
  ReportLoopHeader(Loop *L) : ReportIndVar(rrkLoopHeader), L(L) {};

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkLoopHeader;
  }
  
  /// @name RejectReason interface
  //@{
  virtual std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures a region with invalid entering edges.
class ReportIndEdge : public RejectReason {
  //===--------------------------------------------------------------------===//
public:
  ReportIndEdge();

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkIndEdge;
  }
  
  /// @name RejectReason interface
  //@{
  virtual std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures errors with non affine loop bounds.
class ReportLoopBound : public RejectReason {
  //===--------------------------------------------------------------------===//

  // The offending loop.
  Loop *L;

  // The non-affine loop bound.
  const SCEV *LoopCount;

public:
  ReportLoopBound(Loop *L, const SCEV *LoopCount);

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkLoopBound;
  }
  
  const SCEV *loopCount() { return LoopCount; }

  /// @name RejectReason interface
  //@{
  virtual std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures errors with non-side-effect-known function calls.
class ReportFuncCall : public RejectReason {
  //===--------------------------------------------------------------------===//

  // The offending call instruction.
  Instruction *Inst;

public:
  ReportFuncCall(Instruction *Inst);

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkFuncCall;
  }
  
  /// @name RejectReason interface
  //@{
  std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures errors with aliasing.
class ReportAlias : public RejectReason {
  //===--------------------------------------------------------------------===//

  /// @brief Format an invalid alias set.
  ///
  /// @param AS The invalid alias set to format.
  std::string formatInvalidAlias(AliasSet &AS) const;

public:
  ReportAlias();

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkAlias;
  }
  
  /// @name RejectReason interface
  //@{
  std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures errors with non simplified loops.
class ReportSimpleLoop : public RejectReason {
  //===--------------------------------------------------------------------===//
public:
  ReportSimpleLoop();

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkSimpleLoop;
  }
  
  /// @name RejectReason interface
  //@{
  std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Base class for otherwise ungrouped reject reasons.
class ReportOther : public RejectReason {
  //===--------------------------------------------------------------------===//
public:
  ReportOther(const RejectReasonKind K);

  /// @name RejectReason interface
  //@{
  std::string getMessage() const { return "Unknown reject reason"; }
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures errors with bad IntToPtr instructions.
class ReportIntToPtr : public ReportOther {
  //===--------------------------------------------------------------------===//

  // The offending base value.
  Value *BaseValue;

public:
  ReportIntToPtr(Value *BaseValue)
      : ReportOther(rrkIntToPtr), BaseValue(BaseValue) {};

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkIntToPtr;
  }
  
  /// @name RejectReason interface
  //@{
  std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures errors with alloca instructions.
class ReportAlloca : public ReportOther {
  //===--------------------------------------------------------------------===//
  Instruction *Inst;

public:
  ReportAlloca(Instruction *Inst) : ReportOther(rrkAlloca), Inst(Inst) {};

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkAlloca;
  }
  
  /// @name RejectReason interface
  //@{
  std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures errors with unknown instructions.
class ReportUnknownInst : public ReportOther {
  //===--------------------------------------------------------------------===//
  Instruction *Inst;

public:
  ReportUnknownInst(Instruction *Inst)
      : ReportOther(rrkUnknownInst), Inst(Inst) {};

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkUnknownInst;
  }
  
  /// @name RejectReason interface
  //@{
  std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures errors with phi nodes in exit BBs.
class ReportPHIinExit : public ReportOther {
  //===--------------------------------------------------------------------===//
public:
  ReportPHIinExit() : ReportOther(rrkPHIinExit) {};

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkPHIinExit;
  }
  
  /// @name RejectReason interface
  //@{
  std::string getMessage() const;
  //@}
};

//===----------------------------------------------------------------------===//
/// @brief Captures errors with regions containing the function entry block.
class ReportEntry : public ReportOther {
  //===--------------------------------------------------------------------===//
public:
  ReportEntry() : ReportOther(rrkEntry) {};

  static bool classof(const RejectReason *RR) {
    return RR->getKind() == rrkEntry;
  }
  
  /// @name RejectReason interface
  //@{
  std::string getMessage() const;
  //@}
};

} // namespace polly

#endif // POLLY_SCOP_DETECTION_DIAGNOSTIC_H
