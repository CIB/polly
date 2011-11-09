
#include "polly/Support/SCEVValidator.h"

#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/RegionInfo.h"

#include <vector>

using namespace llvm;

namespace SCEVType {
  enum TYPE {INT, PARAM, IV, INVALID};
}

struct ValidatorResult {
  SCEVType::TYPE type;
  std::vector<const SCEV*> Parameters;

  ValidatorResult() : type(SCEVType::INVALID) {};

  ValidatorResult(const ValidatorResult &vres) {
    type = vres.type;
    Parameters = vres.Parameters;
  };

  ValidatorResult(SCEVType::TYPE type) : type(type) {};
  ValidatorResult(SCEVType::TYPE type, const SCEV* Expr) : type(type) {
    Parameters.push_back(Expr);
  };

  bool isConstant() {
    return type == SCEVType::INT || type == SCEVType::PARAM;
  }

  bool isValid() {
    return type != SCEVType::INVALID;
  }

  bool isIV() {
    return type == SCEVType::IV;
  }

  bool isINT() {
    return type == SCEVType::INT;
  }

  void addParamsFrom(struct ValidatorResult &Source) {
    Parameters.insert(Parameters.end(), Source.Parameters.begin(),
                      Source.Parameters.end());
  }
};

/// Check if a SCEV is valid in a SCoP.
struct SCEVValidator
  : public SCEVVisitor<SCEVValidator, struct ValidatorResult> {
private:
  const Region *R;
  ScalarEvolution &SE;
  Value **BaseAddress;

public:
  SCEVValidator(const Region *R, ScalarEvolution &SE,
                Value **BaseAddress) : R(R), SE(SE),
    BaseAddress(BaseAddress) {};

  struct ValidatorResult visitConstant(const SCEVConstant *Constant) {
    return ValidatorResult(SCEVType::INT);
  }

  struct ValidatorResult visitTruncateExpr(const SCEVTruncateExpr* Expr) {
    ValidatorResult Op = visit(Expr->getOperand());

    // We currently do not represent a truncate expression as an affine
    // expression. If it is constant during Scop execution, we treat it as a
    // parameter, otherwise we bail out.
    if (Op.isConstant())
      return ValidatorResult(SCEVType::PARAM, Expr);

    return ValidatorResult (SCEVType::INVALID);
  }

  struct ValidatorResult visitZeroExtendExpr(const SCEVZeroExtendExpr * Expr) {
    ValidatorResult Op = visit(Expr->getOperand());

    // We currently do not represent a zero extend expression as an affine
    // expression. If it is constant during Scop execution, we treat it as a
    // parameter, otherwise we bail out.
    if (Op.isConstant())
      return ValidatorResult (SCEVType::PARAM, Expr);

    return ValidatorResult(SCEVType::INVALID);
  }

  struct ValidatorResult visitSignExtendExpr(const SCEVSignExtendExpr* Expr) {
    // We currently allow only signed SCEV expressions. In the case of a
    // signed value, a sign extend is a noop.
    //
    // TODO: Reconsider this when we add support for unsigned values.
    return visit(Expr->getOperand());
  }

  struct ValidatorResult visitAddExpr(const SCEVAddExpr* Expr) {
    ValidatorResult Return(SCEVType::INT);

    for (int i = 0, e = Expr->getNumOperands(); i < e; ++i) {
      ValidatorResult Op = visit(Expr->getOperand(i));

      if (!Op.isValid())
        return ValidatorResult(SCEVType::INVALID);

      Return.type = std::max(Return.type, Op.type);
      Return.addParamsFrom(Op);
    }

    // TODO: Check for NSW and NUW.
    return Return;
  }

  struct ValidatorResult visitMulExpr(const SCEVMulExpr* Expr) {
    ValidatorResult Return(SCEVType::INT);

    for (int i = 0, e = Expr->getNumOperands(); i < e; ++i) {
      ValidatorResult Op = visit(Expr->getOperand(i));

      if (Op.type == SCEVType::INT)
        continue;

      if (Op.type == SCEVType::INVALID || Return.type != SCEVType::INT)
        return ValidatorResult(SCEVType::INVALID);

      Return.type = Op.type;
      Return.addParamsFrom(Op);
    }

    // TODO: Check for NSW and NUW.
    return Return;
  }

  struct ValidatorResult visitUDivExpr(const SCEVUDivExpr* Expr) {
    ValidatorResult LHS = visit(Expr->getLHS());
    ValidatorResult RHS = visit(Expr->getRHS());

    // We currently do not represent a unsigned devision as an affine
    // expression. If the division is constant during Scop execution we treat it
    // as a parameter, otherwise we bail out.
    if (LHS.isConstant() && RHS.isConstant())
      return ValidatorResult(SCEVType::PARAM, Expr);

    return ValidatorResult(SCEVType::INVALID);
  }

  struct ValidatorResult visitAddRecExpr(const SCEVAddRecExpr* Expr) {
    if (!Expr->isAffine())
      return ValidatorResult(SCEVType::INVALID);

    ValidatorResult Start = visit(Expr->getStart());
    ValidatorResult Recurrence = visit(Expr->getStepRecurrence(SE));

    if (!Start.isValid() || !Recurrence.isValid() || Recurrence.isIV())
      return ValidatorResult(SCEVType::INVALID);


    if (!R->contains(Expr->getLoop())) {
      if (Start.isIV())
        return ValidatorResult(SCEVType::INVALID);
      else
        return ValidatorResult(SCEVType::PARAM, Expr);
    }

    if (!Recurrence.isINT())
      return ValidatorResult(SCEVType::INVALID);

    ValidatorResult Result(SCEVType::IV);
    Result.addParamsFrom(Start);
    return Result;
  }

  struct ValidatorResult visitSMaxExpr(const SCEVSMaxExpr* Expr) {
    ValidatorResult Return(SCEVType::INT);

    for (int i = 0, e = Expr->getNumOperands(); i < e; ++i) {
      ValidatorResult Op = visit(Expr->getOperand(i));

      if (!Op.isValid())
        return ValidatorResult(SCEVType::INVALID);

      Return.type = std::max(Return.type, Op.type);
      Return.addParamsFrom(Op);
    }

    return Return;
  }

  struct ValidatorResult visitUMaxExpr(const SCEVUMaxExpr* Expr) {
    ValidatorResult Return(SCEVType::PARAM);

    // We do not support unsigned operations. If 'Expr' is constant during Scop
    // execution we treat this as a parameter, otherwise we bail out.
    for (int i = 0, e = Expr->getNumOperands(); i < e; ++i) {
      ValidatorResult Op = visit(Expr->getOperand(i));

      if (!Op.isConstant())
        return ValidatorResult(SCEVType::INVALID);

      Return.addParamsFrom(Op);
    }

    return Return;
  }

  ValidatorResult visitUnknown(const SCEVUnknown* Expr) {
    Value *V = Expr->getValue();

    if (isa<UndefValue>(V))
      return ValidatorResult(SCEVType::INVALID);

    if (BaseAddress) {
      if (*BaseAddress)
        return ValidatorResult(SCEVType::INVALID);
      else
        *BaseAddress = V;
    }

    if (Instruction *I = dyn_cast<Instruction>(Expr->getValue()))
      if (R->contains(I))
        return ValidatorResult(SCEVType::INVALID);

    if (BaseAddress)
      return ValidatorResult(SCEVType::PARAM);
    else
      return ValidatorResult(SCEVType::PARAM, Expr);
  }
};

namespace polly {
  bool isAffineExpr(const Region *R, const SCEV *Expr, ScalarEvolution &SE,
                    Value **BaseAddress) {
    if (isa<SCEVCouldNotCompute>(Expr))
      return false;

    if (BaseAddress)
      *BaseAddress = NULL;

    SCEVValidator Validator(R, SE, BaseAddress);
    ValidatorResult Result = Validator.visit(Expr);

    return Result.isValid();
  }

  std::vector<const SCEV*> getParamsInAffineExpr(const Region *R,
                                                 const SCEV *Expr,
                                                 ScalarEvolution &SE,
                                                 Value **BaseAddress) {
    if (isa<SCEVCouldNotCompute>(Expr))
      return std::vector<const SCEV*>();

    if (BaseAddress)
      *BaseAddress = NULL;

    SCEVValidator Validator(R, SE, BaseAddress);
    ValidatorResult Result = Validator.visit(Expr);

    return Result.Parameters;
  }
}

