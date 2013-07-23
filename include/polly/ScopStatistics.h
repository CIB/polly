#ifndef POLLY_SCOP_SCOPSTATISTICS_H
#define POLLY_SCOP_SCOPSTATISTICS_H

#include "polly/ScopPass.h"

using namespace llvm;
namespace polly {
class Scop;

class ScopStatistics : public ScopPass {
public:
  static char ID;
  //Scop *S;
  explicit ScopStatistics() : ScopPass(ID) {}
protected:

  virtual bool runOnScop(Scop &S);

  virtual void getAnalysisUsage(AnalysisUsage &AU) const;
//public:
  //Scop &getCurScop() const {
    //assert(S && "Not on a Scop!");
    //return *S;
  //}
};

}
namespace llvm {
  class PassRegistry;
  void initializeScopStatisticsPass(llvm::PassRegistry &);
}
#endif
