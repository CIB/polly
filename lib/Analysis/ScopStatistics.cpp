//#include "/home/vulder/llvmtest/llvm/tools/polly/nclude/polly/ScopStatistics.h"
#define DEBUG_TYPE "polly-stat"

#include "llvm/Support/Debug.h"
#include "polly/ScopStatistics.h"
#include "polly/ScopPass.h"
#include "polly/ScopInfo.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "polly/LinkAllPasses.h"


using namespace llvm;
using namespace polly;

bool ScopStatistics::runOnScop(Scop &S) {
  outs() << ">>>>>>>>>"  << S.getNameStr() << "\n";
  outs() << "Your mom";
  return false;
}

void ScopStatistics::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<ScopInfo>();
  AU.setPreservesAll();
}

char ScopStatistics::ID = 0;

Pass *polly::createScopStatisticsPass() {return new ScopStatistics(); }

INITIALIZE_PASS_BEGIN(ScopStatistics, "polly-stat","Polly - get stats", false, false);
INITIALIZE_PASS_END(ScopStatistics, "polly-stat","Polly - get stats", false, false);
