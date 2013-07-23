#define DEBUG_TYPE "polly-stat"

#include "llvm/Support/Debug.h"
#include "polly/ScopStatistics.h"
#include "polly/ScopPass.h"
#include "polly/ScopInfo.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "polly/LinkAllPasses.h"
#include "polly/Dependences.h"
#include "isl/map.h"

using namespace llvm;
using namespace polly;

bool ScopStatistics::runOnScop(Scop &S) {
  outs() << ">>>>>>>>>"  << S.getNameStr() << "\n";
  Dependences *DE = &getAnalysis<Dependences>();
  isl_union_map *m = DE->getDependences(Dependences::TYPE_ALL); 
  
  return false;
}

void ScopStatistics::getAnalysisUsage(AnalysisUsage &AU) const {
  //AU.addRequired<AliasAnalysis>();
  AU.addRequired<Dependences>();
  AU.addRequired<ScopInfo>();
  AU.setPreservesAll();
}

char ScopStatistics::ID = 0;

Pass *polly::createScopStatisticsPass() {return new ScopStatistics(); }

INITIALIZE_PASS_BEGIN(ScopStatistics, "polly-stat","Polly - get stats", false, false);
INITIALIZE_PASS_END(ScopStatistics, "polly-stat","Polly - get stats", false, false);
