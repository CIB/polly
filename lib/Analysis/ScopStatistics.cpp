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

struct mapSave {
  unsigned nparam;
} s;

int workOnMap(__isl_take isl_map *map, void *user);

bool ScopStatistics::runOnScop(Scop &S) {
    outs() << "<<>>>>>>>>>"  << S.getNameStr() << "\n";
    Dependences *DE = &getAnalysis<Dependences>();
    isl_union_map *m = DE->getDependences(Dependences::TYPE_ALL); 
    outs() << "Map dump: "; isl_union_map_dump(m);

    isl_union_map_foreach_map(m, workOnMap, &s);

    outs() << "\n ----------------- \n";

    outs() << "Some nParam: " << s.nparam;
    
    return false;
  }

  void ScopStatistics::getAnalysisUsage(AnalysisUsage &AU) const {
    //AU.addRequired<AliasAnalysis>();
    AU.addRequired<Dependences>();
    AU.addRequired<ScopInfo>();
    AU.setPreservesAll();
  }

  int workOnMap(__isl_take isl_map *map, void *user) {
    mapSave* mapS = (mapSave*) user;
    mapS->nparam = isl_map_n_param(map);

    return 0;
  }

  char ScopStatistics::ID = 0;

  Pass *polly::createScopStatisticsPass() {return new ScopStatistics(); }

  INITIALIZE_PASS_BEGIN(ScopStatistics, "polly-stat","Polly - get stats", false, false);
  INITIALIZE_PASS_END(ScopStatistics, "polly-stat","Polly - get stats", false, false);
