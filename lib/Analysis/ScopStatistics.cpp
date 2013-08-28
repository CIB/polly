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
#include "isl/set.h"

using namespace llvm;
using namespace polly;

struct mapSave {
  unsigned nparam;
} s;
// later change to class and add constructor 
struct mapUniform {
  int nMaps;
  bool *p;
} mu;

// struct next
// islmap *depi
// enum

int workOnMap(__isl_take isl_map *map, void *user);
int testOnMap(__isl_take isl_map *map, void *user);

bool ScopStatistics::runOnScop(Scop &S) {
    outs() << ">>>>>>>>> Run on Scop: "  << S.getNameStr() << "\n";
    Dependences *DE = &getAnalysis<Dependences>();
    isl_union_map *m = DE->getDependences(Dependences::TYPE_ALL); 
    outs() << "Map dump:\n"; isl_union_map_dump(m);
    //mu.nMaps = 0;
    //mu.p = (bool *) malloc(10*sizeof(bool));//10 to replace with number of maps

    //isl_union_map_foreach_map(m, workOnMap, &mu);
    isl_union_map_foreach_map(m, testOnMap, &s);

    outs() << "\n ----------------- \n";

    outs() << "Some nParam: " << s.nparam << "\n";
    
    outs() << "End of my output \n";
    
    return false;
  }

  void ScopStatistics::getAnalysisUsage(AnalysisUsage &AU) const {
    //AU.addRequired<AliasAnalysis>();
    AU.addRequired<Dependences>();
    AU.addRequired<ScopInfo>();
    AU.setPreservesAll();
  }

  int workOnMap(__isl_take isl_map *map, void *user) {
    mapUniform* mapU = (mapUniform *) user;
    (mapU->nMaps)++;
    isl_set* setFmap = isl_set_from_map(map);
    isl_set* setFdeltas = isl_map_deltas(map);
    isl_dim* dimFdeltas = isl_set_get_dim(setFdeltas);  
    isl_int* iInt;
    isl_set_fast_dim_is_fixed(setFmap, dimFdeltas, iInt);

    return 0;
  }

  int testOnMap(__isl_take isl_map *map, void *user) {
    mapSave* mapS = (mapSave*) user;
    mapS->nparam = isl_map_n_param(map);
    
  
    return 0;
  }

  char ScopStatistics::ID = 0;

  Pass *polly::createScopStatisticsPass() {return new ScopStatistics(); }

  INITIALIZE_PASS_BEGIN(ScopStatistics, "polly-stat","Polly - get stats", false, false);
  INITIALIZE_PASS_END(ScopStatistics, "polly-stat","Polly - get stats", false, false);
