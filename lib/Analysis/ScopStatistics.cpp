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
#include <vector>

using namespace llvm;
using namespace polly;

struct mapSave {
  unsigned nparam;
} s;

class MapUniform {

public:
  int nMaps;
  std::vector<bool> p;
  MapUniform();
};

MapUniform::MapUniform() {
  this->nMaps = 0;
}

int workOnMap(__isl_take isl_map *map, void *user);

bool output;

bool ScopStatistics::runOnScop(Scop &S) {
  // set output to true for debug info
  output = false;

  Dependences *DE = &getAnalysis<Dependences>();
  isl_union_map *m = DE->getDependences(Dependences::TYPE_ALL);
  int i;
  MapUniform *mup = new MapUniform();
  
  if(output)
    outs() << "Start working on union_map\n";
  isl_union_map_foreach_map(m, workOnMap, mup);

  if(output) {
    outs() << "Uniform output \n";
    outs() << mup->nMaps << " were found on this union_map \n";
    for (i = 0; i < mup->nMaps; i++) {
      if (mup->p[i] == true) {
        outs() << "True ";
      } else {
        outs() << "False ";
      }
    }
    outs() << "\n";
  }

  isl_union_map_free(m);
  return false;
}

void ScopStatistics::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<Dependences>();
  AU.addRequired<ScopInfo>();
  AU.setPreservesAll();
}

int workOnMap(__isl_take isl_map *map, void *user) {
  unsigned i, j;
  isl_int iInt;
  isl_map *newMap;
  isl_int_init(iInt);

  if(output)
    outs() << "----------\n";
  MapUniform *mapU = (MapUniform *)user;

  if(output)
    outs() << "IN " << isl_map_dim(map, isl_dim_in) << "OUT "
         << isl_map_dim(map, isl_dim_out) << "\n";

  int in = isl_map_dim(map, isl_dim_in);
  int out = isl_map_dim(map, isl_dim_out);

  if (in != out) {
    mapU->p.push_back(false);
    mapU->nMaps = (mapU->nMaps++);
    isl_map_free(map);
    isl_int_clear(iInt);
    return 0;
  }

  newMap = isl_map_copy(map);
  newMap = isl_map_reset_tuple_id(newMap, isl_dim_in);
  newMap = isl_map_reset_tuple_id(newMap, isl_dim_out);

  isl_set *setFdeltas = isl_map_deltas(newMap);
  j = isl_set_dim(setFdeltas, isl_dim_all);

  if(output)
    outs() << "isl_set_dims: " << j << "\n";
  for (i = 0; i < j; i++) {
    if (!isl_set_fast_dim_is_fixed(setFdeltas, i, &iInt)) {
      mapU->p.push_back(false);
      mapU->nMaps = (mapU->nMaps++);
      isl_map_free(map);
      isl_set_free(setFdeltas);
      isl_int_clear(iInt);
      return 0;
    }
    if(output)
      outs() << "constant dim: " << i  << "\n";
  }
  mapU->p.push_back(true);
  mapU->nMaps = (mapU->nMaps++);

  isl_map_free(map);
  isl_set_free(setFdeltas);
  isl_int_clear(iInt);
  return 0;
}

char ScopStatistics::ID = 0;

Pass *polly::createScopStatisticsPass() { return new ScopStatistics(); }

INITIALIZE_PASS_BEGIN(ScopStatistics, "polly-stat", "Polly - get stats", false,
                      false);
INITIALIZE_PASS_END(ScopStatistics, "polly-stat", "Polly - get stats", false,
                    false);
