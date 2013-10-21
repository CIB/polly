#define DEBUG_TYPE "polly-stat"
#include "llvm/Support/Debug.h"

#include "llvm/ADT/Statistic.h"

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

STATISTIC(UniformScops, "Number of the Scops witch are uniform");
STATISTIC(AffineScops, "Number of the Scops witch are affine");
STATISTIC(UniformMaps, "Number of the Maps witch are uniform");
STATISTIC(AffineMaps, "Number of the Maps witch are affine");
STATISTIC(NoDeps, "Number of Scops without dependencies");

class MapUniform {

public:
  int nMaps;
  std::vector<bool> p;
  MapUniform();
};

MapUniform::MapUniform() { this->nMaps = 0; }

int workOnMap(__isl_take isl_map *map, void *user);

bool ScopStatistics::runOnScop(Scop &S) {
  DEBUG(dbgs() << "Running on: " << S.getNameStr() << "\n");

  int i;
  Dependences *DE = &getAnalysis<Dependences>();
  isl_union_map *m = DE->getDependences(Dependences::TYPE_ALL);
  MapUniform *mup = new MapUniform();

  int mapCount = isl_union_map_n_map(m);
  if (!mapCount) {
    NoDeps++;
    isl_union_map_free(m);
    return false;
  }

  DEBUG(dbgs() << "Start working on union_map\n");
  isl_union_map_foreach_map(m, workOnMap, mup);

  bool isUniform = true;
  for (i = 0; i < mup->nMaps; i++) {
    isUniform = isUniform && mup->p[i];
    if (!isUniform)
      break;
  }
   
  if(isUniform)
      ++UniformScops;
  else 
      ++AffineScops;

  DEBUG(dbgs() << "Uniform output \n");
  DEBUG(dbgs() << mup->nMaps << " were found on this union_map \n");
  DEBUG(for (i = 0; i < mup->nMaps; i++) dbgs()
            << ((mup->p[i]) ? "True " : "False ");
        dbgs() << "\n";);

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

  DEBUG(dbgs() << "----------\n");
  MapUniform *mapU = (MapUniform *)user;

  DEBUG(dbgs() << "IN " << isl_map_dim(map, isl_dim_in) << "OUT "
               << isl_map_dim(map, isl_dim_out) << "\n");

  int in = isl_map_dim(map, isl_dim_in);
  int out = isl_map_dim(map, isl_dim_out);

  if (in != out) {
    mapU->p.push_back(false);
    mapU->nMaps = (mapU->nMaps) + 1;
    isl_map_free(map);
    isl_int_clear(iInt);
    return 0;
  }

  newMap = isl_map_copy(map);
  newMap = isl_map_reset_tuple_id(newMap, isl_dim_in);
  newMap = isl_map_reset_tuple_id(newMap, isl_dim_out);

  isl_set *setFdeltas = isl_map_deltas(newMap);
  j = isl_set_dim(setFdeltas, isl_dim_all);

  DEBUG(dbgs() << "isl_set_dims: " << j << "\n");
  bool isUniformDep = true;
  i = 0;
  while (isUniformDep && i < j) {
    isUniformDep =
        isUniformDep && isl_set_fast_dim_is_fixed(setFdeltas, i, &iInt);
    i++;
  }

  mapU->p.push_back(isUniformDep);
  mapU->nMaps = (mapU->nMaps) + 1;

  if (isUniformDep)
    ++UniformMaps;
  else
    ++AffineMaps;

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
                    false)
