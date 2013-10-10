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
  //this->p = bp;
}

int workOnMap(__isl_take isl_map *map, void *user);
int testOnMap(__isl_take isl_map *map, void *user);

bool ScopStatistics::runOnScop(Scop &S) {
    outs() << ">>>>>>>>> Run on Scop: "  << S.getNameStr() << "\n";
    Dependences *DE = &getAnalysis<Dependences>();
    isl_union_map *m = DE->getDependences(Dependences::TYPE_ALL); 
    int i;
    outs() << "Map dump:\n"; isl_union_map_dump(m);
    //isl_union_map_n_ stuff
    //int j = isl_union_map_n_map(m);
    //bool* p = (bool *) malloc(j*sizeof(bool));//10 to replace with number of maps
    MapUniform* mup = new MapUniform();

    isl_union_map_foreach_map(m, workOnMap, &mup);

    outs() << "\n ----------------- \n";
    outs() << "Some nParam: " << s.nparam << "\n";
   
    outs() << "\n ----------------- \n";
    outs() << "uniform output \n";
    outs() << mup->nMaps << "were found \n";
    for(i = 0;i < mup->nMaps; i++){
      if(mup->p[i] == true) {
        outs() << "true ";
      } else {
        outs() << "false ";
      }
    }
    outs() << "\n";

    return false;
  }

  void ScopStatistics::getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<Dependences>();
    AU.addRequired<ScopInfo>();
    AU.setPreservesAll();
  }

  int workOnMap(__isl_take isl_map *map, void *user) {
    unsigned i,j;
    isl_int iInt;
    
    isl_int_init(iInt);

    MapUniform* mapU = (MapUniform *) user;


    outs() << "IN " << isl_map_dim(map,isl_dim_in) << "OUT " << isl_map_dim(map,isl_dim_out) << "\n";

    int in = isl_map_dim(map,isl_dim_in);
    int out = isl_map_dim(map,isl_dim_out); 

    if(in != out) {
      mapU->p.push_back(false);
      mapU->nMaps++;
      return 0; 
    }

    //isl_set* setFmap = isl_set_from_map(map);
    isl_set* setFdeltas = isl_map_deltas(map);
    //isl_dim* dimFdeltas = isl_set_get_dim(setFdeltas);  

    // anzahl der dims 

    //dim type dim out dim_all
    j = isl_set_dim(setFdeltas, isl_dim_all);

    for(i = 0;i < j;i++) {
      //isl_set_fast_dim_is_fixed(setFdeltas, 0, iInt);
      isl_int_set_si(iInt,i);
      if(!isl_set_fast_dim_is_fixed(setFdeltas, isl_dim_all, &iInt)) {
        mapU->p.push_back(false);
        mapU->nMaps++;
        return 0;      
      }
    }
    mapU->p.push_back(true);
    mapU->nMaps++;

    //isl_set_plain_is_fixed(setFdeltas,isl_dim_type,0,iInt);
    isl_int_clear(iInt);
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
