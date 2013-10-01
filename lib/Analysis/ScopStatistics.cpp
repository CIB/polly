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

class MapUniform {

public:
  int nMaps;
  bool* p;
  MapUniform(bool* bp);
};

MapUniform::MapUniform(bool* bp) {
  this->nMaps = 0;
  this->p = bp;
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
    bool* p = (bool *) malloc(10*sizeof(bool));//10 to replace with number of maps
    MapUniform* mup = new MapUniform(p);
    //mu.nMaps = 0;
    

    //isl_union_map_foreach_map(m, workOnMap, &mu);
    isl_union_map_foreach_map(m, testOnMap, &s);

    outs() << "\n ----------------- \n";
    outs() << "Some nParam: " << s.nparam << "\n";
   
    outs() << "\n ----------------- \n";
    outs() << "uniform output \n";
    outs() << mup->nMaps << "were found \n";
    for(i = 0,i < mup->nMaps; i++){
      if(mup->p[i] == true) {
        outs() << "true ";
      } else {
        outs() << "false ";
      }
    }
    outs() << "\n";

    outs() << "End of my output \n";
    


    //set prints to check output
    return false;
  }

  void ScopStatistics::getAnalysisUsage(AnalysisUsage &AU) const {
    //AU.addRequired<AliasAnalysis>();
    AU.addRequired<Dependences>();
    AU.addRequired<ScopInfo>();
    AU.setPreservesAll();
  }

  int workOnMap(__isl_take isl_map *map, void *user) {
    int i;
    bool earlyStop = false;
    isl_int iInt;
    
    isl_int_init(iInt);

    MapUniform* mapU = (MapUniform *) user;
    //isl_set* setFmap = isl_set_from_map(map);
    isl_set* setFdeltas = isl_map_deltas(map);
    //isl_dim* dimFdeltas = isl_set_get_dim(setFdeltas);  

    // anzahl der dims 

//dim type dim out dim_all

    // warscheinlich i isl_int 
    // isl_int_set_si(iInt,0) , () , isl_int_add_ui(iInt,1)
    for(i = 0;i < 10;i++) {
      //isl_set_fast_dim_is_fixed(setFdeltas, 0, iInt);
      // return bool/int 
      // isl_int_set_si(iInt,1);
      if(isl_set_fast_dim_is_fixed(setFdeltas, isl_dim_all, &iInt) == 0) {
        mapU->p[mapU->nMaps] = false;
        mapU->nMaps++;
        earlyStop = true;
        break;      
      }
    }
    if(!earlyStop) {
      mapU->p[mapU->nMaps] = true;
      mapU->nMaps++;
    }

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
