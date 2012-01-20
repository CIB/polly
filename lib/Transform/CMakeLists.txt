if (SCOPLIB_FOUND)
  set(POLLY_SCOPLIB_FILES Pocc.cpp)
endif (SCOPLIB_FOUND)

if (PLUTO_FOUND)
  set(POLLY_PLUTO_FILES Pluto.cpp)
endif (PLUTO_FOUND)

add_polly_library(PollyTransform
  DeadCodeElimination.cpp
  IndependentBlocks.cpp
  IndVarSimplify.cpp
  MayAliasSet.cpp
  ScheduleOptimizer.cpp
  ${POLLY_SCOPLIB_FILES}
  ${POLLY_PLUTO_FILES}
)

add_dependencies(PollyTransform
  PollyCodeGen
)
