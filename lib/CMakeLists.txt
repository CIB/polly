add_subdirectory(Analysis)
add_subdirectory(CodeGen)
add_subdirectory(Exchange)
add_subdirectory(Support)
add_subdirectory(JSON)
add_subdirectory(Transform)

set(MODULE TRUE)
set(LLVM_NO_RTTI 1)

set(LLVM_USED_LIBS
  PollyAnalysis
  PollyCodeGen
  PollyExchange
  PollySupport
  PollyJSON
  PollyTransform
  )

add_polly_loadable_module(LLVMPolly
  RegisterPasses.cpp
  )

if (TARGET intrinsics_gen)
  # Check if we are building as part of an LLVM build
  add_dependencies(LLVMPolly intrinsics_gen)
endif()

add_dependencies(LLVMPolly
  PollyAnalysis
  PollyCodeGen
  PollyExchange
  PollySupport
  PollyJSON
  PollyTransform
  )

set_target_properties(LLVMPolly
  PROPERTIES
  LINKER_LANGUAGE CXX
  PREFIX "")

if (PLUTO_FOUND)
  target_link_libraries(LLVMPolly ${PLUTO_LIBRARY})
endif(PLUTO_FOUND)
