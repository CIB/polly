add_polly_library(PollyExchange
  JSONExporter.cpp
  OpenScopExporter.cpp
  OpenScopImporter.cpp
  ScopLib.cpp
  ScopLibExporter.cpp
  ScopLibImporter.cpp
)

add_dependencies(PollyExchange
  PollyJSON
)

target_link_libraries(PollyExchange PollyJSON)
