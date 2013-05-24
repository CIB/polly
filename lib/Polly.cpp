//===------ Polly.cpp - Add the Polly Passes to default passes  -----------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Add the Polly passes to the optimization passes executed at -O3.
//
//===----------------------------------------------------------------------===//
#include "polly/RegisterPasses.h"
#include "polly/LinkAllPasses.h"

#include "llvm/Support/raw_ostream.h"

#include "llvm/PassManager.h"
#include "llvm/PassRegistry.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;

/// @brief Initialize Polly passes when library is loaded.
///
/// We use the constructor of a statically declared object to initialize the
/// different Polly passes right after the Polly library is loaded. This ensures
/// that the Polly passes are available e.g. in the 'opt' tool.
class StaticInitializer {
public:
  StaticInitializer() {
    PassRegistry &Registry = *PassRegistry::getPassRegistry();
    polly::initializePollyPasses(Registry);
  }
};
static StaticInitializer InitializeEverything;

extern bool PollyEnabled;
extern bool ImportJScop;
extern bool ExportJScop;
extern bool PollyViewer;
extern bool PollyOnlyViewer;
extern bool PollyPrinter;
extern bool PollyOnlyPrinter;

static
void registerPollyEarlyAsPossiblePasses(const llvm::PassManagerBuilder &Builder,
                                        llvm::PassManagerBase &PM) {

  if (Builder.OptLevel == 0)
    return;

  if (PollyOnlyPrinter || PollyPrinter || PollyOnlyViewer || PollyViewer ||
      ExportJScop || ImportJScop)
    PollyEnabled = true;

  if (!PollyEnabled)
    return;

  // Polly is only enabled at -O3
  if (Builder.OptLevel != 3) {
    errs() << "Polly should only be run with -O3. Disabling Polly.\n";
    return;
  }

  polly::registerPollyPasses(PM);
}

static void registerPollyOptLevel0Passes(const llvm::PassManagerBuilder &,
                                         llvm::PassManagerBase &PM) {
  polly::registerCanonicalicationPasses(PM);
}


// Execute Polly together with a set of preparing passes.
//
// We run Polly that early to run before loop optimizer passes like LICM or
// the LoopIdomPass. Both transform the code in a way that Polly will recognize
// less scops.

static llvm::RegisterStandardPasses
PassRegister(llvm::PassManagerBuilder::EP_EarlyAsPossible,
             registerPollyEarlyAsPossiblePasses);
static llvm::RegisterStandardPasses
PassRegisterPreopt(llvm::PassManagerBuilder::EP_EnabledOnOptLevel0,
                  registerPollyOptLevel0Passes);
