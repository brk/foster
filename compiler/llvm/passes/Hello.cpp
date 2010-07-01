// Example "Hello World" LLVM pass from
// http://llvm.org/docs/WritingAnLLVMPass.html

#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace {
struct Hello : public FunctionPass {
  static char ID;
  Hello() : FunctionPass(&ID) {}

  virtual bool runOnFunction(Function& F) {
    outs() << "Hello: " << F.getName() << "\n";
    return false;
  }
};

char Hello::ID = 0;
RegisterPass<Hello> X("hello", "Prints a list of function names");
}
