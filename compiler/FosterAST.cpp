#include "FosterAST.h"
#include "llvm/Target/TargetSelect.h"

#include <map>
#include <vector>

using llvm::Type;

using std::vector;
using std::string;

llvm::ExecutionEngine* ee;
llvm::IRBuilder<> Builder(getGlobalContext());
llvm::Module* TheModule;
std::map<string, const llvm::Type*> NamedTypes;

std::ostream& operator<<(std::ostream& out, ExprAST& expr) {
  return expr.operator<<(out);
}

/** Macros in TargetSelect.h conflict with those from ANTLR... */
void fosterLLVMInitializeNativeTarget() {
  llvm::InitializeNativeTarget();
}

Value* ErrorV(const char* Str) {
  fprintf(stderr, "%s\n", Str);
  return NULL;
}

const Type* LLVMType_from(string s) {
  std::clog << "Getting LLVM type for " << s << std::endl;
  if (NamedTypes[s]) return NamedTypes[s];
  fprintf(stderr, "Unknown type in LLVMType_from(%s)\n", s.c_str());
  return NULL;
}

Value* IntAST::Codegen() {
  return llvm::ConstantInt::get(Type::getInt32Ty(getGlobalContext()),
                                    llvm::APInt(32u, Clean, Base));
}

Value* BinaryExprAST::Codegen() {
  Value* VL = LHS->Codegen();
  Value* VR = RHS->Codegen();
  if (!VL || !VR) return NULL;

  if (Op == "+") { return Builder.CreateAdd(VL, VR, "addtmp"); }
  if (Op == "-") { return Builder.CreateSub(VL, VR, "subtmp"); }
  if (Op == "/") { return Builder.CreateSDiv(VL, VR, "divtmp"); }
  if (Op == "*") { return Builder.CreateMul(VL, VR, "multmp"); }

  std::cerr << "Couldn't gen code for op " << Op << endl;
  return NULL;
}

llvm::Function* PrototypeAST::Codegen() {
  // Make the function type: int(int, ..., int) for now
  const llvm::IntegerType* i32_t = Type::getInt32Ty(getGlobalContext());
  vector<const Type*> Ints(Args.size(), i32_t);
  llvm::FunctionType* FT = llvm::FunctionType::get(i32_t, Ints, false);

  llvm::Function* F = llvm::Function::Create(FT, llvm::Function::ExternalLinkage, Name, TheModule);

  if (!F) {
    std::cout << "Function creation failed!" << std::endl;
    return NULL;
  }

  // If F conflicted, there was already something named "Name"
  if (F->getName() != Name) {
    std::cout << "Error: redefinition of function " << Name << std::endl;
    return NULL;
  }

  // Set names for all arguments
  llvm::Function::arg_iterator AI = F->arg_begin();
  for (int i = 0; i != Args.size(); ++i, ++AI) {
    AI->setName(Args[i]);
    //NamedValues[Args[i]] = AI;
  }

  return F;
}

#define DEFAULT_ADDRESS_SPACE 0u
llvm::Function* FnAST::Codegen() {
  //NamedValues.clear();
  llvm::Function* F = Proto->Codegen();
  if (!F) return F;

  llvm::BasicBlock* BB = llvm::BasicBlock::Create(getGlobalContext(), "entry", F);
  Builder.SetInsertPoint(BB);

  Value* RetVal = Body->Codegen(); // TODO
  if (RetVal) {
    Builder.CreateRet(RetVal);
    //llvm::verifyFunction(*F);
    return F;
  } else {
    F->eraseFromParent();
    std::cout << "Function retval creation failed" << std::endl;
    return NULL;
  }
}


