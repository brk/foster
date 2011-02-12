// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/LLVMUtils.h"

#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/ExprASTVisitor.h"
#include "parse/ParsingContext.h"
#include "parse/ANTLRtoFosterAST.h" // just for parseAPIntFromClean()
#include "parse/FosterUtils.h"
#include "parse/DumpStructure.h"

#include "passes/PrettyPrintPass.h"

#include "llvm/DerivedTypes.h"
#include "llvm/Constants.h"
#include "llvm/Support/raw_os_ostream.h"

#include <map>
#include <vector>
#include <sstream>

using foster::EDiag;
using foster::show;
using foster::currentErrs;
using foster::SourceRange;
using foster::SourceRangeHighlighter;
using foster::SourceLocation;

using llvm::Type;
using llvm::BasicBlock;
using llvm::Function;
using llvm::getGlobalContext;
using llvm::FunctionType;
using llvm::IntegerType;
using llvm::Value;
using llvm::ConstantInt;

using std::vector;
using std::string;


std::ostream& operator<<(std::ostream& out, const TypeAST& type) {
  llvm::raw_os_ostream rout(out);
  foster::prettyPrintType(&type, rout, 40);
  return out;
}

std::ostream& operator<<(std::ostream& out, const ExprAST& expr) {
  return expr.operator<<(out);
}


string str(const ExprAST* expr) {
  if (expr) {
    std::stringstream ss; ss << (*expr); return ss.str();
  } else { return "<nil>"; }
}

string str(const TypeAST* expr) {
  if (expr) {
    std::stringstream ss; ss << (*expr); return ss.str();
  } else { return "<nil>"; }
}

bool isPrintRef(const ExprAST* base) {
  if (const VariableAST* var = dynamic_cast<const VariableAST*>(base)) {
    if (var->name == "print_ref") {
      return true;
    }
  }
  return false;
}

namespace foster {

SourceRangeHighlighter show(ExprAST* ast) {
  if (!ast) {
    SourceLocation empty = SourceLocation::getInvalidLocation();
    return SourceRangeHighlighter(SourceRange(NULL, empty, empty, NULL), empty);
  }
  return show(ast->sourceRange);
}

char kDefaultFnLiteralCallingConvention[] = "fastcc";

} // namespace foster

void ExprASTVisitor::visitChildren(ExprAST* ast) {
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    if (ast->parts[i]) {
      this->onVisitChild(ast, ast->parts[i]);
    } else {
      EDiag() << "visitChildren saw null part " << i << " for ast node " << str(ast) << show(ast);
    }
  }
}

void ExprASTVisitor::onVisitChild(ExprAST* ast, ExprAST* child) {
  child->accept(this);
}

////////////////////////////////////////////////////////////////////


IntAST::IntAST(int activeBits,
                const string& originalText,
                const string& cleanText, int base,
                foster::SourceRange sourceRange)
        : ExprAST("IntAST", sourceRange), text(originalText), base(base) {
  // Debug builds of LLVM don't ignore leading zeroes when considering
  // needed bit widths.
  int bitsLLVMneeds = (std::max)(intSizeForNBits(activeBits),
                                 (unsigned) cleanText.size());
  int ourSize = intSizeForNBits(bitsLLVMneeds);
  apint = new APInt(ourSize, cleanText, base);
  type = TypeAST::i(ourSize);
}

unsigned IntAST::intSizeForNBits(unsigned n) const {
  // Disabled until we get better inferred literal types
  //if (n <= 1) return 1;
  //if (n <= 8) return 8;
  //if (n <= 16) return 16;
  if (n <= 32) return 32;
  if (n <= 64) return 64;
  ASSERT(false) << "Support for arbitrary-precision ints not yet implemented.";
  return 0;
}


IntAST* literalIntAST(int lit, const foster::SourceRange& sourceRange) {
  std::stringstream ss; ss << lit;
  string text = ss.str();

  APInt* p = foster::parseAPIntFromClean(text, 10, sourceRange);
  IntAST* rv = new IntAST(p->getActiveBits(), text, text, 10, sourceRange);
  return rv;
}

const llvm::APInt& IntAST::getAPInt() const { return *apint; }
std::string IntAST::getOriginalText() const { return text; }


llvm::ConstantInt* getConstantInt(IntAST* n) {
  ASSERT(n->type && n->type->getLLVMType());

  llvm::Constant* c = ConstantInt::get(n->type->getLLVMType(), n->getAPInt());
  return llvm::dyn_cast<ConstantInt>(c);
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

PrototypeAST::PrototypeAST(TypeAST* retTy, const string& name,
             const std::vector<VariableAST*>& inArgs,
             foster::SourceRange sourceRange)
    : ExprAST("PrototypeAST", sourceRange),
      name(name), inArgs(inArgs), resultTy(retTy) {
        ASSERT(resultTy != NULL) << "proto: " << name << foster::show(sourceRange);
}


////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

std::ostream& ExprAST::operator<<(std::ostream& out) const {
  llvm::raw_os_ostream raw(out);
  foster::dumpExprStructure(raw, this);
}

std::ostream& NamedTypeDeclAST::operator<<(std::ostream& out) const {
  return out << "type " << name << " = " << str(type) << "\n";
}

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

void          BoolAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void           IntAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void            FnAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void      VariableAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void        IfExprAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void       NilExprAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void     PrototypeAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void        ModuleAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void          CallAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void      ETypeAppAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void NamedTypeDeclAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void BuiltinCompilesExprAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }

void          SeqAST::accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
void    SubscriptAST::accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
void    TupleExprAST::accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
