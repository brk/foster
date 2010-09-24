// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"

#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/ExprASTVisitor.h"
#include "parse/CompilationContext.h"
#include "parse/ANTLRtoFosterAST.h" // just for parseAPIntFromClean()
#include "parse/FosterUtils.h"

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

uint64_t getSaturating(llvm::Value* v) {
  typedef uint64_t T;
  // If the value requires more bits than T can represent, we want
  // to return ~0, not 0. Otherwise, we should leave the value alone.
  T allOnes = ~T(0);
  if (!v) {
    currentErrs() << "numericOf() got a null value, returning " << allOnes << "\n";
    return allOnes;
  }

  if (llvm::ConstantInt* ci = llvm::dyn_cast<llvm::ConstantInt>(v)) {
    return static_cast<T>(ci->getLimitedValue(allOnes));
  } else {
    currentErrs() << "getSaturating() was given a non-constant-int value " << *v;
    ASSERT(false);
    return allOnes;
  }
}


std::ostream& operator<<(std::ostream& out, TypeAST& type) {
  llvm::raw_os_ostream rout(out);
  foster::prettyPrintType(&type, rout, 40);
  return out;
}

std::ostream& operator<<(std::ostream& out, ExprAST& expr) {
  return expr.operator<<(out);
}


string str(ExprAST* expr) {
  if (expr) {
    std::stringstream ss; ss << (*expr); return ss.str();
  } else { return "<nil>"; }
}

string str(TypeAST* expr) {
  if (expr) {
    std::stringstream ss; ss << (*expr); return ss.str();
  } else { return "<nil>"; }
}

string str(Value* value) {
  if (value) {
    std::string s;
    llvm::raw_string_ostream ss(s); ss << *value; return ss.str();
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

// In an identifier chain such as llvm.atomic.load.xor,
// the "llvm" part parses as a variable. In the AST, subsequent components
// are not variables; they are extracted to namespace nodes during parsing.
ExprAST* VariableAST::lookup(const string& nameInNS, const string& meta) {
    ExprAST* nsast = gScopeLookupAST(this->name);
    NamespaceAST* ns = dynamic_cast<NamespaceAST*>(nsast);
    ASSERT(ns) << "namespace lookup failed" << foster::show(this) << str(nsast);
    //llvm::outs() << "var " << this->name << " looking up " << nameInNS << "\n";
    return ns->lookup(nameInNS, meta);
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

bool RefExprAST::isIndirect() {
  if (isIndirect_) return true;
  return (type && value &&
          isPointerToType(value->getType(), type->getLLVMType()));
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

PrototypeAST::PrototypeAST(TypeAST* retTy, const string& name,
             const std::vector<VariableAST*>& inArgs,
             foster::SourceRange sourceRange,
             foster::SymbolTable<foster::SymbolInfo>::LexicalScope* ascope)
    : ExprAST("PrototypeAST", sourceRange),
      name(name), inArgs(inArgs), resultTy(retTy), scope(ascope) {
        ASSERT(resultTy != NULL) << "proto: " << name << foster::show(sourceRange);
}


////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

std::ostream& IntAST::operator<<(std::ostream& out) const {
  return out << "IntAST(" << getOriginalText() << ")";
}

std::ostream& BoolAST::operator<<(std::ostream& out) const {
  return out << "BoolAST(" << string(boolValue ? "true" : "false") << ")";
}

std::ostream& VariableAST::operator<<(std::ostream& out) const {
  if (type) {
    return out << "VarAST( " << name << " : " << str(type) << ")";
  } else {
    return out << "VarAST( " << name << " : " << ")";
  }
}

std::ostream& UnaryOpExprAST::operator<<(std::ostream& out) const {
  return out << "UnaryOp(" << op << ' ' << str(this->parts[0]) << ")";
}

std::ostream& BinaryOpExprAST::operator<<(std::ostream& out) const {
  ExprAST* LHS = this->parts[kLHS];
  ExprAST* RHS = this->parts[kRHS];
  return out << "BinaryOp(lhs=" << str(LHS) << ", op=" << op << ", rhs="  << str(RHS) << ")";
}

std::ostream& CallAST::operator<<(std::ostream& out) const {
  out << "CallAST(base = " << str(this->parts[0]) << ", args = ";
  for (size_t i = 1; i < this->parts.size(); ++i) {
    out << " " << str(this->parts[i]) << ", ";
  }
  return out << ")";
}

std::ostream& NamedTypeDeclAST::operator<<(std::ostream& out) const {
  return out << "type " << name << " = " << str(type) << "\n";
}

std::ostream& SeqAST::operator<<(std::ostream& out) const {
  out << "SeqAST { ";
  for (size_t i = 0; i < this->parts.size(); ++i) {
    if (i > 0) out << " ;\n";
    out << str(this->parts[i]);
  }
  return out << " }";
}

std::ostream& TupleExprAST::operator<<(std::ostream& out) const {
  return out << "TupleExpr(" << str(this->parts[0]) << ")";
}
/*
std::ostream& SimdVectorAST::operator<<(std::ostream& out) const {
  return out << "SimdVector(" << str(this->parts[0]) << ")";
}
*/
std::ostream& SubscriptAST::operator<<(std::ostream& out) const {
  return out << "SubscriptAST(base = " << str(this->parts[0]) << ", index = " << str(this->parts[1]) << ")";
}

std::ostream& PrototypeAST::operator<<(std::ostream& out) const {
  out << "PrototypeAST(name = " << name;
  for (size_t i = 0; i < inArgs.size(); ++i) {
    out << ", arg["<<i<<"] = " << str(inArgs[i]);
  }
  if (resultTy != NULL) {
    out << ", resultTy=" << str(resultTy);
  }
  out << ")";
  return out;
}

std::ostream& FnAST::operator<<(std::ostream& out) const {
  return out << "FnAST(proto = " << str(parts[0]) << ", body = " << str(parts[1]) << "\n";
}

std::ostream& ClosureAST::operator<<(std::ostream& out) const {
  if (hasKnownEnvironment && fn) {
    out << "(closure " << str(fn->getProto());
    for (size_t i = 0; i < parts.size(); ++i) {
      out << "\t" << str(parts[i]);
    }
    return out << ")";
  } else if (fn) {
    return out << "(unrefined closure " << str(fn->getProto()) << ")";
  } else {
    return out << "(malformed closure)";
  }
}

std::ostream& IfExprAST::operator<<(std::ostream& out) const {
  return out << "if (" << str(parts[0]) << ")" <<
      " then " << str(parts[1]) << " else " << str(parts[2]);
}

std::ostream& NilExprAST::operator<<(std::ostream& out) const {
  return out << "NilExprAST()";
}

std::ostream& RefExprAST::operator<<(std::ostream& out) const {
  return out << "RefExprAST(" << str(this->parts[0]) << ")";
}

std::ostream& DerefExprAST::operator<<(std::ostream& out) const {
  return out << "DerefExprAST(" << str(this->parts[0]) << ")";
}

std::ostream& AssignExprAST::operator<<(std::ostream& out) const {
  return out << "AssignExprAST(lhs=" << str(this->parts[0])
      << ", rhs=" << str(parts[1]) << ")" << "\n";
}

std::ostream& BuiltinCompilesExprAST::operator<<(std::ostream& out) const {
  return out << "(__COMPILES__ " << str(this->parts[0]) << ")";
}

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

void          BoolAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void           IntAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void            FnAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void       ClosureAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void      VariableAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void        IfExprAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void       NilExprAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void     PrototypeAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void        ModuleAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void          CallAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void NamedTypeDeclAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }
void BuiltinCompilesExprAST::accept(ExprASTVisitor* visitor) { visitor->visit(this); }

void          SeqAST::accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
void      RefExprAST::accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
void    DerefExprAST::accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
void   AssignExprAST::accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
void    SubscriptAST::accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
void    TupleExprAST::accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }

void  UnaryOpExprAST::accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
void BinaryOpExprAST::accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }


void NamespaceAST::accept(ExprASTVisitor* visitor) {
  llvm::errs() << "Visitor called on NamespaceAST! This is probably not desired...\n";
}
