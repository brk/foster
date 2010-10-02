// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/InputFile.h"
#include "base/InputTextBuffer.h"

#include "parse/ANTLRtoFosterAST.h"
#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/ANTLRtoFosterErrorHandling.h"
#include "parse/CompilationContext.h"

#include "parse/DumpStructure.h"
#include "passes/PrettyPrintPass.h"

#include "_generated_/fosterLexer.h"
#include "_generated_/fosterParser.h"

#include "pystring/pystring.h"

#include "llvm/Support/MemoryBuffer.h"
#include "llvm/ADT/APInt.h"
#include "llvm/System/Path.h"

#include <iostream>
#include <string>
#include <map>
#include <vector>
#include <sstream>
#include <cassert>

using std::string;

using foster::TypeASTFor;
using foster::EDiag;
using foster::DDiag;
using foster::show;
using foster::CompilationContext;

using foster::currentErrs;
using foster::currentOuts;

#include "parse/ANTLRtoFosterAST-inl.h"

Exprs getExprs(pTree tree);

// expressions wrapped in () are marked here
std::map<ExprAST*, bool> gWasWrappedInExplicitParens;

bool foster::wasExplicitlyParenthesized(ExprAST* ast) {
  return gWasWrappedInExplicitParens[ast];
}

bool isBitwiseOpName(const string& op) {
  return op == "bitand" || op == "bitor" || op == "bitxor" ||
         op == "bitshl" || op == "bitlshr" || op == "bitashr";
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

namespace foster {
// "Clean" refers to integer literal text consisting
// only of (possibly hex) digits, no trailer or infix ticks.
APInt* parseAPIntFromClean(const std::string& clean, int base,
                           const SourceRange& sourceRange) {
  // Make sure the base is a reasonable one.
  if (!(base == 2  || base == 8
     || base == 10 || base == 16)) {
    EDiag() << "int base must be 2, 8, 10, or 16, but was "
            << base << show(sourceRange);
    return NULL;
  }

  // Now, clean is a string of only (possibly hex) digits.

  // Make sure the literal only contains
  // valid digits for the chosen base.
  const char* digits = "0123456789abcdef";
  for (size_t i = 0; i < clean.size(); ++i) {
    char c = tolower(clean[i]);
    ptrdiff_t pos = std::find(digits, digits + 16, c) - digits;
    if (pos >= base) {
      EDiag() << "int literal contained invalid digit '" << (std::string(1, clean[i]))
                  << "' @ " << pos << "/" << base << ", " << i << " : " << clean
              << show(sourceRange);
      return NULL;
    }
  }

  // Start with a conservative estimate of how
  // many bits we need to represent this integer
  int bitsPerDigit = int(ceil(log(base)/log(2)));
  int conservativeBitsNeeded = bitsPerDigit * clean.size() + 2;

  llvm::APInt* apint = new llvm::APInt(conservativeBitsNeeded, clean, base);

  // This is just a temporary safety measure/sanity check.
  unsigned activeBits = apint->getActiveBits();
  if (activeBits > 32) {
    EDiag() << "Integer literal requires " << activeBits
            << " bits to represent." << show(sourceRange);
    return NULL;
  }

  return apint;
}


IntAST* parseInt(const string& clean, const string& alltext, int base,
                 const SourceRange& sourceRange) {
  const APInt* apint = foster::parseAPIntFromClean(clean, base, sourceRange);
  if (!apint) {
    return NULL;
  }

  return new IntAST(apint->getActiveBits(), alltext, clean, base, sourceRange);
}

} // namespace foster

IntAST* parseIntFrom(pTree t, const SourceRange& sourceRange) {
  if (textOf(t) != "INT") {
    EDiag() << "parseIntFrom() called on non-INT token " << textOf(t)
            << show(sourceRange);
    return NULL;
  }

  int base = 10;
  std::stringstream clean, alltext;

  // Each child is either a hex clump, a backtick, or an underscore
  int nchildren = getChildCount(t);
  for (int i = 0; i < nchildren; ++i) {
    string text = textOf(child(t, i));
    if (text == "_") {
      if (i != nchildren - 2) {
        EDiag() << "number can have only one underscore,"
                << "in 2nd-to-last position!" << show(sourceRange);
        return NULL;
      } else {
        string baseText = textOf(child(t, i+1));
        alltext << "_" << baseText;

        std::stringstream ss_base(baseText);
        ss_base >> base;
        break;
      }
    } else if (pystring::count(text, "_") >= 1) {
      // An identifier like feed`face_16  is parsed as   feed ` face_16
      // not as  feed ` face _ 16, so we have to split the base off manually.
      std::vector<std::string> parts;
      pystring::split(text, parts, "_");
      if (parts.size() > 2) {
        EDiag() << "Number can have only one underscore! " << show(sourceRange);
        return NULL;
      }
      clean << parts[0];
      std::stringstream ss_base(parts[1]); ss_base >> base;
      alltext << text;
    } else if (text != "`") {
      clean << text;
      alltext << text;
    } else {
      alltext << text;
    }
  }

  return foster::parseInt(clean.str(), alltext.str(), base, sourceRange);
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

ExprAST* ExprAST_from(pTree tree);

/// Returns ast if ast may be valid as the LHS of an assign expr, else NULL.
/// Valid forms for the LHS of an assign expr are:
/// * Variables (presumably to a ref)
/// * Subscripts
/// * Lookups (eventually)
ExprAST* validateAssignLHS(ExprAST* ast) {
  if (dynamic_cast<VariableAST*>(ast)) { return ast; }
  if (dynamic_cast<SubscriptAST*>(ast)) { return ast; }
  return NULL;
}

/// Extract a name and (possibly) a type, and insert
/// a new VariableAST for the name in the symbol table.
VariableAST* parseFormal(pTree tree) {
  // ^(FORMAL ^(NAME varName) ^(... type ... ))
  pTree varNameTree = child(tree, 0);
  if (!varNameTree) {
    currentErrs() << "Error! Null var name in parseFormal..." << "\n";
    display_pTree(tree, 4);
    return NULL;
  }
  string varName = textOf(child(varNameTree, 0));
  if (getChildCount(tree) == 2) {
    TypeAST* tyExpr = TypeAST_from(child(tree, 1));
    return new VariableAST(varName, tyExpr, rangeOf(tree));
  } else {
    // no fixed type, infer later
    return new VariableAST(varName, NULL, rangeOf(tree));
  }
}

std::vector<VariableAST*> getFormals(pTree tree) {
  std::vector<VariableAST*> args;
  if (textOf(tree) == "FORMAL") {
    args.push_back(parseFormal(tree));
  } else {
    for (size_t i = 0; i < getChildCount(tree); ++i) {
       args.push_back(parseFormal(child(tree, i)));
    }
  }
  return args;
}

PrototypeAST* getFnProto(string name,
                         pTree formalsTree,
                         pTree retTyExprTree)
{
  std::vector<VariableAST*> in = getFormals(formalsTree);
  TypeAST* retTy = TypeAST_from(retTyExprTree);
  if (!retTy) {
    retTy = TypeAST::i(32);
  }

  pTree sourceEndTree = (retTyExprTree != NULL) ? retTyExprTree : formalsTree;
  foster::SourceRange sourceRange = rangeFrom(formalsTree, sourceEndTree);
  PrototypeAST* proto = new PrototypeAST(retTy, name, in, sourceRange);

  gScope.getRootScope()->insert(name, proto);

  return proto;
}

FnAST* buildFn(PrototypeAST* proto, pTree bodyTree) {
  ExprAST* body = NULL;
  ExprAST::ScopeType* scope = gScope.pushScope(proto->getName());
    // Ensure all the function parameters are available in the function body.
    for (unsigned i = 0; i < proto->inArgs.size(); ++i) {
      scope->insert(proto->inArgs[i]->name, proto->inArgs[i]);
    }
    body = ExprAST_from(bodyTree);
  gScope.popScope();

  // TODO make source range more accurate
  return new FnAST(proto, body, scope, rangeOf(bodyTree));
}

// parses    a  op  b...c
ExprAST* parseBinaryOpExpr(
    const std::string& opname, ExprAST* a, ExprAST* bc) {

  if (BinaryOpExprAST* rhs = dynamic_cast<BinaryOpExprAST*>(bc)) {
    // ExprAST_from strips parens from expressions; instead of recording their
    // presence in the original source in the ExprAST, we store parenthesized
    // AST nodes in a separate table.
    if (foster::wasExplicitlyParenthesized(rhs)) {
      // Can't split the RHS up; no choice but to return op(a, (b...c))
      goto done;
    }

    ExprAST* b = rhs->parts[rhs->kLHS];
    ExprAST* c = rhs->parts[rhs->kRHS];
    std::string rop = rhs->op;

    // a opname b rop c
    foster::OperatorPrecedenceTable::OperatorRelation rel =
      CompilationContext::getOperatorRelation(opname, rop);
            ////foster::gCompilationContexts.top()->prec.get(opname, rop);
    if (rel == foster::OperatorPrecedenceTable::kOpBindsTighter) {
      delete rhs; // return ((a opname b) rop c)
      ExprAST* ab = parseBinaryOpExpr(opname, a, b);
      return new BinaryOpExprAST(rop, ab, c, rangeFrom(ab, c));
    }
  }

  done:
  return new BinaryOpExprAST(opname, a, bc, rangeFrom(a, bc));
}

// defaultSymbolTemplate can include "%d" to embed a unique number; otherwise,
// a unique int will be appended to the template.
string parseFnName(string defaultSymbolTemplate, pTree tree) {
  string name;
  if (getChildCount(child(tree, 0)) == 1) {
    pTree treeName = child(tree, 0);
    string nameWithQuotes = textOf(child(treeName, 0));
    name = nameWithQuotes.substr(1, nameWithQuotes.size() - 2);
  } else {
    name = freshName(defaultSymbolTemplate);
  }
  return name;
}

FnAST* parseFn(string defaultSymbolTemplate, pTree tree) {
  // (FN 0:NAME 1:IN 2:OUT 3:BODY)
  string name = parseFnName(defaultSymbolTemplate, tree);
  PrototypeAST* proto = getFnProto(name,
                                   child(tree, 1),
                                   child(tree, 2));
  //currentOuts() << "parseFn proto = " << str(proto) << "\n";
  return buildFn(proto, child(tree, 3));
}

// ExprAST_from() is straight-up recursive, and uses gScope and gTypeScope
// to keep track of lexical scoping for variables and types, respectively.
// This works wonderfully for function bodies, where variables must appear
// in topologically sorted order. In order to allow functions at the top-level
// to appear in unsorted order, we have to separate the extraction of function
// prototypes (and insertion of said name/proto pair into the gScope symbol
// table) from the actual parsing of the function body.
ModuleAST* parseTopLevel(pTree tree, std::string moduleName) {
  // The top level is composed of:
  //
  // * Type definitions, such as
  //        type node = tuple { ?ref node, i32 }
  // * Function definitions, such as
  //        f = fn () { 0 }

  std::vector<pTree> pendingParseTrees(getChildCount(tree));
  std::vector<ExprAST*> parsedExprs(getChildCount(tree));
  // forall i, exprs[i] == pendingParseTrees[i] == NULL

  for (size_t i = 0; i < getChildCount(tree); ++i) {
    pendingParseTrees[i] = child(tree, i);
  }

  // forall i, exprs[i] == NULL, pendingParseTrees[i] != NULL
  typedef std::map<pTree, PrototypeAST*> ProtoMap;
  ProtoMap protos;

  for (size_t i = 0; i < pendingParseTrees.size(); ++i) {
    pTree c = pendingParseTrees[i];
    int token = typeOf(c);

    if (token == TYPEDEFN) {
      ExprAST* typeDefn = ExprAST_from(c);
      parsedExprs[i] = typeDefn;
    } else if (token == FNDEF) {
      ASSERT(getChildCount(c) == 2);
      // x = fn { blah }   ===   x = fn "x" { blah }
      pTree lval = (child(c, 0));
      pTree rval = (child(c, 1));
      if (typeOf(lval) == NAME && typeOf(rval) == FN) {
        // (FN 0:NAME 1:IN 2:OUT 3:BODY)
        string name = parseFnName(textOf(child(lval, 0)), rval);
        protos[c] = getFnProto(name, child(rval, 1), child(rval, 2));
      } else {
        EDiag() << "not assigning top-level function to a name?"
                << show(rangeOf(c));
      }
      // parsedExprs[i] remains NULL
    } else if (token == FN) {
      // (FN 0:NAME 1:IN 2:OUT 3:BODY)
      string name = parseFnName(textOf(child(c, 0)), c);
      protos[c] = getFnProto(name, child(c, 1), child(c, 2));
      // parsedExprs[i] remains NULL
    } else {
      ExprAST* otherExpr = ExprAST_from(c);
      if (FnAST* explicitlyNamedFn = dynamic_cast<FnAST*>(otherExpr)) {
        explicitlyNamedFn->removeClosureEnvironment();
        parsedExprs[i] = explicitlyNamedFn;
      } else {
        EDiag() << "expected function or type" << show(rangeOf(c));
      }
    }
  }

  // forall i, either parsedExprs[i] == NULL && protos[i] != NULL
  //              or  parsedExprs[i] != NULL

  for (size_t i = 0; i < parsedExprs.size(); ++i) {
    if (parsedExprs[i]) continue;
    pTree c = pendingParseTrees[i];
    ASSERT(c) << "no parsed expr and no pending parse tree?!?";
    PrototypeAST* proto = protos[c];
    ASSERT(proto) << "no parsed expr and no proto?!?" << show(rangeOf(c));
    pTree fntree =   (typeOf(c) == FNDEF)   ?   child(c, 1)
                       : (typeOf(c) == FN   )   ?   c
                       :                            NULL;
    FnAST* fn = buildFn(proto, child(fntree, 3));
    fn->removeClosureEnvironment();
    parsedExprs[i] = fn;
  }

  return new ModuleAST(parsedExprs,
                       moduleName,
                       gScope.getRootScope(),
                       rangeOf(tree));
}

ExprAST* parseTypeDefinition(pTree tree) {
  pTree nameTree = child(tree, 0);
  string name = textOf(child(nameTree, 0));

  llvm::PATypeHolder namedType = llvm::OpaqueType::get(llvm::getGlobalContext());
  gTypeScope.pushScope("opaque");
    // namedType.get() is an OpaqueType at this point, so we cannot yet do
    // anything but wrap it directly.
    gTypeScope.insert(name, TypeAST::reconstruct(
          llvm::dyn_cast<const llvm::OpaqueType>(namedType.get())));
    TypeAST* tyExpr = TypeAST_from(child(tree, 1));
    llvm::cast<llvm::OpaqueType>(namedType.get())->
               refineAbstractTypeTo(tyExpr->getLLVMType());
  gTypeScope.popScope();

  gTypeScope.insert(name, tyExpr);

  DDiag() << "Associated " << name << " with type " << str(tyExpr) << "\n";
  return new NamedTypeDeclAST(name, tyExpr, rangeOf(tree));
}

// ^(CTOR ^(NAME blah) ^(SEQ ...))
ExprAST* parseCtorExpr(pTree tree,
                       const foster::SourceRange& sourceRange) {
  pTree nameNode = child(tree, 0);
  pTree seqArgs = child(tree, 1);

  string name = textOf(child(nameNode, 0));

  if (name == "tuple") {
    return new TupleExprAST(ExprAST_from(seqArgs), sourceRange);
  }

  foster::EDiag() << "CTOR token parsing found unknown"
                  << " type name '" << name << "'"
                  << foster::show(sourceRange);
  return NULL;
}

std::vector<TypeAST*> getTypes(pTree tree);

// ^(CTOR ^(NAME blah) ^(SEQ ...))
TypeAST* parseCtorType(pTree tree,
                       const foster::SourceRange& sourceRange) {
  pTree nameNode = child(tree, 0);
  pTree seqArgs = child(tree, 1);

  string name = textOf(child(nameNode, 0));
  if (name == "tuple") {
    return TupleTypeAST::get(getTypes(seqArgs)); //, sourceRange);
  }

  if (TypeAST* ty = gTypeScope.lookup(name)) {
    return ty; // TODO fix
  }

  foster::EDiag() << "CTOR type parsing found unknown"
                  << " type name '" << name << "'"
                  << foster::show(sourceRange);
  return NULL;
}

ExprAST* parseTrailers(pTree tree,
                       const foster::SourceRange& sourceRange) {
  ASSERT(getChildCount(tree) >= 2);
  // name (args) ... (args)
  ExprAST* prefix = ExprAST_from(child(tree, 0));
  for (size_t i = 1; i < getChildCount(tree); ++i) {
    int trailerType = typeOf(child(tree, i));
    if (trailerType == CALL) {
      Exprs args = getExprs(child(tree, i));

      // Two different things can parse as function calls: normal function
      // calls, and function-call syntax for built-in bitwise operators.
      VariableAST* varPrefix = dynamic_cast<VariableAST*>(prefix);
      if (varPrefix) {
        if (isBitwiseOpName(varPrefix->name)) {
          if (args.size() != 2) {
            currentErrs() << "Error! Bitwise operator " << varPrefix->name
                      << " with bad number of arguments: " << args.size()
                      << "\n";
            return NULL;
          }
          prefix = new BinaryOpExprAST(varPrefix->name, args[0], args[1],
                                       sourceRange);
          continue;
        }
        // Else fall through to general case below
      }
      prefix = new CallAST(prefix, args, sourceRange);
    } else if (trailerType == LOOKUP) {
      pTree nameNode = child(child(tree, i), 0);
      const string& name = textOf(child(nameNode, 0));
      prefix = prefix->lookup(name);
      if (!prefix) {
        currentErrs() << "Lookup of name '" << name << "' failed." << "\n";
      }
    } else if (trailerType == SUBSCRIPT) {
      prefix = new SubscriptAST(prefix,
                                ExprAST_from(child(child(tree, i), 0)),
                                sourceRange);
    } else {
      currentErrs() << "Unknown trailer type " << textOf(child(tree, i)) << "\n";
    }
  }
  return prefix;
}

ExprAST* parseIf(pTree tree, const SourceRange& sourceRange) {
  return new IfExprAST(ExprAST_from(child(tree, 0)),
                       ExprAST_from(child(tree, 1)),
                       ExprAST_from(child(tree, 2)),
                       sourceRange);
}

ExprAST* parseSeq(pTree tree, const SourceRange& sourceRange) {
  Exprs exprs;
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    ExprAST* ast = ExprAST_from(child(tree, i));
    if (ast != NULL) {
      exprs.push_back(ast);
    }
  }
  return new SeqAST(exprs, sourceRange);
}

ExprAST* parseParenExpr(pTree tree) {
  ExprAST* rv = ExprAST_from(child(tree, 0));
  gWasWrappedInExplicitParens[rv] = true;
  return rv;
}

ExprAST* parseBuiltinCompiles(pTree tree, const SourceRange& sourceRange) {
 return new BuiltinCompilesExprAST(ExprAST_from(child(tree, 0)), sourceRange);
}

ExprAST* ExprAST_from(pTree tree) {
  if (!tree) return NULL;

  int token = typeOf(tree);
  string text = textOf(tree);
  foster::SourceRange sourceRange = rangeOf(tree);

  if (token == TYPEDEFN) { return parseTypeDefinition(tree); }
  if (token == TRAILERS) { return parseTrailers(tree, sourceRange); }
  if (token == CTOR) { return parseCtorExpr(tree, sourceRange); }
  if (token == IF) { return parseIf(tree, sourceRange); }
  if (token == EXPRS || token == SEQ) { return parseSeq(tree, sourceRange); }
  if (token == INT) { return parseIntFrom(tree, sourceRange); }
  if (token == PARENEXPR) { return parseParenExpr(tree); }
  if (token == COMPILES) { return parseBuiltinCompiles(tree, sourceRange); }
  if (token == BODY) { return ExprAST_from(child(tree, 0)); }

  if (text == "false" || text == "true") {
    return new BoolAST(text, sourceRange);
  }

  // <formal arg (body | next) [type]>
  if (token == LETEXPR) {
    pTree tyExprTree = NULL;
    if (getChildCount(tree) == 4) {
      tyExprTree = child(tree, 3);
    }

    PrototypeAST* proto = getFnProto(freshName("<anon_fnlet_%d>"),
                                     child(tree, 0),
                                     tyExprTree);
    FnAST* fn = buildFn(proto, child(tree, 2));

    ExprAST* a = ExprAST_from(child(tree, 1));
    Exprs args; args.push_back(a);
    return new CallAST(fn, args, sourceRange);
  }

  if (token == NAME) {
    string varName = textOf(child(tree, 0));

    // Don't bother trying to look up special variable names,
    // since we'll end up discarding this variable soon anyways.
    if (isBitwiseOpName(varName)) {
      return new VariableAST(varName, NULL, sourceRange);
    }

    ExprAST* varOrProto = gScope.lookup(varName);
    if (!varOrProto) {
      EDiag() << "unknown var name: " << varName << show(sourceRange);
      return NULL;
    } else {
      return new VariableAST(varName, varOrProto->type, sourceRange);
    }
  }

  if (token == FNDEF) {
    ASSERT(getChildCount(tree) == 2);
    // x = fn { blah }   ===   x = fn "x" { blah }
    pTree lval = (child(tree, 0));
    pTree rval = (child(tree, 1));

    if (typeOf(lval) == NAME && typeOf(rval) == FN) {
      return parseFn(textOf(child(lval, 0)), rval);
    } else {
      currentErrs() << "Not assigning function to a name?" << "\n";
      return NULL;
    }
  }

  if (token == OUT) {
    return (getChildCount(tree) == 0)
              ? NULL
              : ExprAST_from(child(tree, 0));
  }

  if (token == FN) {
    // for now, this "<anon_fn" prefix is used for closure conversion later on
    FnAST* fn = parseFn("<anon_fn_%d>", tree);
    if (!fn->getBody()) {
      foster::EDiag() << "Found bare proto (with no body)"
                      << " when expecting full fn literal."
                      << foster::show(fn);
      return NULL;
    }
    fn->markAsClosure();
    return fn;
  }

  // Implicitly, every entry in the precedence table is a binary operator.
  if (CompilationContext::isKnownOperatorName(text)) {
    return parseBinaryOpExpr(text,
                             ExprAST_from(child(tree, 0)),
                             ExprAST_from(child(tree, 1)));
  }

  // Should have handled all keywords by now...
  if (CompilationContext::isKeyword(text)) {
    EDiag() << "illegal use of keyword '" << text << "'" << show(sourceRange);
    return NULL;
  }

  if (CompilationContext::isReservedKeyword(text)) {
    EDiag() << "cannot use reserved keyword '" << text << "'"
            << show(sourceRange);
    return NULL;
  }

  string name = str(tree->getToken(tree));
  foster::EDiag() << "returning NULL ExprAST for tree token " << name
                  << "with text '" << text << "'"
                  << foster::show(sourceRange);
  return NULL;
}

Exprs getExprs(pTree tree) {
  Exprs f;
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    f.push_back(ExprAST_from(child(tree, i)));
  }
  return f;
}

TypeAST* TypeAST_from(pTree tree) {
  if (!tree) return NULL;

  int token = typeOf(tree);
  string text = textOf(tree);
  foster::SourceRange sourceRange = rangeOf(tree);

  if (token == PARENEXPR) { return TypeAST_from(child(tree, 0));  }
  if (token == CTOR) { return parseCtorType(tree, sourceRange);  }
  if (token == INT) {
    IntAST* intAST = parseIntFrom(tree, sourceRange);
    if (intAST) {
      return LiteralIntValueTypeAST::get(intAST);
    }
    EDiag() << "Unable to parse integer in type";
    return NULL;
  }

  if (token == NAME) {
    string name = textOf(child(tree, 0));
    TypeAST* ty = TypeASTFor(name);
    if (!ty) {
      EDiag() << "name " << name << " appears to not be a valid type name"
              << show(sourceRange);
    }
    return ty;
  }

  if (token == FN) {
    FnAST* fn = parseFn("<anon_fn_type_%d>", tree);
    if (!fn) {
      EDiag() << "no fn expr when parsing fn type!" << show(sourceRange);
      return NULL;
    }
    if (fn->getBody()) {
      EDiag() << "had unexpected fn body when parsing fn type!" << show(fn);
    }

    llvm::outs() << "fn type node:\n";
    foster::prettyPrintExpr(fn, llvm::outs(), 40);
    foster::dumpExprStructure(llvm::outs(), fn);
    llvm::outs() << "\n\n";

    std::vector<TypeAST*> argTypes;

    for (int i = 0; i < fn->getProto()->inArgs.size(); ++i) {
      llvm::outs() << "fn arg type " << i << " : " << fn->getProto()->inArgs[i]->type << "\n";
      argTypes.push_back(fn->getProto()->inArgs[i]->type);
    }

    TypeAST* returnType = fn->getProto()->resultTy;
    FnTypeAST* fty =  FnTypeAST::get(returnType, argTypes, "fastcc");
    // Mark the function type as a known closure type,
    // rather than a top-level procedure type.
    fty->markAsClosure();
    return fty;
  }

  if (token == OUT) {
    bool noChildren = (getChildCount(tree) == 0);
    return noChildren ? NULL : TypeAST_from(child(tree, 0));
  }

  string name = str(tree->getToken(tree));
  foster::EDiag() << "returning NULL TypeAST for tree token " << name
                  << foster::show(sourceRange);
  return NULL;
}

std::vector<TypeAST*> getTypes(pTree tree) {
  int token = typeOf(tree);

  std::vector<TypeAST*> types;
  if (token == EXPRS || token == SEQ) {
    for (size_t i = 0; i < getChildCount(tree); ++i) {
      TypeAST* ast = TypeAST_from(child(tree, i));
      if (ast != NULL) {
        types.push_back(ast);
      }
    }
  } else {
    display_pTree(tree, 0);
    foster::EDiag() << "getTypes called with unexpected tree!";
  }
  return types;
}


namespace foster {

  struct ANTLRContext {
    string filename;
    pANTLR3_INPUT_STREAM input;
    pfosterLexer lxr;
    pANTLR3_COMMON_TOKEN_STREAM tstream;
    pfosterParser psr;

    ~ANTLRContext() {
      psr     ->free  (psr);      psr     = NULL;
      tstream ->free  (tstream);  tstream = NULL;
      lxr     ->free  (lxr);      lxr     = NULL;
      input   ->close (input);    input   = NULL;
    }
  };

  namespace {
    void createParser(foster::ANTLRContext& ctx,
                      const string& filepath,
                      foster::InputTextBuffer* textbuf) {
      llvm::MemoryBuffer* buf = textbuf->getMemoryBuffer();
      ASSERT(buf->getBufferSize() <= ((ANTLR3_UINT32)-1)
             && "Trying to parse files larger than 4GB makes me cry.");
      ctx.filename = filepath;
      ctx.input = antlr3NewAsciiStringInPlaceStream(
                                    (pANTLR3_UINT8) buf->getBufferStart(),
                                    (ANTLR3_UINT32) buf->getBufferSize(),
                                    NULL);
      ctx.lxr = fosterLexerNew(ctx.input);
      if (ctx.lxr == NULL) {
        ANTLR3_FPRINTF(stderr, "Unable to create lexer\n");
        exit(ANTLR3_ERR_NOMEM);
      }

      ctx.tstream = antlr3CommonTokenStreamSourceNew(ANTLR3_SIZE_HINT,
                                                     TOKENSOURCE(ctx.lxr));

      if (ctx.tstream == NULL) {
        ANTLR3_FPRINTF(stderr, "Out of memory trying to allocate token stream.\n");
        exit(ANTLR3_ERR_NOMEM);
      }

      ctx.psr = fosterParserNew(ctx.tstream);
      if (ctx.psr == NULL) {
        ANTLR3_FPRINTF(stderr, "Out of memory trying to allocate parser.\n");
        exit(ANTLR3_ERR_NOMEM);
      }
    }

    void createParser(foster::ANTLRContext& ctx,
                      const foster::InputFile& infile) {
      createParser(ctx,
                   infile.getPath().str(),
                   infile.getBuffer());
    }

    void installTreeTokenBoundaryTracker(pANTLR3_BASE_TREE_ADAPTOR adaptor);
  } // unnamed namespace

  void deleteANTLRContext(ANTLRContext* ctx) { delete ctx; }

  ExprAST* parseExpr(const std::string& source,
                     unsigned& outNumANTLRErrors,
                     CompilationContext* cc) {
    ANTLRContext* ctx = new ANTLRContext();
    const char* s = source.c_str();

    foster::InputTextBuffer* membuf = new InputTextBuffer(s, source.size());
    createParser(*ctx, "", membuf);

    installTreeTokenBoundaryTracker(ctx->psr->adaptor);
    foster::installRecognitionErrorFilter(ctx->psr->pParser->rec);

    CompilationContext::pushContext(cc);

    gInputFile = NULL;
    gInputTextBuffer = membuf;

    fosterParser_expr_return langAST = ctx->psr->expr(ctx->psr);

    outNumANTLRErrors = ctx->psr->pParser->rec->state->errorCount;

    ExprAST* rv = ExprAST_from(langAST.tree);

    // If we reuse the same compilation context again later,
    // we do not want to accidentally pick up an incorrect
    // token boundary if we happen to randomly get the same
    // tree pointer values! Doing so can make ANTLR crash.
    CompilationContext::clearTokenBoundaries();
    CompilationContext::popCurrentContext();

    delete ctx;

    return rv;
  }

  ModuleAST* parseModule(const InputFile& file,
                       const std::string& moduleName,
                       pTree& outTree,
                       ANTLRContext*& ctx,
                       unsigned& outNumANTLRErrors) {
    ctx = new ANTLRContext();
    createParser(*ctx, file);

    installTreeTokenBoundaryTracker(ctx->psr->adaptor);
    foster::installRecognitionErrorFilter(ctx->psr->pParser->rec);

    gInputFile = &file;
    gInputTextBuffer = file.getBuffer();

    fosterParser_program_return langAST = ctx->psr->program(ctx->psr);

    outTree = langAST.tree;
    outNumANTLRErrors = ctx->psr->pParser->rec->state->errorCount;

    ModuleAST* m = parseTopLevel(outTree, moduleName);

    return m;
  }

  ////////////////////////////////////////////////////////////////////

  // Ugly ANTLR-C token boundary customization.
  namespace {
    typedef void                  (*setTokenBoundariesFunc)
    (struct ANTLR3_BASE_TREE_ADAPTOR_struct * adaptor, void * t,
     pANTLR3_COMMON_TOKEN startToken, pANTLR3_COMMON_TOKEN stopToken);

    static setTokenBoundariesFunc sgDefaultSTB;

    static void customSetTokenBoundariesFunc
    (struct ANTLR3_BASE_TREE_ADAPTOR_struct * adaptor, void * t,
     pANTLR3_COMMON_TOKEN startToken, pANTLR3_COMMON_TOKEN stopToken) {
      sgDefaultSTB(adaptor, t, startToken, stopToken);
      CompilationContext::setTokenRange((pTree) t, startToken, stopToken);
    }

    // This is a vaguely unpleasant (but terrifically accurate) hack
    // to monitor the token boundaries computed for tree nodes, which
    // are unfortunately (and strangely) not actually stored in the nodes
    // themselves, but rather in shadow parent nodes inaccessible from
    // the tree nodes themselves. Anyways, we just replace the function pointer
    // in the virtual table with a thin shim, above.
    void installTreeTokenBoundaryTracker(pANTLR3_BASE_TREE_ADAPTOR adaptor) {
      sgDefaultSTB = adaptor->setTokenBoundaries;
      adaptor->setTokenBoundaries = customSetTokenBoundariesFunc;
    }
  } // unnamed namespace

} // namespace foster
const char* ANTLR_VERSION_STR = PACKAGE_VERSION;
