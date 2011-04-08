// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/InputFile.h"
#include "base/InputTextBuffer.h"

#include "parse/ANTLRtoFosterAST.h"
#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/ANTLRtoFosterErrorHandling.h"
#include "parse/ParsingContext.h"

#include "_generated_/fosterLexer.h"
#include "_generated_/fosterParser.h"

#include "pystring/pystring.h"

#include "llvm/ADT/Statistic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"

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
using foster::ParsingContext;

using foster::currentErrs;
using foster::currentOuts;

#define DEBUG_TYPE "foster"

STATISTIC(sgNumExprAST, "Number of ExprASTs created");
STATISTIC(sgNumTypeAST, "Number of TypeASTs created");

std::string str(pANTLR3_STRING pstr) {
  return string((const char*)pstr->chars);
}

string str(pANTLR3_COMMON_TOKEN tok) {
  if (!tok) return "<nil tok>";

  switch (tok->type) {
    case ANTLR3_TEXT_NONE: return "none";
    case ANTLR3_TEXT_CHARP: return string((const char*)tok->tokText.chars);
    case ANTLR3_TEXT_STRING: return str(tok->tokText.text);
  }

  pANTLR3_STRING pstr = tok->toString(tok);
  if (pstr) {
    return str(pstr);
  } else {
    char buf[80];
    sprintf(buf, "<str(tok) failed, type = %d>", tok->type);
    return string(buf);
  }
}

void display_pTree(pTree t, int nspaces);

size_t getChildCount(pTree tree) {
  return static_cast<size_t>(tree->getChildCount(tree));
}

string textOf(pTree tree) {
  ASSERT(tree) << "can't get text of null pTree!";
  return str(tree->getText(tree));
}

pTree child(pTree tree, int i) {
  ASSERT(tree) << "can't take child of null pTree!";
  return (pTree) tree->getChild(tree, i);
}

int typeOf(pTree tree) { return tree->getType(tree); }

pANTLR3_COMMON_TOKEN getStartToken(pTree tree) {
  if (!tree) return NULL;
  pANTLR3_COMMON_TOKEN tok = ParsingContext::getStartToken(tree);
  if (tok) return tok;

  // Some nodes we're okay with having no token info for...
  if (getChildCount(tree) == 0) {
    int tag = typeOf(tree);
    if (tag == OUT || tag == IN || tag == BODY
     || tag == ANTLR3_TOKEN_INVALID) {
      return NULL;
    }
  }

  // Usually, ANTLR will have annotated the tree directly;
  // however, in some cases, only subtrees will have token
  // information. In such cases, we search along the edge of the
  // parse tree to find the first edge child with token info.
  pTree node = tree;
  while (!tok && getChildCount(node) > 0) {
    node = child(node, 0);
    tok = ParsingContext::getStartToken(node);
  }
  if (!tok) {
    currentOuts() << "Warning: unable to find start token for ANTLR parse tree"
              << " node " << textOf(tree) << " @ " << tree
              << " , " << typeOf(tree) << "\n";
  }
  return tok;
}

pANTLR3_COMMON_TOKEN getEndToken(pTree tree) {
  if (!tree) return NULL;
  pANTLR3_COMMON_TOKEN tok = ParsingContext::getEndToken(tree);
  if (tok) return tok;

  if (getChildCount(tree) == 0) {
    int tag = typeOf(tree);
    if (tag == OUT || tag == IN || tag == BODY
     || tag == ANTLR3_TOKEN_INVALID) {
      return NULL;
    }
  }

  pTree node = tree;
  while (!tok && getChildCount(node) > 0) {
    node = child(node, getChildCount(node) - 1);
    tok = ParsingContext::getEndToken(node);
  }
  if (!tok) {
    currentOuts() << "Warning: unable to find end token for ANTLR parse tree"
              << " node " << textOf(tree) << " @ " << tree << "\n";
  }
  return tok;
}

foster::SourceLocation getStartLocation(pANTLR3_COMMON_TOKEN tok) {
  if (!tok) { return foster::SourceLocation::getInvalidLocation(); }
  // ANTLR gives source locations starting from 1; we want them from 0
  return foster::SourceLocation(tok->getLine(tok) - 1,
                                tok->getCharPositionInLine(tok));
}

foster::SourceLocation getEndLocation(pANTLR3_COMMON_TOKEN tok) {
  if (!tok) {
    return foster::SourceLocation::getInvalidLocation();
  }
  return foster::SourceLocation(tok->getLine(tok) - 1,
      tok->getCharPositionInLine(tok) + tok->getText(tok)->len);
}

foster::SourceRange rangeFrom(pTree start, pTree end) {
  pANTLR3_COMMON_TOKEN stok = getStartToken(start);
  pANTLR3_COMMON_TOKEN etok = getEndToken(end);
  return foster::SourceRange(foster::gInputFile,
      getStartLocation(stok),
      getEndLocation(etok),
      foster::gInputTextBuffer);
}

foster::SourceRange rangeOf(pTree tree) {
  return rangeFrom(tree, tree);
}

foster::SourceRange rangeFrom(ExprAST* a, ExprAST* b) {
  if (a && b) {
    foster::SourceRange ar = a->sourceRange;
    foster::SourceRange br = b->sourceRange;
    ASSERT(ar.source == br.source);
    return foster::SourceRange(ar.source, ar.begin, br.end);
  } else if (a) {
    foster::SourceRange ar = a->sourceRange;
    return foster::SourceRange(ar.source, ar.begin,
                   foster::SourceLocation::getInvalidLocation());
  } else {
    return foster::SourceRange::getEmptyRange();
  }
}


string spaces(int n) { return string(n, ' '); }

void display_pTree(pTree t, int nspaces) {
  if (!t) {
    currentOuts() << spaces(nspaces) << "<NULL tree>" << "\n";
    return;
  }

  int token = t->getType(t);
  string text = textOf(t);
  int nchildren = getChildCount(t);
  std::stringstream ss;
  ss << spaces(nspaces) << "<" << text << "; ";
  currentOuts() << ss.str() << spaces(70 - ss.str().size())
            << token << " @ " << t;
  currentOuts() << " (";
  currentOuts() << (ParsingContext::getStartToken(t) ? '+' : '-');
  currentOuts() << (ParsingContext::getEndToken(t)   ? '+' : '-');
  currentOuts() << ")" << "\n";
  for (int i = 0; i < nchildren; ++i) {
    display_pTree(child(t, i), nspaces+2);
  }
  currentOuts() << spaces(nspaces) << "/" << text << ">" << "\n";
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

// expressions wrapped in () are marked here
std::map<const ExprAST*, bool> gWasWrappedInExplicitParens;

bool foster::wasExplicitlyParenthesized(const ExprAST* ast) {
  return gWasWrappedInExplicitParens[ast];
}

const char* getDefaultCallingConvParse() {
  //foster::EDiag() << "getDefaultCallingConvParse()";
  return foster::kDefaultFnLiteralCallingConvention;
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

IntAST* parseIntFrom(pTree t, const SourceRange& sourceRange) {
  if (textOf(t) != "INT") {
    EDiag() << "parseIntFrom() called on non-INT token " << textOf(t)
            << show(sourceRange);
    return NULL;
  }

  std::stringstream alltext;

  // Each child is either a hex clump, a backtick, or an underscore
  int nchildren = getChildCount(t);
  for (int i = 0; i < nchildren; ++i) {
    string text = textOf(child(t, i));
    if (text == "_" && i != nchildren - 2) {
      EDiag() << "number can have only one underscore,"
              << "in 2nd-to-last position!" << show(sourceRange);
      return NULL;
    }

    alltext << text;
  }

  return new IntAST(alltext.str(), sourceRange);
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

ExprAST* ExprAST_from(pTree tree);

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

  return proto;
}

FnAST* buildFn(PrototypeAST* proto, pTree bodyTree) {
  ExprAST* body = ExprAST_from(bodyTree);
  // TODO make source range more accurate
  return new FnAST(proto, body, rangeOf(bodyTree));
}

string parseFnName(string name, pTree tree) {
  if (getChildCount(child(tree, 0)) == 1) {
    ASSERT(false) << "temporarily disabled support for fn symbol names";
    pTree treeName = child(tree, 0);
    string nameWithQuotes = textOf(child(treeName, 0));
    name = nameWithQuotes.substr(1, nameWithQuotes.size() - 2);
  }
  return ParsingContext::freshName(name);
}

FnAST* parseFn(string defaultSymbolTemplate, pTree tree) {
  // (FN 0:NAME 1:IN 2:OUT 3:BODY)
  string name = parseFnName(defaultSymbolTemplate, tree);
  PrototypeAST* proto = getFnProto(name,
                                   child(tree, 1),
                                   child(tree, 2));
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

    if (token == FNDEF) {
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
    parsedExprs[i] = buildFn(proto, child(fntree, 3));
  }

  return new ModuleAST(parsedExprs,
                       moduleName,
                       rangeOf(tree));
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

  if (TypeAST* ty = ParsingContext::lookupType(name)) {
    return ty; // TODO fix
  }

  foster::EDiag() << "CTOR type parsing found unknown"
                  << " type name '" << name << "'"
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

ExprAST* parseTrailers(pTree tree,
                       const foster::SourceRange& sourceRange) {
  ASSERT(getChildCount(tree) >= 2);
  // name (args) ... (args)
  ExprAST* prefix = ExprAST_from(child(tree, 0));
  for (size_t i = 1; i < getChildCount(tree); ++i) {
    int trailerType = typeOf(child(tree, i));
    if (trailerType == CALL) {
      Exprs args = getExprs(child(tree, i));
      prefix = new CallAST(prefix, args, sourceRange);
    } else if (trailerType == LOOKUP) {
      ASSERT("lookups temporarily not supported");
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

ExprAST* extractBinopChain(pTree tree,
           std::vector< std::pair<std::string, ExprAST*> >& pairs) {
  pTree binops = child(tree, 0);
  pTree compounds = child(tree, 1);

  ASSERT(getChildCount(binops) == getChildCount(compounds) - 1);

  for (size_t i = 0; i < getChildCount(binops); ++i) {
    pairs.push_back(std::make_pair(
                        textOf(child(binops, i)),
                        ExprAST_from(child(compounds, i + 1))));
  }

  return ExprAST_from(child(compounds, 0));
}

void leftAssoc(std::vector<std::string>& opstack,
               std::vector<ExprAST*>& argstack) {
  ExprAST*           y = argstack.back(); argstack.pop_back();
  ExprAST*           x = argstack.back(); argstack.pop_back();
  const std::string& o =  opstack.back();  opstack.pop_back();

  Exprs exprs;
  exprs.push_back(x);
  exprs.push_back(y);
  ExprAST* opr = new VariableAST("primitive_"+o+"_i32", NULL, rangeFrom(x, y));
  argstack.push_back(new CallAST(opr, exprs, rangeFrom(x, y)));
}

ExprAST* parseBinopChain(pTree tree) {
  std::vector< std::pair<std::string, ExprAST*> > pairs;
  ExprAST* first = extractBinopChain(tree, pairs);

  std::vector<std::string> opstack;
  std::vector<ExprAST*> argstack;
  argstack.push_back(first);
  argstack.push_back(pairs[0].second);
  opstack.push_back(pairs[0].first);

  for (size_t i = 1; i < pairs.size(); ++i) {
    const std::string& opd = pairs[i].first;
    ExprAST* e = pairs[i].second;
    while (!opstack.empty()) {
      const std::string& top = opstack.back();
      foster::OperatorPrecedenceTable::OperatorRelation rel =
                           ParsingContext::getOperatorRelation(top, opd);
      if (rel != foster::OperatorPrecedenceTable::kOpBindsTighter) {
        break;
      }
      leftAssoc(opstack, argstack);
    }
    argstack.push_back(e);
    opstack.push_back(opd);
  }

  while (!opstack.empty()) {
    leftAssoc(opstack, argstack);
  }

  ASSERT(argstack.size() == 1);
  return argstack[0];
}

// <formal arg (body | next) [type]>
ExprAST* parseLetExpr(pTree tree, const foster::SourceRange& sourceRange) {
  TypeAST* type = NULL;
  if (getChildCount(tree) == 4) {
    type = TypeAST_from(child(tree, 3));
  }

  VariableAST* var = parseFormal(child(tree, 0));
  ExprAST* bound  = ExprAST_from(child(tree, 1));
  ExprAST* inexpr = ExprAST_from(child(tree, 2));
  return new LetAST(var, bound, inexpr, type, sourceRange);
}

ExprAST* ExprAST_from(pTree tree) {
  if (!tree) return NULL;

  ++sgNumExprAST;

  int token = typeOf(tree);
  string text = textOf(tree);
  foster::SourceRange sourceRange = rangeOf(tree);

  if (token == TRAILERS) { return parseTrailers(tree, sourceRange); }
  if (token == CTOR) {     return parseCtorExpr(tree, sourceRange); }
  if (token == IF) {       return parseIf(tree, sourceRange); }
  if (token == EXPRS || token == SEQ) { return parseSeq(tree, sourceRange); }
  if (token == INT) {         return parseIntFrom(tree, sourceRange); }
  if (token == PARENEXPR) {   return parseParenExpr(tree); }
  if (token == COMPILES) {    return parseBuiltinCompiles(tree, sourceRange); }
  if (token == BODY) {        return ExprAST_from(child(tree, 0)); }
  if (token == BINOP_CHAIN) { return parseBinopChain(tree); }
  if (token == LETEXPR) { return parseLetExpr(tree, sourceRange); }
  if (text == "false" || text == "true") {
    return new BoolAST(text, sourceRange);
  }

  if (token == NAME) {
    return new VariableAST(textOf(child(tree, 0)), NULL, sourceRange);
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
    FnAST* fn = parseFn("<anon_fn_", tree);
    if (!fn->getBody()) {
      foster::EDiag() << "Found bare proto (with no body)"
                      << " when expecting full fn literal."
                      << foster::show(fn);
      return NULL;
    }
    return fn;
  }

  // Should have handled all keywords by now...
  if (ParsingContext::isKeyword(text)) {
    EDiag() << "illegal use of keyword '" << text << "'" << show(sourceRange);
    return NULL;
  }

  if (ParsingContext::isReservedKeyword(text)) {
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

TypeAST* TypeAST_from(pTree tree) {
  if (!tree) return NULL;

  ++sgNumTypeAST;

  int token = typeOf(tree);
  string text = textOf(tree);
  foster::SourceRange sourceRange = rangeOf(tree);

  if (token == PARENEXPR) { return TypeAST_from(child(tree, 0));  }
  if (token == CTOR) { return parseCtorType(tree, sourceRange);  }

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
    FnAST* fn = parseFn("<anon_fn_type_", tree);
    if (!fn) {
      EDiag() << "no fn expr when parsing fn type!" << show(sourceRange);
      return NULL;
    }
    if (fn->getBody()) {
      EDiag() << "had unexpected fn body when parsing fn type!" << show(fn);
    }

    std::vector<TypeAST*> argTypes;

    for (size_t i = 0; i < fn->getProto()->inArgs.size(); ++i) {
      llvm::outs() << "fn arg type " << i << " : " << fn->getProto()->inArgs[i]->type << "\n";
      argTypes.push_back(fn->getProto()->inArgs[i]->type);
    }

    TypeAST* returnType = fn->getProto()->resultTy;
    FnTypeAST* fty =  FnTypeAST::get(returnType, argTypes,
                                     getDefaultCallingConvParse());
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

  struct FosterIndentingTokenSource : ANTLR3_TOKEN_SOURCE {
    pANTLR3_TOKEN_SOURCE originalSource;
  };

  pANTLR3_COMMON_TOKEN fosterNextTokenFunc(pANTLR3_TOKEN_SOURCE tokenSource) {
    FosterIndentingTokenSource* fits = (FosterIndentingTokenSource*) tokenSource;
    return fits->originalSource->nextToken(fits->originalSource);
  }

  pANTLR3_TOKEN_SOURCE newFosterIndentingTokenSource(pANTLR3_TOKEN_SOURCE src) {
    FosterIndentingTokenSource* s = new FosterIndentingTokenSource;
    s->originalSource = src;
    // Set all the fields required for an ANTLR3_TOKEN_SOURCE.
    s->eofToken   = src->eofToken;
    s->fileName   = src->fileName;
    s->skipToken  = src->skipToken;
    s->strFactory = src->strFactory;
    s->super      = (void*) s;
    s->nextToken  = fosterNextTokenFunc;
    return s;
  }

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

      pANTLR3_TOKEN_SOURCE customSource
                = newFosterIndentingTokenSource(TOKENSOURCE(ctx.lxr));

      ctx.tstream = antlr3CommonTokenStreamSourceNew(ANTLR3_SIZE_HINT,
                                                     customSource);

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
                     ParsingContext* cc) {
    ANTLRContext* ctx = new ANTLRContext();
    const char* s = source.c_str();

    foster::InputTextBuffer* membuf = new InputTextBuffer(s, source.size());
    createParser(*ctx, "", membuf);

    installTreeTokenBoundaryTracker(ctx->psr->adaptor);
    foster::installRecognitionErrorFilter(ctx->psr->pParser->rec);

    ParsingContext::pushContext(cc);

    gInputFile = NULL;
    gInputTextBuffer = membuf;

    fosterParser_expr_return langAST = ctx->psr->expr(ctx->psr);

    outNumANTLRErrors = ctx->psr->pParser->rec->state->errorCount;

    ExprAST* rv = ExprAST_from(langAST.tree);

    // If we reuse the same compilation context again later,
    // we do not want to accidentally pick up an incorrect
    // token boundary if we happen to randomly get the same
    // tree pointer values! Doing so can make ANTLR crash.
    ParsingContext::clearTokenBoundaries();
    ParsingContext::popCurrentContext();

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

    llvm::sys::TimeValue parse_beg = llvm::sys::TimeValue::now();

    fosterParser_program_return langAST = ctx->psr->program(ctx->psr);

    llvm::sys::TimeValue parse_mid = llvm::sys::TimeValue::now();
    outTree = langAST.tree;
    outNumANTLRErrors = ctx->psr->pParser->rec->state->errorCount;

    ModuleAST* m = parseTopLevel(outTree, moduleName);

    llvm::sys::TimeValue parse_end = llvm::sys::TimeValue::now();

    //llvm::outs() << "ANTLR  parsing: " << (parse_mid - parse_beg).msec() << "\n";
    //llvm::outs() << "Foster parsing: " << (parse_end - parse_mid).msec() << "\n";

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
      ParsingContext::setTokenRange((pTree) t, startToken, stopToken);
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
