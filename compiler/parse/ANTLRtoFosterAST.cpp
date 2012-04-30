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

#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/DataTypes.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/FileSystem.h"

#include "city.h"

#include <iostream>
#include <string>
#include <map>
#include <queue>
#include <vector>
#include <sstream>
#include <cassert>

using std::string;

using foster::EDiag;
using foster::show;
using foster::ParsingContext;

#define DEBUG_TYPE "foster"

KindAST* getDefaultKind() { return new BaseKindAST(BaseKindAST::KindType); }
KindAST* getBoxedKind() { return new BaseKindAST(BaseKindAST::KindBoxed); }

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

TypeAST* TypeAST_from(pTree tree);
void display_pTree(pTree t, int nspaces);

size_t getChildCount(pTree tree) {
  return static_cast<size_t>(tree->getChildCount(tree));
}

pTree child(pTree tree, int i) {
  ASSERT(tree) << "can't take child of null pTree!";
  return (pTree) tree->getChild(tree, i);
}

string textOf(pTree tree) {
  ASSERT(tree) << "can't get text of null pTree!";
  return str(tree->getText(tree));
}

string textOfVar(pTree tree) { return textOf(child(tree, 0)); }

int typeOf(pTree tree) { return tree->getType(tree); }

pANTLR3_COMMON_TOKEN getStartToken(pTree tree) {
  if (!tree) return NULL;
  pANTLR3_COMMON_TOKEN tok = ParsingContext::getStartToken(tree);
  if (tok) return tok;

  // Some nodes we're okay with having no token info for...
  /*
  if (getChildCount(tree) == 0) {
    int tag = typeOf(tree);
    if (tag == OUT || tag == IN || tag == BODY
     || tag == ANTLR3_TOKEN_INVALID) {
      return NULL;
    }
  }
  */

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
    llvm::outs() << "Warning: unable to find start token for ANTLR parse tree"
              << " node " << textOf(tree) << " @ " << tree
              << " , " << typeOf(tree) << "\n";
  }
  return tok;
}

pANTLR3_COMMON_TOKEN getEndToken(pTree tree) {
  if (!tree) return NULL;
  pANTLR3_COMMON_TOKEN tok = ParsingContext::getEndToken(tree);
  if (tok) return tok;

  /*
  if (getChildCount(tree) == 0) {
    int tag = typeOf(tree);
    if (tag == OUT || tag == IN || tag == BODY
     || tag == ANTLR3_TOKEN_INVALID) {
      return NULL;
    }
  }
  */

  pTree node = tree;
  while (!tok && getChildCount(node) > 0) {
    node = child(node, getChildCount(node) - 1);
    tok = ParsingContext::getEndToken(node);
  }
  if (!tok) {
    llvm::outs() << "Warning: unable to find end token for ANTLR parse tree"
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


string spaces(int n) { return (n > 0) ? string(n, ' ') : ""; }

void display_pTree(pTree t, int nspaces) {
  if (!t) {
    llvm::outs() << spaces(nspaces) << "<NULL tree>" << "\n";
    return;
  }

  int token = t->getType(t);
  string text = textOf(t);
  int nchildren = getChildCount(t);
  std::stringstream ss;
  ss << spaces(nspaces) << "<" << text << "; ";
  llvm::outs() << ss.str() << spaces(100 - ss.str().size())
                << token << " @ " << t;
  llvm::outs() << " (";
  llvm::outs() << (ParsingContext::getStartToken(t) ? '+' : '-');
  llvm::outs() << (ParsingContext::getEndToken(t)   ? '+' : '-');
  llvm::outs() << ")" << "\n";
  for (int i = 0; i < nchildren; ++i) {
    display_pTree(child(t, i), nspaces+2);
  }
  llvm::outs() << spaces(nspaces) << "/" << text << ">" << "\n";
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

const char* getDefaultCallingConvParse() {
  //foster::EDiag() << "getDefaultCallingConvParse()";
  return foster::kDefaultFnLiteralCallingConvention;
}

////////////////////////////////////////////////////////////////////

IntAST* parseIntFrom(pTree t) {
  ASSERT(textOf(t) == "INT_NUM")
            << "parseIntFrom() called on non-INT_NUM token " << textOf(t)
            << show(rangeOf(t));

  std::stringstream alltext;

  int nchildren = getChildCount(t);
  for (int i = 0; i < nchildren; ++i) {
    alltext << textOf(child(t, i));
  }

  return new IntAST(alltext.str(), rangeOf(t));
}

////////////////////////////////////////////////////////////////////

ExprAST* ExprAST_from(pTree tree);
std::vector<TypeAST*> getTypes(pTree tree);

Exprs getExprs(pTree tree) {
  Exprs f;
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    f.push_back(ExprAST_from(child(tree, i)));
  }
  return f;
}

ExprAST* parseSeq(pTree tree) {
  return new SeqAST(getExprs(tree), rangeOf(tree));
}

ExprAST* parseParenExpr(pTree tree) {
  return ExprAST_from(child(tree, 0));
}

Formal parseFormal(pTree formal) {
  ASSERT(getChildCount(formal) == 2);
  TypeAST* ty = TypeAST_from(child(formal, 1));
  return Formal(textOfVar(child(formal, 0)), ty);
}

KindAST* parseKind(pTree t) {
  switch (typeOf(t)) {
  case KIND_TYPE:       return new BaseKindAST(BaseKindAST::KindType);
  case KIND_TYPE_BOXED: return new BaseKindAST(BaseKindAST::KindBoxed);
  }
  ASSERT(false) << "Unknown kind in parseKind()"; return NULL;
}

void parseFormals(std::vector<Formal>& formals, pTree tree) {
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    formals.push_back(parseFormal(child(tree, i)));
  }
}

TypeFormal parseTypeFormal(pTree t, KindAST* defaultKind) {
  std::string varname = textOfVar(child(t, 0));
  KindAST* kind = (getChildCount(t) == 2)
                ? parseKind(child(t, 1))
                : defaultKind;
  return TypeFormal(varname, kind);
}

// TYPEVAR_DECL name kind?
std::vector<TypeFormal> parseTyFormals(pTree t, KindAST* defaultKind) {
  std::vector<TypeFormal> names;
  for (size_t i = 0; i < getChildCount(t); ++i) {
    names.push_back(parseTypeFormal(child(t, i), defaultKind));
  }
  return names;
}

// ^(VAL_ABS ^(FORMALS formals) ^(MU tyvar_decl*) e_seq?)
ExprAST* parseValAbs(pTree tree) {
  std::vector<Formal> formals;
  parseFormals(formals, child(tree, 0));
  std::vector<TypeFormal> tyVarFormals = parseTyFormals(child(tree, 1),
                                                        getDefaultKind());
  TypeAST* resultType = NULL;
  ExprAST* resultSeq = getChildCount(tree) == 3
                         ? parseSeq(child(tree, 2))
                         : new SeqAST(Exprs(), rangeOf(tree));
  return new ValAbs(formals, tyVarFormals, resultSeq, resultType, rangeOf(tree));
}

ExprAST* parseTuple(pTree t) {
  if (getChildCount(t) == 1) {
    return ExprAST_from(child(t, 0));
  } return new TupleExprAST(getExprs(t), rangeOf(t));
}

Binding parseBinding(pTree tree) {
  return Binding(textOfVar(child(tree, 0)), ExprAST_from(child(tree, 1)));
}

std::vector<Binding> parseBindings(pTree tree) {
  std::vector<Binding> bindings;
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    bindings.push_back(parseBinding(child(tree, i)));
  }
  return bindings;
}

// ^(LETS ^(MU binding+) e_seq)
ExprAST* parseLets(pTree tree) {
  return new LetAST(parseBindings(child(tree, 0)),
                         parseSeq(child(tree, 1)),
                         false, rangeOf(tree));
}

// ^(LETREC ^(MU binding+) e_seq)
ExprAST* parseLetRec(pTree tree) {
  return new LetAST(parseBindings(child(tree, 0)),
                         parseSeq(child(tree, 1)),
                         true,  rangeOf(tree));
}

bool isLexicalOperator(const std::string& text) {
  ASSERT(!text.empty());
  return !isalpha(text[0]); // coincides with fragment IDENT_START
}

VariableAST* parseVarDirect(pTree t) {
  return new VariableAST(textOf(t), NULL, rangeOf(t));
}

std::string parseName(pTree nm) {
  display_pTree(nm, 4);
  if (typeOf(nm) == QNAME) {
    return textOf(child(nm, 0)) + "." + parseName(child(nm, 1));
  } else {
    return textOf(nm);
  }
}

// t = ^(_NAME name)
VariableAST* parseTermVar(pTree t) {
  return new VariableAST(parseName(child(t, 0)), NULL, rangeOf(t));
}

// ^(IF e e_seq e_seq)
ExprAST* parseIf(pTree tree) {
  return new IfExprAST(ExprAST_from(child(tree, 0)),
                       parseSeq(child(tree, 1)),
                       parseSeq(child(tree, 2)),
                       rangeOf(tree));
}

// ^(UNTIL e e_seq)
ExprAST* parseUntil(pTree tree) {
  return new UntilExpr(ExprAST_from(child(tree, 0)),
                       parseSeq(child(tree, 1)),
                       rangeOf(tree));
}

ExprAST* parseRef(pTree tree) {
  return new AllocAST(ExprAST_from(child(tree, 0)), rangeOf(tree));
}

ExprAST* parseBuiltinCompiles(pTree t) {
 return new BuiltinCompilesExprAST(ExprAST_from(child(t, 0)), rangeOf(t));
}

ExprAST* parseBool(pTree t) {
  return new BoolAST(textOf(child(t, 0)), rangeOf(t));
}

std::string contentsOfStringWithQuotes(pTree t) {
  return textOf(child(t, 0));
}

std::string contentsOfStringWithoutQuotes(pTree t) {
  std::string s = contentsOfStringWithQuotes(t);
  if (s.size() >= 6) {
    std::string::const_iterator         i = s.begin();
    std::string::const_reverse_iterator r = s.rbegin();
    if (i[0] == '\'' && i[1] == '\'' && i[2] == '\''
     && r[0] == '\'' && r[1] == '\'' && r[2] == '\'') {
      return std::string(s.begin() + 3, s.end() - 3);
    }
    if (i[0] == '"' && i[1] == '"' && i[2] == '"'
     && r[0] == '"' && r[1] == '"' && r[2] == '"') {
      return std::string(s.begin() + 3, s.end() - 3);
    }
  }

  char f = s[0]; char b = s[s.size() - 1];
  if ((f == '\'' && b == '\'')
    ||(f == '"'  && b == '"')) {
    return std::string(s.begin() + 1, s.end() - 1);
  }

  EDiag() << "Unable to determine what kind of string this is!" << s;
  return s;
}

ExprAST* parseString(pTree t) {
  return new StringAST(contentsOfStringWithQuotes(t), rangeOf(t));
}

Pattern* parsePattern(pTree t);
Pattern* parsePatternAtom(pTree t);

std::vector<Pattern*> noPatterns() { std::vector<Pattern*> f; return f; }

std::vector<Pattern*> getPatterns(pTree tree) {
  std::vector<Pattern*> f;
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    f.push_back(parsePattern(child(tree, i)));
  }
  return f;
}

std::vector<Pattern*> getPatternAtomsFrom1(pTree tree) {
  std::vector<Pattern*> f;
  for (size_t i = 1; i < getChildCount(tree); ++i) {
    f.push_back(parsePatternAtom(child(tree, i)));
  }
  return f;
}

Pattern* parseTuplePattern(pTree t) {
  if (getChildCount(t) == 1) {
    return parsePattern(child(t, 0));
  } return new TuplePattern(rangeOf(t), getPatterns(t));
}

// ^(CTOR x)
VariableAST* parseCtor(pTree t) {
  ASSERT(typeOf(t) == CTOR);
  return parseTermVar(child(t, 0));
}

ExprAST* parseAtom(pTree tree);
Pattern* parsePatternAtom(pTree t) {

  int token = typeOf(t);
  if ((token == PHRASE)
    || (token == TERM)) { ASSERT(false); }

    if (token == CTOR ) { EDiag() << "Ctor text: " << textOfVar(child(t, 0)); return new CtorPattern(rangeOf(t), textOfVar(child(t, 0)), noPatterns()); }
  if (token == WILDCARD) { return new WildcardPattern(rangeOf(t)); }
  if (token == TUPLE)    { return parseTuplePattern(t); }
  if (token == TERMNAME) { return new LiteralPattern(rangeOf(t), LiteralPattern::LP_VAR, parseTermVar(t)); }
  if (token == INT_NUM)  { return new LiteralPattern(rangeOf(t), LiteralPattern::LP_INT, parseAtom(t)); }
  if (token == BOOL   )  { return new LiteralPattern(rangeOf(t), LiteralPattern::LP_BOOL, parseAtom(t)); }
  //if (token == STRING ) { return new LiteralPattern(LiteralPattern::LP_STR, parseAtom(t)); }

  display_pTree(t, 2);
  ASSERT(false) << "returning NULL Pattern for parsePatternAtom token " << str(t->getToken(t));
  return NULL;
}

// ^(MU patom) (may be ctor)
// ^(MU pctor patom*)
Pattern* parsePattern(pTree t) {
  if (getChildCount(t) == 1) {
    return parsePatternAtom(child(t, 0));
  } return new CtorPattern(rangeOf(t), parseCtor(child(t, 0))->getName(),
                           getPatternAtomsFrom1(t));
}

// ^(CASE p e_seq)
CaseBranch parseCaseBranch(pTree t) {
  CaseBranch b = std::make_pair(parsePattern(child(t, 0)),
                                parseSeq(    child(t, 1)));
  return b;
}

// ^(CASE e pmatch+)
ExprAST* parseCase(pTree t) {
  ExprAST* scrutinee = ExprAST_from(child(t, 0));
  std::vector<CaseBranch> branches;
  for (size_t i = 1; i < getChildCount(t); ++i) {
    branches.push_back(parseCaseBranch(child(t, i)));
  }
  return new CaseExpr(scrutinee, branches, rangeOf(t));
}

ExprAST* parseAtom(pTree tree) {
  int token = typeOf(tree);

  if (token == VAL_ABS)  { return parseValAbs(tree); }
  if (token == LETS)     { return parseLets(tree); }
  if (token == LETREC)   { return parseLetRec(tree); }
  if (token == TUPLE)    { return parseTuple(tree); }
  if (token == UNTIL)    { return parseUntil(tree); }
  if (token == TERMNAME) { return parseTermVar(tree); }
  if (token == INT_NUM)  { return parseIntFrom(tree); }
  if (token == IF)       { return parseIf(tree); }
  if (token == REF)      { return parseRef(tree); }
  if (token == COMPILES) { return parseBuiltinCompiles(tree); }
  if (token == CASE)     { return parseCase(tree); }
  if (token == CTOR)     { return parseCtor(tree); }
  if (token == BOOL)     { return parseBool(tree); }
  if (token == STRING)   { return parseString(tree); }

  display_pTree(tree, 2);
  foster::EDiag() << "returning NULL ExprAST for parseAtom token " << str(tree->getToken(tree));
  return NULL;
}

ExprAST* parseSubscript(ExprAST* base, pTree tree) {
  return new SubscriptAST(base, ExprAST_from(child(tree, 0)), rangeOf(tree));
}

ExprAST* parseDeref(ExprAST* base, pTree tree) {
  return new DerefAST(base, rangeOf(tree));
}

// ^(VAL_TYPE_APP t*)
ExprAST* parseValTypeApp(ExprAST* base, pTree tree) {
  std::vector<TypeAST*> types;
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    types.push_back(TypeAST_from(child(tree, i)));
  }
  return new ETypeAppAST(NULL, base, types, rangeOf(tree));
}

// ^(VAL_APP)
ExprAST* parseValApp(ExprAST* base, pTree tree) {
  ASSERT(getChildCount(tree) == 0);
  return new CallAST(base, Exprs(), rangeOf(tree));
}

ExprAST* parseSuffix(ExprAST* base, pTree tree) {
  int token = typeOf(tree);

  if (token == SUBSCRIPT) { return parseSubscript(base, tree); }
  if (token == DEREF)     { return parseDeref(base, tree); }
  if (token == VAL_APP)   { return parseValApp(base, tree); }
  if (token == VAL_TYPE_APP) { return parseValTypeApp(base, tree); }
  display_pTree(tree, 2);
  foster::EDiag() << "returning NULL ExprAST for parseSuffix token " << str(tree->getToken(tree));
  return NULL;
}

// ^(LVALUE atom suffix*)
ExprAST* parseLValue(pTree tree) {
  ExprAST* acc = parseAtom(child(tree, 0));
  for (size_t i = 1; i < getChildCount(tree); ++i) {
     acc = parseSuffix(acc, child(tree, i));
  }
  return acc;
}

// ^(PHRASE lvalue+)
ExprAST* parsePhrase(pTree tree) {
  ExprAST* base = parseLValue(child(tree, 0));
  if (getChildCount(tree) == 1) { return base; }
  Exprs exprs;
  for (size_t i = 1; i < getChildCount(tree); ++i) {
    exprs.push_back(parseLValue(child(tree, i)));
  }
  return new CallAST(base, exprs, rangeOf(tree));
}

ExprAST* parseBinops(pTree tree) {
  display_pTree(tree, 2);
  foster::EDiag() << "returning NULL TypeAST for parseBinops token " << str(tree->getToken(tree));
  return NULL;
}

// Returns the punctuation chars at the start of the given string.
// This isn't quite right in the presence of user-defined operators,
// since we'd want .e.g +++ to behave like +.
std::string oprPrefixOf(std::string s) {
  if (!s.empty() && !ispunct(s[0])) {
    return s; // for "and", "or", etc.
  }
  std::string::iterator b, e;
  b = s.begin(); e = s.end();
  while (b != e && ispunct(*b)) { ++b; }
  return std::string(s.begin(), b);
}

typedef std::pair<VariableAST*, std::string> VarOpPair;

void leftAssoc(std::vector<VarOpPair>& opstack,
               std::vector<ExprAST*>& argstack) {
  ExprAST*  y = argstack.back(); argstack.pop_back();
  ExprAST*  x = argstack.back(); argstack.pop_back();
  VarOpPair p =  opstack.back();  opstack.pop_back();
  const std::string& o = p.second;

  if (o == ">^") {
    // TODO move this switch to desugaring in me.
    argstack.push_back(new StoreAST(x, y, rangeFrom(x, y)));
  } else {
    Exprs exprs;
    exprs.push_back(x);
    exprs.push_back(y);
    argstack.push_back(new CallAST(p.first, exprs, rangeFrom(x, y)));
  }
}

ExprAST* parseBinopChain(ExprAST* first, pTree binOpPairs) {
  if (getChildCount(binOpPairs) == 0) {
    return first;
  }

  std::vector< std::pair<VarOpPair, ExprAST*> > pairs;

  for (size_t i = 0; i < getChildCount(binOpPairs); i += 2) {
    pairs.push_back(std::make_pair(
                     VarOpPair(parseVarDirect(child(binOpPairs, i)),
                           oprPrefixOf(textOf(child(binOpPairs, i)))),
                     parsePhrase(child(binOpPairs, i + 1))));
  }

  std::vector<VarOpPair> opstack;
  std::vector<ExprAST*> argstack;
  argstack.push_back(first);
  argstack.push_back(pairs[0].second);
  opstack.push_back(pairs[0].first);

  for (size_t i = 1; i < pairs.size(); ++i) {
    while (!opstack.empty()) {
      const std::string& top = opstack.back().second;
      const std::string& opd = pairs[i].first.second;
      foster::OperatorPrecedenceTable::OperatorRelation rel =
                           ParsingContext::getOperatorRelation(top, opd);
      if (rel != foster::OperatorPrecedenceTable::kOpBindsTighter) {
        break;
      }
      leftAssoc(opstack, argstack);
    }

    argstack.push_back(pairs[i].second);
    opstack.push_back( pairs[i].first);
  }

  while (!opstack.empty()) {
    leftAssoc(opstack, argstack);
  }

  ASSERT(argstack.size() == 1);
  return argstack[0];
}

// ^(TERM ^(MU opr?) ^(MU phrase) ^(MU binops?))
ExprAST* parseTerm(pTree tree) {
  pTree pTmaybeOpr = child(tree, 0);
  pTree pTphrase   = child(tree, 1);
  pTree pTmaybeBin = child(tree, 2);
  ExprAST* base = parsePhrase(child(pTphrase, 0));

  if (getChildCount(pTmaybeOpr) > 0) {
    VariableAST* opvar = parseTermVar(pTmaybeOpr);
    // TODO move this check so it is caught by __COMPILES__
    ASSERT(opvar->getName() == "-")
                       << "For now, only unary - is allowed, not unary "
                       << "'" << opvar->getName() << "'"
                       << show(rangeOf(pTmaybeOpr));
    // If we have            - f x y (+ ...) ...,
    // interpret this as ((-) (f x y)) (+ ...) ...
    std::vector<ExprAST*> exprs; exprs.push_back(base);
    base = new CallAST(opvar, exprs, rangeFrom(pTmaybeOpr, pTphrase));
  }

  return parseBinopChain(base, pTmaybeBin);
}

ExprAST* ExprAST_from(pTree tree) {
  if (!tree) return NULL;

  int token = typeOf(tree);
  string text = textOf(tree);
  foster::SourceRange sourceRange = rangeOf(tree);

  if (token == TERM) { return parseTerm(tree); }

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
  ASSERT(false) << "returning NULL ExprAST for ExprAST_from token " << name
                  << "with text '" << text << "'"
                  << foster::show(sourceRange);
  return NULL;
}

TypeAST* parseTypeAtom(pTree tree);

// ^(OF dctor tatom*)
DataCtorAST* parseDataCtor(pTree t) {
  //foster::SourceRange sourceRange = rangeOf(t);
  DataCtorAST* c = new DataCtorAST();
  c->name = parseCtor(child(t, 0))->getName();
  for (size_t i = 1; i < getChildCount(t); ++i) {
    c->types.push_back(parseTypeAtom(child(t, i)));
  }
  return c;
}

// ^(MU data_ctor*)
std::vector<DataCtorAST*> parseDataCtors(pTree t) {
  std::vector<DataCtorAST*> ctors;
  for (size_t i = 0; i < getChildCount(t); ++i) {
    ctors.push_back(parseDataCtor(child(t, i)));
  }
  return ctors;
}

ModuleAST* parseTopLevel(pTree root_tree, std::string moduleName,
                         std::string hash,
                         std::queue<std::pair<string, string> >& out_imports) {
  // The top level is composed of declarations and definitions.
  std::vector<Decl*> decls;
  std::vector<Defn*> defns;
  std::vector<Data*> datas;

  pTree imports = child(root_tree, 0);
  for (size_t i = 0; i < getChildCount(imports); ++i) {
    pTree imp = child(imports, i);
    std::string imp_name = textOf(child(imp, 0));
    std::string imp_text = contentsOfStringWithoutQuotes(child(imp, 1));
    out_imports.push(std::make_pair(imp_name, imp_text));
  }

  for (size_t i = 1; i < getChildCount(root_tree); ++i) {
    pTree c = child(root_tree, i);
    int token = typeOf(c);

    if (token == DEFN) { // ^(DEFN x atom)
      string name = textOfVar(child(c, 0));
      ExprAST* atom = parseAtom(child(c, 1));
      defns.push_back(new Defn(name, atom));

      if (ValAbs* fn = dynamic_cast<ValAbs*>(atom)) { fn->name = name; }
    } else if (token == DECL) {
      pTree typevar = child(c, 0);
      pTree type    = child(c, 1);
      decls.push_back(new Decl(textOfVar(typevar), TypeAST_from(type)));
    } else if (token == DATATYPE) { // ^(DATATYPE id ^(MU tyvar_decl*) ^(MU data_ctor*)
      datas.push_back(new Data(textOf(child(c, 0)),
                      parseTyFormals(child(c, 1), getBoxedKind()),
                      parseDataCtors(child(c, 2))));
    } else {
      EDiag() << "ANTLRtoFosterAST.cpp: "
              << "Unexpected top-level element with token ID " << token;
      display_pTree(c, 8);
      display_pTree(root_tree, 4);
      EDiag() << show(rangeOf(c));
    }
  }
  return new ModuleAST(decls, defns, datas, moduleName, hash);
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

// ^(FUNC_TYPE t+)
// ^(BINDING binding+)
void parseAnnots(std::map<string, string>& annots,
                 pTree tree) {
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    Binding b = parseBinding(child(tree, i));
    string  k = b.name;
    string  v;

    if (VariableAST* q = dynamic_cast<VariableAST*>(b.body)) {
      v = q->getName();
    } else
    if (IntAST* q = dynamic_cast<IntAST*>(b.body)) {
      v = q->getOriginalText();
    } else
    if (BoolAST* q = dynamic_cast<BoolAST*>(b.body)) {
      v = q->boolValue ? "true" : "false";
    }

    if (v == "") {
      EDiag() << "Annotation failed to parse value string from "
              << string(b.body->tag) << show(b.body);
    } else {
      annots[k] = v;
    }
  }
}

// ^(FUNC_TYPE ^(TUPLE t+) tannots?)
TypeAST* parseFuncType(pTree tree) {
  std::vector<TypeAST*> types = getTypes(child(tree, 0));
  TypeAST* rt = types.back(); types.pop_back();

  std::map<string, string> annots;
  if (getChildCount(tree) == 2) {
    parseAnnots(annots, child(tree, 1));
  }

  // Lambdas default to fastcc, procs default to ccc.
  bool isProc = annots.find("proc") != annots.end()
             && annots["proc"] == "true";
  if (annots["callconv"] == "") {
    annots["callconv"] = isProc ? "ccc" : "fastcc";
  }
  return new FnTypeAST(rt, types, annots);
}

// ^(TYPEVAR a)
NamedTypeAST* parseTypeVar(pTree tree) {
  TypeAST* ty = NULL;
  return new NamedTypeAST(textOf(child(tree, 0)), ty, rangeOf(tree));
}

// ^(TYPE_PLACEHOLDER ^(TYPEVAR a))
TypeAST* parseTypePlaceholder(pTree tree) {
  NamedTypeAST* tv = parseTypeVar(child(tree, 0));
  tv->is_placeholder = true;
  return tv;
}

TypeAST* parseTupleType(pTree tree) {
  if (getChildCount(tree) == 1) {
    return TypeAST_from(child(tree, 0));
  } else {
    return TupleTypeAST::get(getTypes(tree));
  }
}

TypeAST* parseTypeAtom(pTree tree) {
  int token = typeOf(tree);

  if (token == FUNC_TYPE) { return parseFuncType(tree); }
  if (token == TUPLE)     { return parseTupleType(tree); }
  if (token == TYPENAME)  { return parseTypeVar(tree); }
  if (token == TYPE_PLACEHOLDER) { return parseTypePlaceholder(tree); }

  display_pTree(tree, 2);
  ASSERT(false) << "parseTypeAtom";
  return NULL;
}

std::vector<TypeAST*> getTypes(pTree tree) {
  std::vector<TypeAST*> types;
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    TypeAST* ast = TypeAST_from(child(tree, i));
    ASSERT(ast != NULL) << "getTypes: parsing type " << i;
    types.push_back(ast);
  }
  return types;
}

std::vector<TypeAST*> getTypeAtoms(pTree tree) {
  std::vector<TypeAST*> types;
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    TypeAST* ast = parseTypeAtom(child(tree, i));
    ASSERT(ast != NULL) << "getTypeAtoms: parsing type atom " << i;
    types.push_back(ast);
  }
  return types;
}

// ^(TYPE_TYP_APP tatom tatom+)
TypeAST* parseTypeTypeApp(pTree tree) {
  return TypeTypeAppAST::get(getTypeAtoms(tree));
}

// ^(FORALL_TYPE tyformal+ t)
TypeAST* parseForallType(pTree tree) {
  std::vector<TypeFormal> tyformals;
  for (size_t i = 0; i < getChildCount(tree) - 1; ++i) {
    tyformals.push_back(parseTypeFormal(child(tree, i), getBoxedKind()));
  }
  return new ForallTypeAST(tyformals,
                           TypeAST_from(child(tree, getChildCount(tree) - 1)),
                           rangeOf(tree));
}

TypeAST* TypeAST_from(pTree tree) {
  if (!tree) return NULL;

  int token = typeOf(tree);
  string text = textOf(tree);
  foster::SourceRange sourceRange = rangeOf(tree);

  if (token == TYPE_ATOM)    { return parseTypeAtom(child(tree, 0)); }
  if (token == TYPE_TYP_APP) { return parseTypeTypeApp(tree); }
  if (token == FORALL_TYPE)  { return parseForallType(tree); }

  string name = str(tree->getToken(tree));
  foster::EDiag() << "returning NULL TypeAST for tree token " << name
                  << foster::show(sourceRange);
  return NULL;
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

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
    uint128 getMemoryBufferHash(llvm::MemoryBuffer* buf) {
      return CityHash128(buf->getBufferStart(), buf->getBufferSize());
    }

    uint128 getFileHash(const InputFile& file) {
      return getMemoryBufferHash(file.getBuffer()->getMemoryBuffer());
    }

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

  void parseModule(WholeProgramAST* pgm,
                   const foster::InputFile& file,
                   unsigned* outNumANTLRErrors,
                   std::queue<std::pair<string, string> >& out_imports) {
    uint128 hash = getFileHash(file);
    if (pgm->seen.count(hash) == 1) {
      return;
    }
    char hashcstr[33] = {0};
    sprintf(hashcstr, "%08" PRIx64 "%08" PRIx64,
                     Uint128Low64(hash), Uint128High64(hash));
    std::string hashstr(hashcstr);
    printf("Hash of file %s is %s\n", file.getShortName().c_str(), hashcstr);

    ANTLRContext* ctx = new ANTLRContext();
    createParser(*ctx, file);

    installTreeTokenBoundaryTracker(ctx->psr->adaptor);
    foster::installRecognitionErrorFilter(ctx->psr->pParser->rec);

    gInputFile = &file; // used when creating source ranges
    gInputTextBuffer = file.getBuffer(); // also used for source ranges

    fosterParser_module_return langAST = ctx->psr->module(ctx->psr);
    *outNumANTLRErrors += ctx->psr->pParser->rec->state->errorCount;

    ModuleAST* m = parseTopLevel(langAST.tree, file.getShortName(), hashstr, out_imports);
    m->buf = file.getBuffer();

    pgm->seen[hash] = m;
    pgm->modules.push_back(m);
  }


  foster::InputFile* resolveModulePath(const std::string& searchPath,
                                       const std::string& spath);

  WholeProgramAST* parseWholeProgram(const InputFile& startfile,
                                     const std::string& searchPath,
                                     unsigned* outNumANTLRErrors) {
    WholeProgramAST* pgm = new WholeProgramAST();
    *outNumANTLRErrors = 0;

    //llvm::sys::TimeValue parse_beg = llvm::sys::TimeValue::now();
    std::queue<std::pair<string, string> > pending_imports;
    parseModule(pgm, startfile, outNumANTLRErrors, pending_imports);

    while (*outNumANTLRErrors == 0 && !pending_imports.empty()) {
      std::pair<string, string> imp = pending_imports.front();
                                      pending_imports.pop();
      std::string localname = imp.first;
      std::string imp_path  = imp.second;
      std::cout << "pending import: " << imp.first << " " << imp.second << std::endl;
      if (foster::InputFile* f = resolveModulePath(searchPath, imp_path)) {
        parseModule(pgm, *f, outNumANTLRErrors, pending_imports);
      } else {
        EDiag() << "Unable to resolve import path: " << imp_path;
        return NULL;
      }
    }

    //llvm::sys::TimeValue parse_end = llvm::sys::TimeValue::now();
    //llvm::outs() << "ANTLR  parsing: " << (parse_mid - parse_beg).msec() << "\n";
    //llvm::outs() << "Foster parsing: " << (parse_end - parse_mid).msec() << "\n";

    return pgm;
  }

  // spath will be something like "foo/bar"
  // We'll want to check for searchPath/foo/bar/bar.foster
  foster::InputFile* resolveModulePath(const std::string& searchPath,
                                       const std::string& spath) {
    llvm::SmallString<256> path;

    if (searchPath.empty()) {
      llvm::sys::path::append(path, ".");
    } else {
      llvm::sys::path::append(path, searchPath);
    }

    llvm::sys::path::append(path, spath);
    llvm::sys::path::append(path, llvm::sys::path::stem(spath));
    llvm::sys::path::replace_extension(path, "foster");
    if (llvm::sys::fs::exists(path.str())) {
      llvm::sys::Path fpath(path.str());
      return new foster::InputFile(fpath);
    } else {
      return NULL;
    }
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
