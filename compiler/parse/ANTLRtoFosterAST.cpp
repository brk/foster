// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/InputFile.h"
#include "base/InputTextBuffer.h"

#include "parse/ANTLRtoFosterAST.h"
#include "parse/FosterAST.h"
#include "parse/ANTLRtoFosterErrorHandling.h"
#include "parse/CompilationContext.h"

#include "_generated_/fosterLexer.h"
#include "_generated_/fosterParser.h"

#include "pystring/pystring.h"

#include "llvm/Support/MemoryBuffer.h"
#include "llvm/ADT/APInt.h"

#include <iostream>
#include <string>
#include <map>
#include <vector>
#include <sstream>
#include <cassert>

using std::string;
using std::endl;
using std::cout;
using std::cerr;

using foster::TypeASTFor;
using foster::LLVMTypeFor;
using foster::EDiag;
using foster::show;

namespace foster {
std::string gPendingModuleName;
}

// {{{ ANTLR stuff
std::string str(pANTLR3_STRING pstr) {
  return string((const char*)pstr->chars);
}

std::string stringTreeFrom(pTree parseTree) {
  return str(parseTree->toStringTree(parseTree));
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

/////////////////////////////////////////////////////////////////////

void display_pTree(pTree t, int nspaces);
ExprAST* ExprAST_from(pTree tree, bool infn);
// }}}

namespace {

typedef void                  (*setTokenBoundariesFunc)
(struct ANTLR3_BASE_TREE_ADAPTOR_struct * adaptor, void * t,
 pANTLR3_COMMON_TOKEN startToken, pANTLR3_COMMON_TOKEN stopToken);

static setTokenBoundariesFunc sgDefaultSTB;

static void customSetTokenBoundariesFunc
(struct ANTLR3_BASE_TREE_ADAPTOR_struct * adaptor, void * t,
 pANTLR3_COMMON_TOKEN startToken, pANTLR3_COMMON_TOKEN stopToken) {
  sgDefaultSTB(adaptor, t, startToken, stopToken);

  foster::CompilationContext* cc = foster::gCompilationContexts.top();
  cc->startTokens[(pTree)t] = startToken;
  cc->  endTokens[(pTree)t] =  stopToken;
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

size_t getChildCount(pTree tree) {
  return static_cast<size_t>(tree->getChildCount(tree));
}

string textOf(pTree tree) {
  if (!tree) {
    cerr << "Error! Can't get text of a null node!" << endl;
    return "<NULL pTree>";
  }
  return str(tree->getText(tree));
}

pTree child(pTree tree, int i) {
  if (!tree) {
    cerr << "Error! Can't take child of null pTree!" << endl;
    return NULL;
  }
  return (pTree) tree->getChild(tree, i);
}

int typeOf(pTree tree) { return tree->getType(tree); }

pANTLR3_COMMON_TOKEN getStartToken(pTree tree) {
  if (!tree) return NULL;
  pANTLR3_COMMON_TOKEN tok = foster::gCompilationContexts.top()->
                                startTokens[tree];
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
    tok = foster::gCompilationContexts.top()->startTokens[node];
  }
  if (!tok) {
    cout << "Warning: unable to find start token for ANTLR parse tree"
              << " node " << textOf(tree) << " @ " << tree
              << " , " << typeOf(tree) << endl;
  }
  return tok;
}

pANTLR3_COMMON_TOKEN getEndToken(pTree tree) {
  if (!tree) return NULL;
  pANTLR3_COMMON_TOKEN tok = foster::gCompilationContexts.top()->
                                endTokens[tree];
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
    tok = foster::gCompilationContexts.top()->endTokens[node];
  }
  if (!tok) {
    cout << "Warning: unable to find end token for ANTLR parse tree"
              << " node " << textOf(tree) << " @ " << tree << endl;
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
  if (false && (!stok || !etok)) {
    cout << "rangeFrom " << start << " => " << stok << " ;; "
              << end << " => " << etok << endl;
    if (!stok) { display_pTree(start, 2); }
    if (!etok) { display_pTree(  end, 2); }
  }
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

Exprs getExprs(pTree tree, bool fnMeansClosure);

// expressions wrapped in () are marked here
std::map<ExprAST*, bool> gWasWrappedInExplicitParens;

bool foster::wasExplicitlyParenthesized(ExprAST* ast) {
  return gWasWrappedInExplicitParens[ast];
}

std::map<string, bool> keywords;
std::map<string, bool> reserved_keywords;

const char* c_keywords[] = {
  "as" , "at" , "def" , "id", "in", "is", "it", "to",
  "given" , "false" , "if" , "match" , "do" , "new" , "nil",
  "gives" , "and" , "or" , "true" , "var" , "while",
  "for", "ref", "?ref"
};
const char* c_reserved_keywords[] = {
  "def", "catch", "lazy", "object", "package", "private",
  "protected", "return", "throw", "trait", "try", "type",
  "val", "with", "yield", "except"
};

bool isUnaryOp(const string& op) {
  return op == "-" || op == "not";
}

#ifndef ARRAY_SIZE
#define ARRAY_SIZE(a) (sizeof(a)/sizeof(((a)[0])))
#endif

bool isSpecialName(const string& op) {
  return op == "deref" || isBitwiseOpName(op);
}

bool isBitwiseOpName(const string& op) {
  return op == "bitand" || op == "bitor" || op == "bitxor" ||
         op == "bitshl" || op == "bitlshr" || op == "bitashr";
}

void initMaps() {
  static bool didInit = false;
  if (didInit) return;
  didInit = true;
  
  for (size_t i = 0; i < ARRAY_SIZE(c_keywords); ++i) {
    keywords[c_keywords[i]] = true;
  }

  for (size_t i = 0; i < ARRAY_SIZE(c_reserved_keywords); ++i) {
    reserved_keywords[c_reserved_keywords[i]] = true;
  }
}

string spaces(int n) { return string(n, ' '); }

void display_pTree(pTree t, int nspaces) {
  if (!t) {
    cout << spaces(nspaces) << "<NULL tree>" << endl;
    return;
  }

  int token = t->getType(t);
  string text = textOf(t);
  int nchildren = getChildCount(t);
  std::stringstream ss;
  ss << spaces(nspaces) << "<" << text << "; ";
  cout << ss.str() << spaces(70 - ss.str().size())
            << token << " @ " << t;
  cout << " (";
  cout << (foster::gCompilationContexts.top()->startTokens[t] ? '+' : '-');
  cout << (foster::gCompilationContexts.top()->  endTokens[t] ? '+' : '-');
  cout << ")" << endl;
  for (int i = 0; i < nchildren; ++i) {
    display_pTree(child(t, i), nspaces+2);
  }
  cout << spaces(nspaces) << "/" << text << ">" << endl;
}

void dumpANTLRTreeNode(std::ostream& out, pTree tree, int depth) {
  out << string(depth, ' ');
  out << "text:"<< str(tree->getText(tree)) << " ";
  out << "line:"<< tree->getLine(tree) << " ";
  out << "charpos:"<< tree->getCharPositionInLine(tree) << " ";
  out << std::endl;
}

void dumpANTLRTree(std::ostream& out, pTree tree, int depth) {
  int nchildren = tree->getChildCount(tree);
  out << "nchildren:" << nchildren << std::endl;
  for (int i = 0; i < nchildren; ++i) {
    dumpANTLRTree(out, (pTree) tree->getChild(tree, i), depth + 1);
  }
  dumpANTLRTreeNode(out, tree, depth);
}

namespace foster {
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

IntAST* parseIntFrom(pTree t) {
  SourceRange sourceRange = rangeOf(t);

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

/// Returns ast if ast may be valid as the LHS of an assign expr, else NULL.
/// Valid forms for the LHS of an assign expr are:
/// * Variables (presumably to a ref)
/// * Subscripts
/// * Lookups (eventually)
ExprAST* validateAssignLHS(ExprAST* ast) {
  if (VariableAST* var = dynamic_cast<VariableAST*>(ast)) { return ast; }
  if (SubscriptAST* var = dynamic_cast<SubscriptAST*>(ast)) { return ast; }
  return NULL;
}

VariableAST* parseFormal(pTree tree, bool fnMeansClosure) {
  // ^(FORMAL ^(NAME varName) ^(... type ... ))
  pTree varNameTree = child(tree, 0);
  if (!varNameTree) {
    cerr << "Error! Null var name in parseFormal..." << endl;
    display_pTree(tree, 4);
    return NULL;
  }
  string varName = textOf(child(varNameTree, 0));
  if (getChildCount(tree) == 2) {
    TypeAST* tyExpr = TypeAST_from(child(tree, 1));
    if (tyExpr) {
      if (0) cout << "\tParsed formal " << varName
                << " with type expr " << str(tyExpr) << endl;
    } else {
      if (0) cout << "\tParsed formal " << varName
                       << " with null type expr " << endl;
    }
    VariableAST* var = new VariableAST(varName, tyExpr, rangeOf(tree));
    gScope.insert(varName, new foster::SymbolInfo(var));
    return var;
  } else {
    // no fixed type, infer later
    VariableAST* var = new VariableAST(varName, NULL, rangeOf(tree));
    gScope.insert(varName, new foster::SymbolInfo(var));
    return var;
  }
}

std::vector<VariableAST*> getFormals(pTree tree, bool fnMeansClosure) {
  std::vector<VariableAST*> args;
  if (textOf(tree) == "FORMAL") {
    args.push_back(parseFormal(tree, fnMeansClosure));
  } else {
    for (size_t i = 0; i < getChildCount(tree); ++i) {
       args.push_back(parseFormal(child(tree, i), fnMeansClosure));
    }
  }
  return args;
}

PrototypeAST* getFnProto(string name,
                         bool fnMeansClosure,
                         pTree formalsTree,
                         pTree retTyExprTree)
{
  foster::SymbolTable<foster::SymbolInfo>::LexicalScope* protoScope =
                                    gScope.pushScope("fn proto " + name);
    std::vector<VariableAST*> in = getFormals(formalsTree, fnMeansClosure);
    TypeAST* retTy = TypeAST_from(retTyExprTree);
  gScope.popScope();

  pTree sourceEndTree = (retTyExprTree != NULL) ? retTyExprTree : formalsTree;
  foster::SourceRange sourceRange = rangeFrom(formalsTree, sourceEndTree);
  PrototypeAST* proto = new PrototypeAST(retTy, name, in, protoScope,
                              sourceRange);

  gScope.getRootScope()->insert(name, new foster::SymbolInfo(proto));

  return proto;
}

FnAST* buildFn(PrototypeAST* proto, pTree bodyTree) {
  ExprAST* body = NULL;
  gScope.pushExistingScope(proto->scope);
    body = ExprAST_from(bodyTree, true);
  gScope.popExistingScope(proto->scope);

  // TODO make source range more accurate
  return new FnAST(proto, body, rangeOf(bodyTree));
}

// parses    a  op  b...c
ExprAST* parseBinaryOpExpr(
    const std::string& opname, ExprAST* a, ExprAST* bc) {

  if (BinaryOpExprAST* rhs = dynamic_cast<BinaryOpExprAST*>(bc)) {
    // ExprAST_from strips parens from expressions; instead of recording their
    // presence in the original source in the ExprAST, we store parenthesized
    // AST nodes in a separate table.
    if (wasExplicitlyParenthesized(rhs)) {
      // Can't split the RHS up; no choice but to return op(a, (b...c))
      goto done;
    }

    ExprAST* b = rhs->parts[rhs->kLHS];
    ExprAST* c = rhs->parts[rhs->kRHS];
    std::string rop = rhs->op;

    // a opname b rop c
    foster::OperatorPrecedenceTable::OperatorRelation rel =
	    foster::gCompilationContexts.top()->prec.get(opname, rop);
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

FnAST* parseFn(string defaultSymbolTemplate, pTree tree, bool fnMeansClosure) {
  // (FN 0:NAME 1:IN 2:OUT 3:BODY)
  string name = parseFnName(defaultSymbolTemplate, tree);
  PrototypeAST* proto = getFnProto(name, fnMeansClosure,
                                   child(tree, 1),
                                   child(tree, 2));
  //cout << "parseFn proto = " << str(proto) << endl;
  return buildFn(proto, child(tree, 3));
}

// ExprAST_from() is straight-up recursive, and uses gScope and gTypeScope
// to keep track of lexical scoping for variables and types, respectively.
// This works wonderfully for function bodies, where variables must appear
// in topologically sorted order. In order to allow functions at the top-level
// to appear in unsorted order, we have to separate the extraction of function
// prototypes (and insertion of said name/proto pair into the gScope symbol
// table) from the actual parsing of the function body.
ModuleAST* parseTopLevel(pTree tree) {
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
      ExprAST* typeDefn = ExprAST_from(c, false);
      parsedExprs[i] = typeDefn;
    } else if (token == FNDEF) {
      ASSERT(getChildCount(c) == 2);
      // x = fn { blah }   ===   x = fn "x" { blah }
      pTree lval = (child(c, 0));
      pTree rval = (child(c, 1));
      if (typeOf(lval) == NAME && typeOf(rval) == FN) {
        // (FN 0:NAME 1:IN 2:OUT 3:BODY)
        string name = parseFnName(textOf(child(lval, 0)), rval);
        protos[c] = getFnProto(name, true, child(rval, 1), child(rval, 2));
      } else {
        EDiag() << "not assigning top-level function to a name?"
                << show(rangeOf(c));
      }
      // parsedExprs[i] remains NULL
    } else if (token == FN) {
      // (FN 0:NAME 1:IN 2:OUT 3:BODY)
      string name = parseFnName(textOf(child(c, 0)), c);
      protos[c] = getFnProto(name, true, child(c, 1), child(c, 2));
      // parsedExprs[i] remains NULL
    } else {
      ExprAST* otherExpr = ExprAST_from(c, false);
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

  std::string moduleName(foster::gPendingModuleName);
  if (moduleName.empty()) {
    moduleName = "<default_foster_module>";
  }

  return new ModuleAST(parsedExprs,
                       moduleName,
                       gScope.getRootScope(),
                       rangeOf(tree));
}

ExprAST* parseTypeDefinition(pTree tree, bool fnMeansClosure) {
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

  cout << "Associated " << name << " with type " << str(tyExpr) << endl;
  return new NamedTypeDeclAST(name, tyExpr, rangeOf(tree));
}

ExprAST* parseForRange(pTree tree, bool fnMeansClosure,
                       const SourceRange& sourceRange) {
  pTree varNameTree = child(tree, 0);
  string varName = textOf(child(varNameTree, 0));
  VariableAST* var = new VariableAST(varName,
                                     TypeAST::i(32),
			                         rangeOf(varNameTree));
  ExprAST* start = ExprAST_from(child(tree, 1), fnMeansClosure);
  ExprAST* end   = ExprAST_from(child(tree, 2), fnMeansClosure);
  ExprAST* incr  = NULL;

  if (getChildCount(tree) >= 5) {
    incr = ExprAST_from(child(tree, 4), fnMeansClosure);
  }

  gScope.pushScope("for-range " + varName);
  gScope.insert(varName, new foster::SymbolInfo(var));
  ExprAST* body  = ExprAST_from(child(tree, 3), fnMeansClosure);
  gScope.popScope();

  cout << "for (" << varName <<" in _ to _ ...)" << endl;
  return new ForRangeExprAST(var, start, end, body, incr, sourceRange);
}

// ^(CTOR ^(NAME blah) ^(SEQ ...))
ExprAST* parseCtorExpr(pTree tree, bool fnMeansClosure,
                       const foster::SourceRange& sourceRange) {
  pTree nameNode = child(tree, 0);
  pTree seqArgs = child(tree, 1);

  string name = textOf(child(nameNode, 0));
  if (name == "simd-vector") {
    return new SimdVectorAST(ExprAST_from(seqArgs, fnMeansClosure), sourceRange);
  }
#if 0
  if (name == "array") {
    return new ArrayExprAST(ExprAST_from(seqArgs, fnMeansClosure), sourceRange);
  }
#endif
  if (name == "tuple") {
    return new TupleExprAST(ExprAST_from(seqArgs, fnMeansClosure), sourceRange);
  }

#if 0
  if (TypeAST* ty = gTypeScope.lookup(name, "")) {
    ASSERT(ty->getLLVMType() && ty->getLLVMType()->isStructTy());
    return new TupleExprAST(ExprAST_from(seqArgs, fnMeansClosure),
                            name, sourceRange);
  }
#endif

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
  if (name == "simd-vector") {
    // e.g. simd-vector of 4 i32
    TypeAST* size = TypeAST_from(child(seqArgs, 0));
    TypeAST* type = TypeAST_from(child(seqArgs, 1));
    if (LiteralIntValueTypeAST* litsize =
                                 dynamic_cast<LiteralIntValueTypeAST*>(size)) {
      return SimdVectorTypeAST::get(litsize, type, sourceRange);
    } else {
      EDiag() << "simd-vector type must be parameterized by a literal int size"
              << show(rangeOf(child(seqArgs, 0)));
      return NULL;
    }
  }
  if (name == "array") {
    foster::EDiag() << "array types not yet supported!"
                    << foster::show(sourceRange);
    //return new ArrayTypeAST(TypeAST_from(seqArgs), sourceRange);
    return NULL;
  }
  if (name == "tuple") {
    return TupleTypeAST::get(getTypes(seqArgs)); //, sourceRange);
  }

  if (TypeAST* ty = gTypeScope.lookup(name, "")) {
    return ty; // TODO fix
  }

  foster::EDiag() << "CTOR type parsing found unknown"
                  << " type name '" << name << "'"
                  << foster::show(sourceRange);
  return NULL;
}

ExprAST* ExprAST_from(pTree tree, bool fnMeansClosure) {
  if (!tree) return NULL;

  int token = typeOf(tree);
  string text = textOf(tree);
  foster::SourceRange sourceRange = rangeOf(tree);

  if (token == TYPEDEFN) {
    return parseTypeDefinition(tree, fnMeansClosure);
  }

  if (token == TRAILERS) {
    ASSERT(getChildCount(tree) >= 2);
    // name (args) ... (args)
    ExprAST* prefix = ExprAST_from(child(tree, 0), fnMeansClosure);
    for (size_t i = 1; i < getChildCount(tree); ++i) {
      int trailerType = typeOf(child(tree, i));
      if (trailerType == CALL) {
        Exprs args = getExprs(child(tree, i), fnMeansClosure);

        // Two different things can parse as function calls: normal function
        // calls, and function-call syntax for built-in bitwise operators.
        VariableAST* varPrefix = dynamic_cast<VariableAST*>(prefix);
        if (varPrefix) {
          if (varPrefix->name == "deref") {
            if (args.size() != 1) {
              cerr << "Error! Deref operator called with "
                        << " bad number of args: " << args.size() << endl;
              return NULL;
            }
            prefix = new DerefExprAST(args[0], sourceRange);
            continue;
          }

          if (isBitwiseOpName(varPrefix->name)) {
            if (args.size() != 2) {
              cerr << "Error! Bitwise operator " << varPrefix->name
                        << " with bad number of arguments: " << args.size()
                        << endl;
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
        prefix = prefix->lookup(name, "");
        if (!prefix) {
          cerr << "Lookup of name '" << name << "' failed." << endl;
        }
      } else if (trailerType == SUBSCRIPT) {
        prefix = new SubscriptAST(prefix,
                                  ExprAST_from(child(child(tree, i), 0),
                                               fnMeansClosure),
                                  sourceRange);
      } else {
        cerr << "Unknown trailer type " << textOf(child(tree, i)) << endl;
      }
    }
    return prefix;
  }

  if (token == BODY) { // usually contains SEQ
    return ExprAST_from(child(tree, 0), fnMeansClosure);
  }

  // <var start end body incr?>
  if (token == FORRANGE) {
    return parseForRange(tree, fnMeansClosure, sourceRange);
  }

  // <LHS RHS>
  if (token == SETEXPR) {
    ExprAST* lhs = validateAssignLHS(
                       ExprAST_from(child(tree, 0), fnMeansClosure));
    if (!lhs) {
      cerr << "Error! Invalid syntactic form on LHS of assignment;" <<
          " must be variable or subscript expr" << endl;
      return NULL;
    }
    ExprAST* rhs = ExprAST_from(child(tree, 1), fnMeansClosure);
    return new AssignExprAST(lhs, rhs, sourceRange);
  }

  // <formal arg (body | next) [type]>
  if (token == LETEXPR) {
    pTree tyExprTree = NULL;
    if (getChildCount(tree) == 4) {
      tyExprTree = child(tree, 3);
    }

    PrototypeAST* proto = getFnProto(freshName("<anon_fnlet_%d>"),
                                     fnMeansClosure,
                                     child(tree, 0),
                                     tyExprTree);
    FnAST* fn = buildFn(proto, child(tree, 2));
    fn->lambdaLiftOnly = true;

    ExprAST* a = ExprAST_from(child(tree, 1), fnMeansClosure);
    Exprs args; args.push_back(a);
    return new CallAST(fn, args, sourceRange);
  }

  if (token == EXPRS || token == SEQ) {
    Exprs exprs;
    for (size_t i = 0; i < getChildCount(tree); ++i) {
      ExprAST* ast = ExprAST_from(child(tree, i), fnMeansClosure);
      if (ast != NULL) {
        exprs.push_back(ast);
      }
    }
    return new SeqAST(exprs, sourceRange);
  }

  if (token == INT) {
    IntAST* ast = parseIntFrom(tree);
    if (ast) {
      return ast;
    } else {
      cout << "Could not parse int!"; // TODO improve error message
      return NULL;
    }
  }

  if (token == CTOR) {
    return parseCtorExpr(tree, fnMeansClosure, sourceRange);
  }

  if (token == NAME) {
    string varName = textOf(child(tree, 0));

    // Don't bother trying to look up special variable names,
    // since we'll end up discarding this variable soon anyways.
    if (isSpecialName(varName)) {
      // Give a bogus type until type inference is implemented.
      return new VariableAST(varName, TypeAST::i(32), sourceRange);
    }

    ExprAST* var = gScopeLookupAST(varName);
    if (!var) {
      EDiag() << "unknown var name: " << varName << show(sourceRange);
    }
    return var;
  }

  if (token == OUT) {
    return (getChildCount(tree) == 0)
              ? NULL
              : ExprAST_from(child(tree, 0), fnMeansClosure);
  }

  if (token == FNDEF) {
    ASSERT(getChildCount(tree) == 2);
    // x = fn { blah }   ===   x = fn "x" { blah }
    pTree lval = (child(tree, 0));
    pTree rval = (child(tree, 1));

    if (typeOf(lval) == NAME && typeOf(rval) == FN) {
      return parseFn(textOf(child(lval, 0)), rval, fnMeansClosure);
    } else {
      cerr << "Not assigning function to a name?" << endl;
      return NULL;
    }
  }

  if (text == "new" || text == "ref") {
    bool isKnownIndirect    = text == "new";

    // Currently 'new' and 'ref' are interchangeable, though the intended
    // convention is that 'new' is for value-exprs and 'ref' is for type-exprs
    return new RefExprAST(
                 ExprAST_from(child(tree, 0), fnMeansClosure),
    		 isKnownIndirect,
                 sourceRange);
  }

  // Handle unary negation explicitly, before the binary op handler
  if (getChildCount(tree) == 1 && isUnaryOp(text)) {
    return new UnaryOpExprAST(text,
                  ExprAST_from(child(tree, 0), fnMeansClosure),
                  sourceRange);
  }

  if (token == PARENEXPR) {
    ExprAST* rv = ExprAST_from(child(tree, 0), fnMeansClosure);
    gWasWrappedInExplicitParens[rv] = true;
    return rv;
  }

  if (token == COMPILES) {
     return new BuiltinCompilesExprAST(
                  ExprAST_from(child(tree, 0), fnMeansClosure), sourceRange);
  }

  // Implicitly, every entry in the precedence table is a binary operator.
  if (foster::gCompilationContexts.top()->prec.isKnownOperatorName(text)) {
    ExprAST* lhs = ExprAST_from(child(tree, 0), fnMeansClosure);
    ExprAST* rhs = ExprAST_from(child(tree, 1), fnMeansClosure);
    return parseBinaryOpExpr(text, lhs, rhs);
  }

  if (token == IF) {
    return new IfExprAST(ExprAST_from(child(tree, 0), fnMeansClosure),
                         ExprAST_from(child(tree, 1), fnMeansClosure),
                         ExprAST_from(child(tree, 2), fnMeansClosure),
                         sourceRange);
  }

  // This could be either an anonymous function, in which case
  // fnMeansClosure will be true, or it could be a function with
  // an embedded name like fn "main" () { blah }, and fnMeansClosure
  // will be false.
  if (token == FN) {
    // for now, this "<anon_fn" prefix is used for closure conversion later on
    FnAST* fn = parseFn("<anon_fn_%d>", tree, fnMeansClosure);
    if (!fn->body) {
      foster::EDiag() << "Found bare proto (with no body)"
                      << " when expecting full fn literal."
                      << foster::show(fn);
      return NULL;
    }

    if (0) cout << "Parsed fn " << *(fn->proto) << ", fnMeansClosure? "
              << fnMeansClosure << endl;
    if (fnMeansClosure) {
      ClosureAST* cloast = new ClosureAST(fn, sourceRange);
      if (1) EDiag() << "\t\t\tFN MEANS CLOSURE: " << str(fn)
        << "; cloast = " << foster::show(cloast);
      return cloast;
    } else {
      return fn;
    }
  }

  if (text == "false" || text == "true") {
    return new BoolAST(text, sourceRange);
  }

  // Should have handled all keywords by now...
  if (keywords[text]) {
    EDiag() << "illegal use of keyword '" << text << "'" << show(sourceRange);
    return NULL;
  }

  if (reserved_keywords[text]) {
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

Exprs getExprs(pTree tree, bool fnMeansClosure) {
  Exprs f;
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    f.push_back(ExprAST_from(child(tree, i), fnMeansClosure));
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
    IntAST* ast = parseIntFrom(tree);
    if (ast) {
      return LiteralIntValueTypeAST::get(ast);
    }
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
    FnAST* fn = parseFn("<anon_fn_%d>", tree, true);
    if (!fn) {
      EDiag() << "no fn expr when parsing fn type!" << show(sourceRange);
      return NULL;
    }
    if (fn->body) {
      EDiag() << "had unexpected fn body when parsing fn type!" << show(fn);
    }
    return new ClosureTypeAST(fn->proto, NULL, sourceRange);
  }

  if (text == "ref") {
    // TODO add sourcerange or make ctor public
    return RefTypeAST::get(TypeAST_from(child(tree, 0)));
  }

  if (token == OUT) {
    return (getChildCount(tree) == 0) ? NULL : TypeAST_from(child(tree, 0));
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

  gCompilationContexts.push(cc);
  gInputFile = NULL;
  gInputTextBuffer = membuf;
  
  fosterParser_expr_return langAST = ctx->psr->expr(ctx->psr);

  outNumANTLRErrors = ctx->psr->pParser->rec->state->errorCount;

  ExprAST* rv = ExprAST_from(langAST.tree, false);

  // If we reuse the same compilation context again later,
  // we do not want to accidentally pick up an incorrect
  // token boundary if we happen to randomly get the same
  // tree pointer values! Doing so can make ANTLR crash.
  gCompilationContexts.top()->startTokens.clear();
  gCompilationContexts.top()->  endTokens.clear();
  gCompilationContexts.pop();

  delete ctx;
  
  return rv;
}

ModuleAST* parseModule(const InputFile& file,
                       pTree& outTree,
                       ANTLRContext*& ctx,
                       unsigned& outNumANTLRErrors,
                       CompilationContext* cc) {
  ctx = new ANTLRContext();
  createParser(*ctx, file);

  installTreeTokenBoundaryTracker(ctx->psr->adaptor);
  foster::installRecognitionErrorFilter(ctx->psr->pParser->rec);

  gCompilationContexts.push(cc);
  gInputFile = &file;
  gInputTextBuffer = file.getBuffer();
  
  fosterParser_program_return langAST = ctx->psr->program(ctx->psr);

  outTree = langAST.tree;
  outNumANTLRErrors = ctx->psr->pParser->rec->state->errorCount;

  ModuleAST* m = parseTopLevel(outTree);

  gCompilationContexts.top()->startTokens.clear();
  gCompilationContexts.top()->  endTokens.clear();
  gCompilationContexts.pop();

  return m;
}

} // namespace foster

const char* ANTLR_VERSION_STR = PACKAGE_VERSION;
