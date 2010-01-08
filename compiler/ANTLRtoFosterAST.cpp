// vim: set foldmethod=marker :
// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "ANTLRtoFosterAST.h"
#include "FosterAST.h"

#include "fosterLexer.h"
#include "fosterParser.h"

#include <iostream>
#include <string>
#include <map>
#include <vector>
#include <sstream>
#include <cassert>

using std::string;
using std::endl;

// {{{ ANTLR stuff
std::string str(pANTLR3_STRING pstr) { return string((const char*)pstr->chars); }

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

// }}}

int getChildCount(pTree tree) { return tree->getChildCount(tree); }
string textOf(pTree tree) { return str(tree->getText(tree)); }
pTree child(pTree tree, int i) { return (pTree) tree->getChild(tree, i); }

Exprs getExprs(pTree tree, int depth, bool infn);
std::ostream& operator<<(std::ostream& out, Exprs& f) { return out << join("", f); }

std::map<string, bool> binaryOps;
std::map<string, bool> keywords;
std::map<string, bool> reserved_keywords;
const char* c_binaryOps[] = {
  "<=", "<", "==",
  "*", "+", "/", "-",
  "bitand", "bitor", "shl", "shr",
  "=" }; // ".."
const char* c_keywords[] = { "as" , "at" , "def" , "id", "in", "is", "it", "to",
  "given" , "false" , "if" , "match" , "do" , "new" , "nil",
  "gives" , "and" , "or" , "true" , "var" , "while"
};
const char* c_reserved_keywords[] = {
  "def", "catch", "for",
  "lazy", "object", "package", "private", "protected", "requires", "ensures"
  "return", "throw", "trait", "try", "type", "val", "with", "yield"
};

void initMaps() {
  for (int i = 0; i < sizeof(c_binaryOps)/sizeof(char*); ++i) {
    binaryOps[c_binaryOps[i]] = true;
  }
  for (int i = 0; i < sizeof(c_keywords)/sizeof(char*); ++i) {
    keywords[c_keywords[i]] = true;
  }

  for (int i = 0; i < sizeof(c_reserved_keywords)/sizeof(char*); ++i) {
    reserved_keywords[c_reserved_keywords[i]] = true;
  }

  initModuleTypeNames();
}

string spaces(int n) { return string(n, ' '); }

void display_pTree(pTree t, int nspaces) {
  int token = t->getType(t);
  string text = textOf(t);
  int nchildren = getChildCount(t);
  std::cout << spaces(nspaces) << "<" << text << "; " << token << std::endl;
  for (int i = 0; i < nchildren; ++i) {
    display_pTree(child(t, i), nspaces+2);
  }
  std::cout << spaces(nspaces) << "/" << text << ">" << std::endl;
}

IntAST* parseIntFrom(pTree t) {
  if (textOf(t) != "INT") {
    std::cerr << "Error: parseIntFrom() called on a " << textOf(t) << "!";
    return NULL;
  }

  int base = 10;
  std::stringstream clean;

  // Each child is either a hex clump, a backtick, or an underscore
  int nchildren = getChildCount(t);
  for (int i = 0; i < nchildren; ++i) {
    string text = textOf(child(t, i));

    if (text == "_") {
      if (i != nchildren - 2) {
        std::cerr << "Error: number can have only one underscore, in 2nd-to-last position!";
        return NULL;
      } else {
        std::stringstream ss_base(textOf(child(t, i+1)));
        ss_base >> base;
        break;
      }
    } else if (text != "`") {
      clean << text;
    }
  }

  // LLVM will decide what does or does not constitute a valid int string for a given radix.
  return new IntAST(clean.str(), base);
}

int typeOf(pTree tree) { return tree->getType(tree); }

VariableAST* parseFormal(pTree tree) {
  string varName = textOf(child(tree, 0));
  const Type* ty = NULL;
  if (getChildCount(tree) == 2) {
    string typeName = textOf(child(tree, 1));
   
    // TODO: this needs to be delayed...
    ty = LLVMTypeFor(typeName);
    std::cout << "\tParsed formal " << varName << " with type " << *ty << std::endl;
    if (!ty) {
      std::cerr << "Error: LLVM module had no type for name '" << typeName << "'" << std::endl;
    }
  } else {
    // TODO
  }
  VariableAST* var = new VariableAST(varName, ty);
  varScope.insert(varName, var);
  return var;
}

std::vector<VariableAST*> getFormals(pTree tree) {
  std::vector<VariableAST*> args;
  for (int i = 0; i < getChildCount(tree); ++i) {
     args.push_back(parseFormal(child(tree, i)));
  }
  return args;
}

// defaultSymbolTemplate can include "%d" to embed a unique number; otherwise,
// a unique int will be appended to the template.
// (FN 0:NAME 1:IN 2:OUT 3:BODY)
FnAST* parseFn(string defaultSymbolTemplate, pTree tree, int depth, bool infn) {
  if (infn) {
    std::cerr << "Error: saw function inside another function"
              << "; nested functions not yet supported..." << std::endl;
    return NULL;
  }

  string name;
  if (getChildCount(child(tree, 0)) == 1) {
    pTree treeName = child(tree, 0);
    string nameWithQuotes = textOf(child(treeName, 0));
    name = nameWithQuotes.substr(1, nameWithQuotes.size() - 2);
  } else {
    name = freshName(defaultSymbolTemplate);
  }
  
  varScope.pushScope("fn proto " + name);
    PrototypeAST* proto = new PrototypeAST(name, getFormals(child(tree, 1)));
    VariableAST* fnRef = new VariableAST(name, proto->GetType());
    varScope.insert(name, fnRef);
    
    std::cout << "Parsing body of fn " << name << std::endl;
    ExprAST* body = ExprAST_from(child(tree, 3), depth + 1, true);
    std::cout << "Parsed  body of fn " << name << std::endl;
  varScope.popScope();
  
  FnAST* fn = new FnAST(proto, body);
  varScope.insert(name, fnRef);
  
  return fn;
}

ExprAST* ExprAST_from(pTree tree, int depth, bool infn) {
  if (!tree) return NULL;

  int token = typeOf(tree);
  string text = textOf(tree);
  int nchildren = getChildCount(tree);
  //printf("%sToken number %d, text %s, nchildren: %d\n", spaces(depth).c_str(), token, text.c_str(), nchildren);
  //display_pTree(tree, 2);
  
  if (token == TRAILERS) {
    assert(getChildCount(tree) >= 2);
    // name (args) ... (args)
    ExprAST* prefix = ExprAST_from(child(tree, 0), depth, infn);
    for (int i = 1; i < getChildCount(tree); ++i) {
      int trailerType = typeOf(child(tree, i));
      if (trailerType == CALL) {
        prefix = new CallAST(prefix, getExprs(child(tree, i), depth, infn));
      } else if (trailerType == SUBSCRIPT) {
        prefix = new SubscriptAST(prefix, ExprAST_from(child(child(tree, i), 0), depth, infn));
      } else {
        std::cerr << "Unknown trailer type " << textOf(child(tree, i)) << std::endl;
      }
    }
    return prefix;
  }
  
  if (token == SEQ) { // contains FIELD_LIST
    return ExprAST_from(child(tree, 0), depth + 1, infn);
  }
  
  if (token == BODY) { // usually contains SEQ
    return ExprAST_from(child(tree, 0), depth, infn);
  }
  
  if (token == EXPRS || token == FIELD_LIST) {
    Exprs exprs;
    for (int i = 0; i < getChildCount(tree); ++i) {
      ExprAST* ast = ExprAST_from(child(tree, i), depth + 1, infn);
      exprs.push_back(ast);
    }
    return new SeqAST(exprs);
  }

  if (token == INT) {
    IntAST* ast = parseIntFrom(tree);
    if (ast) {
      return ast;
    } else {
      std::cout << "Could not parse int!"; // TODO improve error message
      return NULL;
    }
  }
  
  if (token == NAME) {
    string varName = textOf(child(tree, 0));
    ExprAST* var = varScope.lookup(varName, "");
    if (!var) {
      std::cerr << "Could not find expr for var name\t" << varName << std::endl;
    }
    return var;
  }
  
  if (text == "=") {
    assert(getChildCount(tree) == 2);
    // x = fn { blah }   ===   x = fn "x" { blah }
    pTree lval = (child(tree, 0));
    pTree rval = (child(tree, 1));
    
    if (typeOf(lval) == NAME && typeOf(rval) == FN) {
      FnAST* fn = parseFn(textOf(child(lval, 0)), rval, depth, infn);
      return fn;
    } else {
      std::cerr << "Not assigning function to a name?" << std::endl;
      return NULL;
    }
  }
  
  if (token == TUPLE) {
    return new TupleExprAST(ExprAST_from(child(tree, 0), depth + 1, infn));
  }
  
  if (binaryOps[text]) {
    return new BinaryExprAST(text, ExprAST_from(child(tree, 0), depth + 1, infn),
                                   ExprAST_from(child(tree, 1), depth + 1, infn));
  }
  if (token == IF) {
    return new IfExprAST(ExprAST_from(child(tree, 0), depth+1, infn),
                         ExprAST_from(child(tree, 1), depth+1, infn),
                         ExprAST_from(child(tree, 2), depth+1, infn));
  }
  if (token == FN) {
    return parseFn("<anon_fn_%d>", tree, depth, infn);
  }

  if (text == "false" || text == "true") {
    return new BoolAST(text);
  }
  
  /*
  if (text == "nil") {
    return new VariableAST(text);
  }
  */

  // Should have handled all keywords by now...
  if (keywords[text]) {
    std::cerr << "Illegal use of keyword '" << text << "' !" << endl;
    return NULL;
  }

  if (reserved_keywords[text]) {
    std::cerr << "Cannot use reserved keyword '" << text << "' !" << endl;
    return NULL;
  }

  string name = str(tree->getToken(tree));
  printf("returning NULL ExprAST for tree token %s\n", name.c_str());
  return NULL;
}

Exprs getExprs(pTree tree, int depth, bool infn) {
  Exprs f;
  int childCount = getChildCount(tree);
  for (int i = 0; i < childCount; ++i) {
    f.push_back(ExprAST_from(child(tree, i), depth + 1, infn));
  }
  return f;
}

