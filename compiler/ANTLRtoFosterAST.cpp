// vim: set foldmethod=marker :
#include "ANTLRtoFosterAST.h"
#include "FosterAST.h"

#include "fosterLexer.h"
#include "fosterParser.h"

#include <iostream>
#include <string>
#include <map>
#include <vector>
#include <sstream>

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

string join(string glue, Exprs exprs) {
  std::stringstream ss;
  for (int i = 0; i < exprs.size(); ++i) {
    if (i > 0) ss << glue;
    if (exprs[i]) {
      ss << *exprs[i];
    } else {
      ss << "<nil>";
    }
  }
  return ss.str();
}

std::ostream& operator<<(std::ostream& out, Exprs& f) { return out << join("", f); }

int getChildCount(pTree tree) { return tree->getChildCount(tree); }
string textOf(pTree tree) { return str(tree->getText(tree)); }
pTree child(pTree tree, int i) { return (pTree) tree->getChild(tree, i); }

Exprs getExprs(pTree tree);

std::map<string, bool> binaryOps;
std::map<string, bool> keywords;
std::map<string, bool> reserved_keywords;
const char* c_binaryOps[] = { "<=", "<", "==", "*", "+", "/", "-", "=" };
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

  llvm::LLVMContext& gcon = getGlobalContext();
  NamedTypes["Int"] =     Type::getInt32Ty(gcon);
  NamedTypes["Boolean"] = Type::getInt1Ty(gcon);
  /*
  std::vector<const Type*> StringParts;
  StringParts.push_back(Type::Int32Ty);
  StringParts.push_back(PointerType::get(Type::Int8Ty, DEFAULT_ADDRESS_SPACE));
  NamedTypes["String"] = StructType::get(StringParts);
  TheModule->addTypeName("String", NamedTypes["String"]);
  */

  const unsigned DEFAULT_ADDRESS_SPACE = 0u;
  NamedTypes["String"] = llvm::PointerType::get(Type::getInt8Ty(gcon), DEFAULT_ADDRESS_SPACE);
  //NamedTypes["Any"] = Type::Int32Ty; // TODO
}

void indent(int n) { for (int i = 0; i < n; ++i) { std::cout << " "; } }

void display_pTree(pTree t, int nspaces) {
  int token = t->getType(t);
  string text = textOf(t);
  int nchildren = getChildCount(t);
  indent(nspaces);
  std::cout << "<" << text << "; " << token << std::endl;
  for (int i = 0; i < nchildren; ++i) {
    display_pTree(child(t, i), nspaces+2);
  }
  indent(nspaces);
  std::cout << "/" << text << ">" << std::endl;
}

IntAST* parseIntFrom(pTree t) {
  if (textOf(t) != "INT") {
    std::cout << "parseIntFrom() called on a " << textOf(t) << "!";
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
        std::cout << "Error: number can have only one underscore, in 2nd-to-last position!";
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

ExprAST* ExprAST_from(pTree tree) {
  if (!tree) return NULL;

  int token = tree->getType(tree);
  string text = textOf(tree);
  int nchildren = getChildCount(tree);
  printf("Token number %d, text %s, nchildren: %d\n", token, text.c_str(), nchildren);
  //display_pTree(tree, 2);
  if ((text == "EXPRS" || text == "BODY" || text == "SEQ" || text == "FIELD_LIST") && nchildren > 0) {
    std::cout << "Ignoring all but first expression...";
    return ExprAST_from(child(tree, 0));
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
  if (binaryOps[text]) {
    return new BinaryExprAST(text, ExprAST_from(child(tree, 0)), ExprAST_from(child(tree, 1)));
  }
  if (token == FN) {
    string name = "<anon fn>";
    if (getChildCount(child(tree, 0)) == 1) {
      pTree NAME = child(tree, 0);
      string nameWithQuotes = textOf(child(NAME, 0));
      name = nameWithQuotes.substr(1, nameWithQuotes.size() - 2);
    }
    PrototypeAST* proto = new PrototypeAST(name);
    ExprAST* body = ExprAST_from(child(tree, 3));
    return new FnAST(proto, body);
  }

  /*
  if (text == "false" || text == "true" || text == "nil") {
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

Exprs getExprs(pTree tree) {
  Exprs f;
  int childCount = getChildCount(tree);
  for (int i = 0; i < childCount; ++i) {
    f.push_back(ExprAST_from(child(tree, i)));
  }
  return f;
}

