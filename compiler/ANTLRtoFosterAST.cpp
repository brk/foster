// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "ANTLRtoFosterAST.h"
#include "FosterAST.h"
#include "TypecheckPass.h"

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
string textOf(pTree tree) {
  if (!tree) {
    std::cerr << "Error! Can't get text of a null node!" << std::endl;
    return "<NULL pTree>";
  }
  return str(tree->getText(tree));
}
pTree child(pTree tree, int i) {
  if (!tree) {
    std::cerr << "Error! Can't take child of null pTree!" << std::endl;
    return NULL;
  }
  return (pTree) tree->getChild(tree, i);
}

Exprs getExprs(pTree tree, bool fnMeansClosure);
std::ostream& operator<<(std::ostream& out, Exprs& f) { return out << join("", f); }

std::map<ExprAST*, bool> overridePrecedence; // expressions wrapped in () are marked here
std::map<string, bool> keywords;
std::map<string, bool> reserved_keywords;

enum OperatorAssociativity {
  eLeftAssociative,
  eRightAssociative,
  eNotAssociative };
struct OpSpec { const char* name; int precedence; OperatorAssociativity assoc; };

std::map<string, OpSpec> binaryOps;
bool isBinaryOp(const std::string& name) {
  return binaryOps[name].precedence > 0;
}
// TODO: enforce associativity
// TODO: exponentiation operator?
OpSpec c_binaryOps[] = {
    { "/",  20, eLeftAssociative },
    { "*",  20, eLeftAssociative },
    { "-",  25, eLeftAssociative },
    { "+",  25, eLeftAssociative },
    { "<=", 50, eLeftAssociative },
    { "<",  50, eLeftAssociative },
    { "==", 60, eLeftAssociative },
    { "!=", 60, eLeftAssociative },
    { "=",  70, eNotAssociative  }
}; // ".."
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
  for (int i = 0; i < ARRAY_SIZE(c_binaryOps); ++i) {
    binaryOps[c_binaryOps[i].name] = OpSpec(c_binaryOps[i]);
  }

  for (int i = 0; i < ARRAY_SIZE(c_keywords); ++i) {
    keywords[c_keywords[i]] = true;
  }

  for (int i = 0; i < ARRAY_SIZE(c_reserved_keywords); ++i) {
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
  std::stringstream clean, alltext;

  // Each child is either a hex clump, a backtick, or an underscore
  int nchildren = getChildCount(t);
  for (int i = 0; i < nchildren; ++i) {
    string text = textOf(child(t, i));

    if (text == "_") {
      if (i != nchildren - 2) {
        std::cerr << "Error: number can have only one underscore, in 2nd-to-last position!";
        return NULL;
      } else {
        string baseText = textOf(child(t, i+1));
        alltext << "_" << baseText;

        std::stringstream ss_base(baseText);
        ss_base >> base;
        break;
      }
    } else if (text != "`") {
      clean << text;
      alltext << text;
    } else {
      alltext << text;
    }
  }

  // LLVM will decide what does or does not constitute a valid int string for a given radix.
  return new IntAST(alltext.str(), clean.str(), base);
}

int typeOf(pTree tree) { return tree->getType(tree); }

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
    std::cerr << "Error! Null var name in parseFormal..." << std::endl;
    display_pTree(tree, 4);
    return NULL;
  }
  string varName = textOf(child(varNameTree, 0));
  if (getChildCount(tree) == 2) {
    ExprAST* tyExpr = ExprAST_from(child(tree, 1), true);
    if (tyExpr) {
      std::cout << "\tParsed formal " << varName << " with type expr " << str(tyExpr) << std::endl;
    } else {
      std::cout << "\tParsed formal " << varName << " with null type expr " << std::endl;
    }
    VariableAST* var = new VariableAST(varName, tyExpr);
    varScope.insert(varName, var);
    return var;
  } else {
    VariableAST* var = new VariableAST(varName); // no fixed type, infer later
    varScope.insert(varName, var);
    return var;
  }
}

std::vector<VariableAST*> getFormals(pTree tree, bool fnMeansClosure) {
  std::vector<VariableAST*> args;
  if (textOf(tree) == "FORMAL") {
    args.push_back(parseFormal(tree, fnMeansClosure));
  } else {
    for (int i = 0; i < getChildCount(tree); ++i) {
       args.push_back(parseFormal(child(tree, i), fnMeansClosure));
    }
  }
  return args;
}

PrototypeAST* getFnProto(string name, bool fnMeansClosure, pTree formalsTree, pTree tyExprTree) {
  FosterSymbolTable<ExprAST>::LexicalScope* protoScope = varScope.pushScope("fn proto " + name);
    std::vector<VariableAST*> in = getFormals(formalsTree, fnMeansClosure);
    ExprAST* tyExpr = ExprAST_from(tyExprTree, fnMeansClosure);
  varScope.popScope();

  PrototypeAST* proto = new PrototypeAST(name, in, tyExpr, protoScope);
  VariableAST* fnRef = new VariableAST(proto->name, proto);
  varScope.insert(proto->name, fnRef);

  return proto;
}

FnAST* buildFn(PrototypeAST* proto, pTree bodyTree) {
  varScope.pushExistingScope(proto->scope);
    ExprAST* body = ExprAST_from(bodyTree, true);
  varScope.popExistingScope(proto->scope);

  return new FnAST(proto, body);
}

// parses    a  op  b...c
ExprAST* parseBinaryOpExpr(const std::string& opname, ExprAST* a, ExprAST* bc) {
  if (BinaryOpExprAST* rhs = dynamic_cast<BinaryOpExprAST*>(bc)) {
    // ExprAST_from strips parens from expressions; instead of recording their
    // presence in the original source in the ExprAST, we store parenthesized
    // AST nodes in a separate table.
    bool wasExplicitlyParenthesized = overridePrecedence[rhs];
    if (wasExplicitlyParenthesized) {
      // Can't split the RHS up; no choice but to return op(a, (b...c))
      goto done;
    }

    ExprAST* b = rhs->parts[rhs->kLHS];
    ExprAST* c = rhs->parts[rhs->kRHS];
    std::string rop = rhs->op;

    // a opname b rop c
    if (binaryOps[opname].precedence <= binaryOps[rop].precedence) {
      delete rhs;
      return new BinaryOpExprAST(rop, parseBinaryOpExpr(opname, a, b), c);
    }
  }

  done:
  return new BinaryOpExprAST(opname, a, bc);
}

std::ostream& operator<<(std::ostream& out, const OpSpec& op) {
  return out << "(opr " << op.name << " : " << op.precedence << ")";
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
  PrototypeAST* proto = getFnProto(name, fnMeansClosure, child(tree, 1), child(tree, 2));
  return buildFn(proto, child(tree, 3));
}

// ExprAST_from() is straight-up recursive, and uses varScope and typeScope
// to keep track of lexical scoping for types and variables, respectively.
// This works wonderfully for function bodies, where variables must appear
// in topologically sorted order. In order to allow functions at the top-level
// to appear in unsorted order, we have to separate the extraction of function
// prototypes (and insertion of said name/proto pair into the varScope symbol
// table) from the actual parsing of the function body.
ExprAST* parseTopLevel(pTree tree) {
  std::vector<pTree> pendingParseTrees(getChildCount(tree));
  std::vector<ExprAST*> exprs(getChildCount(tree));
  // forall i, exprs[i] == pendingParseTrees[i] == NULL

  for (int i = 0; i < getChildCount(tree); ++i) {
    pendingParseTrees[i] = child(tree, i);
  }

  // forall i, exprs[i] == NULL, pendingParseTrees[i] != NULL
  std::map<pTree, PrototypeAST*> protos;

  for (int i = 0; i < pendingParseTrees.size(); ++i) {
    pTree c = pendingParseTrees[i];
    int token = typeOf(c);

    if (token == TYPEDEFN) { exprs[i] = ExprAST_from(c, false); }
    else if (token == FNDEF) {
      assert(getChildCount(c) == 2);
      // x = fn { blah }   ===   x = fn "x" { blah }
      pTree lval = (child(c, 0));
      pTree rval = (child(c, 1));
      if (typeOf(lval) == NAME && typeOf(rval) == FN) {
        // (FN 0:NAME 1:IN 2:OUT 3:BODY)
        string name = parseFnName(textOf(child(lval, 0)), rval);
        protos[c] = getFnProto(name, true, child(rval, 1), child(rval, 2));
      } else {
        std::cerr << "Not assigning top-level function to a name?" << std::endl;
      }
    } else {
      exprs[i] = ExprAST_from(c, false);
    }
  }

  // forall i, either exprs[i] == NULL && pendingParseTrees[i] != NULL
  //              or  exprs[i] != NULL && pendingParseTrees[i] == NULL

  for (int i = 0; i < pendingParseTrees.size(); ++i) {
    if (!exprs[i]) {
      pTree c = pendingParseTrees[i];
      if (PrototypeAST* proto = protos[c]) {
        pTree rval = child(c, 1);
        exprs[i] = buildFn(proto, child(rval, 3));
      } else {
        exprs[i] = ExprAST_from(c, false);
      }
    }
  }

  return new SeqAST(exprs);
}

ExprAST* ExprAST_from(pTree tree, bool fnMeansClosure) {
  if (!tree) return NULL;

  int token = typeOf(tree);
  string text = textOf(tree);
  int nchildren = getChildCount(tree);
  //display_pTree(tree, 2);

  if (token == TYPEDEFN) {
    pTree nameTree = child(tree, 0);
    string name = textOf(child(nameTree, 0));

    llvm::PATypeHolder namedType = llvm::OpaqueType::get(getGlobalContext());
    typeScope.pushScope("opaque");
      typeScope.insert(name, TypeAST::get(namedType.get()));
      ExprAST* tyExpr = ExprAST_from(child(tree, 1), fnMeansClosure);
      { TypecheckPass tyPass; tyPass.typeParsingMode = true; tyExpr->accept(&tyPass); }
      llvm::cast<llvm::OpaqueType>(namedType.get())->refineAbstractTypeTo(tyExpr->type->getLLVMType());
    typeScope.popScope();

    typeScope.insert(name, tyExpr->type);
    std::cout << "Associated " << name << " with type " << *(tyExpr->type) << std::endl;
    //module->addTypeName(name, tyExpr->type->getLLVMType());
  }

  if (token == TRAILERS) {
    assert(getChildCount(tree) >= 2);
    // name (args) ... (args)
    ExprAST* prefix = ExprAST_from(child(tree, 0), fnMeansClosure);
    for (int i = 1; i < getChildCount(tree); ++i) {
      int trailerType = typeOf(child(tree, i));
      if (trailerType == CALL) {
        Exprs args = getExprs(child(tree, i), fnMeansClosure);

        // Two different things can parse as function calls: normal function calls,
        // and function-call syntax for built-in bitwise operators.
        VariableAST* varPrefix = dynamic_cast<VariableAST*>(prefix);
        if (varPrefix) {
          if (varPrefix->name == "deref") {
            if (args.size() != 1) {
              std::cerr << "Error! Deref operator called with bad number of args: " <<
                  args.size() << std::endl;
              return NULL;
            }
            prefix = new DerefExprAST(args[0]);
            continue;
          }

          if (isBitwiseOpName(varPrefix->name)) {
            if (args.size() != 2) {
              std::cerr << "Error! Bitwise operator " << varPrefix->name <<
                  " with bad number of arguments: " << args.size() << "!" << std::endl;
              return NULL;
            }
            prefix = new BinaryOpExprAST(varPrefix->name, args[0], args[1]);
            continue;
          }
          // Else fall through to general case below
        }
        prefix = new CallAST(prefix, args);
      } else if (trailerType == LOOKUP) {
        pTree nameNode = child(child(tree, i), 0);
        const string& name = textOf(child(nameNode, 0));
        prefix = prefix->lookup(name, "");
        if (!prefix) { std::cerr << "Lookup of name '" << name << "' failed." << std::endl; }
      } else if (trailerType == SUBSCRIPT) {
        prefix = new SubscriptAST(prefix, ExprAST_from(child(child(tree, i), 0), fnMeansClosure));
      } else {
        std::cerr << "Unknown trailer type " << textOf(child(tree, i)) << std::endl;
      }
    }
    return prefix;
  }

  if (token == BODY) { // usually contains SEQ
    return ExprAST_from(child(tree, 0), fnMeansClosure);
  }

  // <var start end body incr?>
  if (token == FORRANGE) {
    string varName = textOf(child(child(tree, 0), 0));
    VariableAST* var = new VariableAST(varName, TypeAST::get(LLVMTypeFor("i32")));
    ExprAST* start = ExprAST_from(child(tree, 1), fnMeansClosure);
    ExprAST* end   = ExprAST_from(child(tree, 2), fnMeansClosure);
    ExprAST* incr  = NULL;

    if (getChildCount(tree) >= 5) {
      incr = ExprAST_from(child(tree, 4), fnMeansClosure);
    }

    varScope.pushScope("for-range " + varName);
    varScope.insert(varName, var);
    ExprAST* body  = ExprAST_from(child(tree, 3), fnMeansClosure);
    varScope.popScope();

    std::cout << "for (" << varName <<" in _ to _ ...)" << std::endl;
    return new ForRangeExprAST(var, start, end, body, incr);
  }

  // <LHS RHS>
  if (token == SETEXPR) {
    ExprAST* lhs = validateAssignLHS(ExprAST_from(child(tree, 0), fnMeansClosure));
    if (!lhs) {
      std::cerr << "Error! Invalid syntactic form on LHS of assignment;" <<
          " must be variable or subscript expr" << std::endl;
      return NULL;
    }
    ExprAST* rhs = ExprAST_from(child(tree, 1), fnMeansClosure);
    return new AssignExprAST(lhs, rhs);
  }

  // <formal arg (body | next) [type]>
  if (token == LETEXPR) {
    pTree tyExprTree = NULL;
    if (getChildCount(tree) == 4) {
      tyExprTree = child(tree, 3);
    }

    PrototypeAST* proto = getFnProto(freshName("<anon_fnlet_%d>"), fnMeansClosure, child(tree, 0), tyExprTree);
    FnAST* fn = buildFn(proto, child(tree, 2));
    fn->lambdaLiftOnly = true;

    ExprAST* a = ExprAST_from(child(tree, 1), fnMeansClosure);
    Exprs args; args.push_back(a);
    return new CallAST(fn, args);
  }

  if (token == EXPRS || token == SEQ) {
    if (fnMeansClosure) {
      Exprs exprs;
      for (int i = 0; i < getChildCount(tree); ++i) {
        ExprAST* ast = ExprAST_from(child(tree, i), fnMeansClosure);
        if (ast != NULL) {
          exprs.push_back(ast);
        }
      }
      return new SeqAST(exprs);
    } else {
      return parseTopLevel(tree);
    }
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

  if (token == CTOR) { // ^(CTOR ^(NAME blah) ^(SEQ ...))
    pTree nameNode = child(tree, 0);
    pTree seqArgs = child(tree, 1);

    string name = textOf(child(nameNode, 0));
    if (name == "simd-vector") {
      return new SimdVectorAST(ExprAST_from(seqArgs, fnMeansClosure));
    }
    if (name == "array") {
      return new ArrayExprAST(ExprAST_from(seqArgs, fnMeansClosure));
    }
    if (name == "tuple") {
      return new TupleExprAST(ExprAST_from(seqArgs, fnMeansClosure));
    }

    // TODO for now, new mytype { args } is equivalent to new tuple { args }
    if (TypeAST* ty = typeScope.lookup(name, "")) {
      assert(ty->getLLVMType() && ty->getLLVMType()->isStructTy());
      return new TupleExprAST(ExprAST_from(seqArgs, fnMeansClosure), name);
    }

    std::cerr << "Error: CTOR token parsing found unknown type name '" << name << "'" << std::endl;
    return NULL;
  }

  if (token == NAME) {
    string varName = textOf(child(tree, 0));

    // Don't bother trying to look up special variable names,
    // since we'll end up discarding this variable soon anyways.
    if (isSpecialName(varName)) {
      // Give a bogus type until type inference is implemented.
      return new VariableAST(varName, TypeAST::get(LLVMTypeFor("i32")));
    }

    ExprAST* var = varScope.lookup(varName, "");
    if (!var) {
      // Maybe parsing a type expr, in which case names refer directly to
      // types, either user-defined or built-in (to Foster or LLVM)
      TypeAST* ty = typeScope.lookup(varName, "");
      if (!ty) {
        ty = TypeASTFor(varName);
        if (ty) {
          //std::cout << "Could not find ExprAST for var name\t" << varName << ", but it's a valid builtin type name..." << std::endl;
          var = new VariableAST(varName, ty);
        } else {
          std::cerr << "Could not find ExprAST for var name\t" << varName << ", and it's not a valid type name..." << std::endl;
        }
      } else {
        //std::cout << "Could not find ExprAST for var name\t" << varName << ", but it's a valid user type name..." << std::endl;
        var = new VariableAST(varName, ty);
      }
    } else {
      //std::cout << "Found entry for variable " << varName << " in scope." << std::endl;
    }
    return var;
  }

  if (token == OUT) {
    return (getChildCount(tree) == 0) ? NULL : ExprAST_from(child(tree, 0), fnMeansClosure);
  }

  if (token == FNDEF) {
    assert(getChildCount(tree) == 2);
    // x = fn { blah }   ===   x = fn "x" { blah }
    pTree lval = (child(tree, 0));
    pTree rval = (child(tree, 1));

    if (typeOf(lval) == NAME && typeOf(rval) == FN) {
      return parseFn(textOf(child(lval, 0)), rval, fnMeansClosure);
    } else {
      std::cerr << "Not assigning function to a name?" << std::endl;
      return NULL;
    }
  }

  if (text == "new" || text == "ref" || text == "?ref") {
	bool isNullableTypeDecl = text == "?ref";
	bool isKnownIndirect    = text == "new";

    // Currently 'new' and 'ref' are interchangeable, though the intended
    // convention is that 'new' is for value-exprs and 'ref' is for type-exprs
    return new RefExprAST(ExprAST_from(child(tree, 0), fnMeansClosure),
    		isNullableTypeDecl, isKnownIndirect);
  }

  if (text == "nil") { return new NilExprAST(); }

  // Handle unary negation explicitly, before the binary op handler
  if (getChildCount(tree) == 1 && isUnaryOp(text)) {
    return new UnaryOpExprAST(text, ExprAST_from(child(tree, 0), fnMeansClosure));
  }

  if (token == PARENEXPR) {
    ExprAST* rv = ExprAST_from(child(tree, 0), fnMeansClosure);
    overridePrecedence[rv] = true;
    return rv;
  }

  if (token == COMPILES) { return new BuiltinCompilesExprAST(ExprAST_from(child(tree, 0), fnMeansClosure)); }
  if (token == UNPACK)   { return new UnpackExprAST(ExprAST_from(child(tree, 0), fnMeansClosure)); }

  if (isBinaryOp(text)) {
    ExprAST* lhs = ExprAST_from(child(tree, 0), fnMeansClosure);
    ExprAST* rhs = ExprAST_from(child(tree, 1), fnMeansClosure);
    return parseBinaryOpExpr(text, lhs, rhs);
  }

  if (token == IF) {
    return new IfExprAST(ExprAST_from(child(tree, 0), fnMeansClosure),
                         ExprAST_from(child(tree, 1), fnMeansClosure),
                         ExprAST_from(child(tree, 2), fnMeansClosure));
  }
  if (token == FN) {
    // for now, this "<anon_fn" prefix is used for closure conversion later on
    FnAST* fn = parseFn("<anon_fn_%d>", tree, fnMeansClosure);
    if (!fn->body) {
      std::cout << "NO BODY FOR PROTO " << *fn->proto << std::endl;

      return new ClosureTypeAST(fn);
    }

    std::cout << "Parsed fn " << *(fn->proto) << ", fnMeansClosure? " << fnMeansClosure << std::endl;
    if (fnMeansClosure) {
      std::cout << "\t\t\tFN MEANS CLOSURE: " << *fn << std::endl;
      //return fn;
      return new ClosureAST(fn);
    } else {
      return fn;
    }
  }
  if (text == "false" || text == "true") { return new BoolAST(text); }


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

Exprs getExprs(pTree tree, bool fnMeansClosure) {
  Exprs f;
  int childCount = getChildCount(tree);
  for (int i = 0; i < childCount; ++i) {
    f.push_back(ExprAST_from(child(tree, i), fnMeansClosure));
  }
  return f;
}

