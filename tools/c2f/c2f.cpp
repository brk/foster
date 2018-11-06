//------------------------------------------------------------------------------
// C-to-Foster translator.
// Mainly focuses on translating syntax as a starting point for human cleanup,
// rather than being an Emscripten-style automated translator of semantics.
//
// Current status: moderately hacky prototype.
//
// Doesn't do any special handling/recognition of function-like macros.
// Doesn't do any relooping for converted CFGs.
// Doesn't handle pointers or structure allocations very well.
//   (needs to do analysis to differentiate arrays from singleton pointers).
// Could get better translations by doing more careful analysis of which
//   variables in the program are mutable and which aren't.
// Doesn't handle certain name conflicts in generated code.
//   Specifically, accessor names (field 'anon' of type 'S')
//   can shadow datatype construtors ('$S_anon' from whatever type).
// Doesn't yet gracefully handle declarations/usage of unnamed,
//   un-typedef'ed structs.
// Doesn't handle variable-arg list function definitions.
// Doesn't yet handle fixed-length arrays.
// Doesn't handle global variables.
//
// Originally based on AST matching sample by Eli Bendersky (eliben@gmail.com).
//------------------------------------------------------------------------------
#include <string>
#include <sstream>
#include <set>

#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Analysis/CFG.h"
#include "clang/Analysis/Analyses/FormatString.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Lex/Lexer.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Format.h"

using namespace clang;
using namespace clang::ast_matchers;
using namespace clang::driver;
using namespace clang::tooling;

class FieldPointernessTracker {
public:
  FieldPointernessTracker() {}

  void notePointeryField(const FieldDecl* fd);

  void notePointeryField(const ValueDecl* vd) {
    if (auto fd = dyn_cast<FieldDecl>(vd)) {
      notePointeryField(fd);
    }
  }

  bool isPointeryField(const FieldDecl* fd);
  bool isPointeryField(const ValueDecl* vd) {
    if (auto fd = dyn_cast<FieldDecl>(vd)) {
      return isPointeryField(fd);
    }
    return false;
  }
  bool isPointeryField(const Expr* e) {
    if (auto me = dyn_cast<MemberExpr>(e)) {
      return isPointeryField(me->getMemberDecl());
    }
    return false;
  }

private:
  std::map<std::string, bool> fullPtrFields;
};

class VarMutabilityAndPointernessTracker {
public:
  VarMutabilityAndPointernessTracker() {}

  void notePointeryVar(const std::string& name) { pointery[name] = true; }
  bool isPointeryVar(const FieldDecl* fd);
  bool isPointeryVar(const std::string& v) { return pointery[v]; }
  bool isPointeryVar(const Expr* e) {
    if (auto dre = dyn_cast<DeclRefExpr>(e->IgnoreParenImpCasts())) {
      return pointery[dre->getDecl()->getName()];
    }
    return false;
  }

  void noteMutableVar(const std::string& v) { mutableness[v] = true; }
  bool isMutableVar(const std::string& v) { return mutableness[v]; }
  bool isMutableVar(const Expr* e) {
    if (auto dre = dyn_cast<DeclRefExpr>(e->IgnoreParenImpCasts())) {
      return mutableness[dre->getDecl()->getName()];
            // || isDeclRefOfMutableAlias(e);
    }
    return false;
  }

  void summarize(const std::string& name) {
    llvm::errs() << "For function " << name << ":\n";
    llvm::errs() << "Local variable pointerness status:\n";
    for (auto p : pointery) {
      llvm::errs() << "\t" << p.first << " :: " << p.second << "\n";
    }
    llvm::errs() << "\n";
    llvm::errs() << "Local variable mutability status:\n";
    for (auto p : mutableness) {
      llvm::errs() << "\t" << p.first << " :: " << p.second << "\n";
    }
  }

  void clear() {
    pointery.clear();
    mutableness.clear();
  }

private:
  std::map<std::string, bool> pointery;
  std::map<std::string, bool> mutableness;
};

struct {
private:
  std::map<std::string, bool> handledTypeNames;

public:
  bool alreadyHandled(const std::string& name) {
    bool handled = handledTypeNames[name];
    if (!handled) handledTypeNames[name] = true;
    return handled;
  }

  bool shouldIgnore(const std::string& name) {
    return ignoredSymbolNames.find(name) != ignoredSymbolNames.end();
  }

  std::map<std::string, std::string> enumPrefixForConstants;
  std::set<std::string> ignoredSymbolNames;

  FieldPointernessTracker fpt;

  // I couldn't figure out a better way of communicating between the
  // ClangTool invocation site and the ASTConsumer itself.
  struct { bool SawGlobalVariables = false; } uglyhack;
} globals;

static llvm::cl::OptionCategory CtoFosterCategory("C-to-Foster");

static llvm::cl::opt<bool>
optDumpCFGs("dump-cfgs",
  llvm::cl::desc("Dump CFGs (when using CFGs instead of ASTs for reconstruction)"),
  llvm::cl::cat(CtoFosterCategory));

static llvm::cl::opt<bool>
optDumpOrigSource("dump-orig-source",
  llvm::cl::desc("Dump original C source in a comment before each generated function"),
  llvm::cl::cat(CtoFosterCategory));

static llvm::cl::opt<bool>
optC2FVerbose("c2f-verbose",
  llvm::cl::desc("Enable extra debugging output"),
  llvm::cl::cat(CtoFosterCategory));
/*
static bool startswith(const std::string& a, const std::string& b) {
  return a.size() >= b.size() && a.substr(0, b.size()) == b;
}
*/

std::string s(const char* c) { return std::string(c); }
std::string s(uint64_t v) { return std::to_string(v); }

const RecordType* bindRecordType(const Type* typ) {
  if (const TypedefType* tty = dyn_cast<TypedefType>(typ)) {
    return bindRecordType(tty->desugar().getTypePtr());
  }
  if (const ElaboratedType* ety = dyn_cast<ElaboratedType>(typ)) {
    return bindRecordType(ety->getNamedType().getTypePtr());
  }
  if (const RecordType* rty = dyn_cast<RecordType>(typ)) {
    return rty;
  }
  return nullptr;
}

std::string tyOpSuffix(const clang::Type* ty) {
  if (ty->isCharType()) return "Int8";
  if (ty->isSpecificBuiltinType(BuiltinType::UShort)) return "Int16";
  if (ty->isSpecificBuiltinType(BuiltinType::Short)) return "Int16";
  if (ty->isSpecificBuiltinType(BuiltinType::UInt)) return "Int32";
  if (ty->isSpecificBuiltinType(BuiltinType::Int)) return "Int32";
  if (ty->isSpecificBuiltinType(BuiltinType::ULong)) return "Int64";
  if (ty->isSpecificBuiltinType(BuiltinType::Long)) return "Int64";
  if (ty->isSpecificBuiltinType(BuiltinType::ULongLong)) return "Int64";
  if (ty->isSpecificBuiltinType(BuiltinType::LongLong)) return "Int64";
  if (ty->isSpecificBuiltinType(BuiltinType::Float)) return "f32";
  if (ty->isSpecificBuiltinType(BuiltinType::Double)) return "f64";
  if (ty->isSpecificBuiltinType(BuiltinType::LongDouble)) return "f64";

  if (auto pty = dyn_cast<PointerType>(ty)) {
    return "Ptr /*" + tyOpSuffix(ty->getPointeeType().getTypePtr()) + "*/ ";
  }

  if (auto tdty = dyn_cast<TypedefType>(ty)) {
    return tdty->getDecl()->getName();
  }

  return "";
}

std::string fnTyName(const FunctionProtoType* fpt);

std::string tryParseFnTy(const Type* ty) {
  if (auto tdt = dyn_cast<TypedefType>(ty)) {
    return tryParseFnTy(tdt->desugar().getTypePtr());
  }
  if (auto pty = dyn_cast<PointerType>(ty)) {
    return tryParseFnTy(pty->getPointeeType().getTypePtr());
  }
  if (auto fpt = dyn_cast<FunctionProtoType>(ty)) {
    return fnTyName(fpt);
  }
  return "";
}

const Stmt* lastStmtWithin(const Stmt* s) {
  if (!s) return s;
  if (const CompoundStmt* cs = dyn_cast<CompoundStmt>(s)) {
    if (cs->body_back()) return cs->body_back();
  }
  return s;
}

bool isVoidPtr(const Type* inp_ty) {
  const PointerType* ptr_ty = dyn_cast<PointerType>(inp_ty);
  const Type* ty = ptr_ty ? ptr_ty->getPointeeType().getTypePtr() : nullptr;
  return ty && ty->isVoidType();
}

bool isTrivialIntegerLiteralInRange(const Expr* e, int64_t lo, int64_t hi) {
  if (auto lit = dyn_cast<IntegerLiteral>(e->IgnoreParenImpCasts())) {
    int64_t se = lit->getValue().getSExtValue();
    return se >= lo && se <= hi;
  }
  return false;
}

template <typename T>
std::string str(T x) {
  std::string s;
  std::stringstream ss(s);
  ss << x;
  return ss.str();
}

std::string getNameForAnonymousRecordTypeWithin(const Decl* d, const TagDecl* td) {
  std::string rv;

  if (td) {
    if (auto typdef = td->getTypedefNameForAnonDecl()) {
      rv = typdef->getIdentifier()->getName();
    } else if (td->getIdentifier()) {
      rv = td->getIdentifier()->getName();
    }
  } else {
    rv = "Anon_";
  }

  if (!rv.empty()) {
    PresumedLoc PLoc = d->getASTContext().getSourceManager().getPresumedLoc(
      d->getLocation());
    if (PLoc.isValid()) {
      rv = rv + "__" + str(PLoc.getLine()) + "_" + str(PLoc.getColumn());
    }
  }

  return rv;
}

std::string fosterizedTypeName(std::string rv) {
  if (rv == "_IO_FILE") return "CFile";

  if ((!rv.empty()) && islower(rv[0])) {
    rv[0] = toupper(rv[0]);
  }
  return rv;
}

std::string maybeNonUppercaseTyName(const clang::Type* ty, std::string defaultName);

std::string tyName(const clang::Type* ty, std::string defaultName = "C2FUNK") {
  if (ty->isCharType()) return "Int8";
  if (ty->isSpecificBuiltinType(BuiltinType::UShort)) return "Int16";
  if (ty->isSpecificBuiltinType(BuiltinType::Short)) return "Int16";
  if (ty->isSpecificBuiltinType(BuiltinType::UInt)) return "Int32";
  if (ty->isSpecificBuiltinType(BuiltinType::Int)) return "Int32";
  if (ty->isSpecificBuiltinType(BuiltinType::ULong)) return "Int64";
  if (ty->isSpecificBuiltinType(BuiltinType::Long)) return "Int64";
  if (ty->isSpecificBuiltinType(BuiltinType::ULongLong)) return "Int64";
  if (ty->isSpecificBuiltinType(BuiltinType::LongLong)) return "Int64";
  if (ty->isSpecificBuiltinType(BuiltinType::Float)) return "Float32";
  if (ty->isSpecificBuiltinType(BuiltinType::Double)) return "Float64";
  if (ty->isSpecificBuiltinType(BuiltinType::LongDouble)) return "Float64";

  if (ty->isSpecificBuiltinType(BuiltinType::Void)) return "()";

  return fosterizedTypeName(maybeNonUppercaseTyName(ty, defaultName));
}

std::string getNamedRecordDeclName(const RecordDecl* rd) {
  if (TypedefNameDecl* tnd = rd->getTypedefNameForAnonDecl()) {
    return tnd->getName();
  }

  return rd->getNameAsString();
}

std::string getRecordDeclName(const RecordDecl* rd) {
  std::string name = getNamedRecordDeclName(rd);

  if (name.empty()) { // anonymous nested struct, probably.
    if (auto td = dyn_cast<TagDecl>(rd->getDeclContext())) {
      name = getNameForAnonymousRecordTypeWithin(rd, td);
    } else {
      name = getNameForAnonymousRecordTypeWithin(rd, nullptr);
    }
  }

  return name;
}

const RecordDecl* getRecordDeclFromType(const Type* ty) {
  if (const ElaboratedType* ety = dyn_cast<ElaboratedType>(ty)) {
    if (ety->isSugared()) {
      return getRecordDeclFromType(ety->desugar().getTypePtr());
    }
  }

  if (const RecordType* rty = dyn_cast<RecordType>(ty)) {
    return rty->getDecl();
  }

  return nullptr;
}

std::string getEnumTypeReprName(const EnumType* ety) {
  return tyName(ety->getDecl()->getIntegerType().getTypePtr());
}

std::string getEnumDeclName(const EnumDecl* ed) {
  std::string name = ed->getCanonicalDecl()->getNameAsString();
  if (name.empty()) {
    auto tnd = ed->getTypedefNameForAnonDecl();
    if (tnd) name = tnd->getNameAsString();
  }
  if (name.empty()) name = "/*EnumType unknown*/";
  return name;
}

std::string getEnumTypeName(const EnumType* ety) {
  return getEnumDeclName(ety->getDecl());
}

bool tryBindConstantSizedArrayType(const Type* ty,
                                   const Type* &eltTy,
                                   uint64_t    &size) {
  if (auto cat = dyn_cast<ConstantArrayType>(ty)) {
    const Type* inner = cat->getElementType().getTypePtr();
    const uint64_t outerSize = cat->getSize().getZExtValue();

    uint64_t innerSize = 0;
    if (tryBindConstantSizedArrayType(inner, eltTy, innerSize)) {
      size = outerSize * innerSize;
    } else {
      size = outerSize;
      eltTy = inner;
    }
    return true;
  }
  return false;
}

std::string maybeNonUppercaseTyName(const clang::Type* ty, std::string defaultName) {

  if (const PointerType* pty = dyn_cast<PointerType>(ty)) {
    auto eltTy = pty->getPointeeType().getTypePtr();

    // Special case: pointer-to-function in C becomes plain function in Foster.
    // TODO: identify & elide C's explicit function environments.
    if (auto dc = dyn_cast<DecayedType>(eltTy)) {
      std::string fnty = tryParseFnTy(dc->getDecayedType().getTypePtr());
      if (fnty != "") return fnty;
    }
    if (auto dc = dyn_cast<FunctionProtoType>(eltTy)) {
      return fnTyName(dc);
    }

    // could mean either (Array t) or (Ref t) or t
    if (isVoidPtr(pty)) return "VOIDPTR";
    if (const RecordType* rty = bindRecordType(eltTy)) {
      auto nm = rty->getDecl()->getNameAsString();
      if (!nm.empty()) return nm;

      return tyName(pty->getPointeeType().getTypePtr());
    }

    return "(Ptr " + tyName(eltTy) + ") /*411*/";
  }

  if (auto dc = dyn_cast<DecayedType>(ty)) {
    std::string fnty = tryParseFnTy(dc->getDecayedType().getTypePtr());
    if (fnty != "") return fnty;
  }
  if (auto dc = dyn_cast<FunctionProtoType>(ty)) {
    return fnTyName(dc);
  }

  if (const TypedefType* tty = dyn_cast<TypedefType>(ty)) {
    auto nm = tyName(tty->desugar().getTypePtr(), tty->getDecl()->getNameAsString());
    if (!nm.empty()) return nm;
  }

  if (const ConstantArrayType* cat = dyn_cast<ConstantArrayType>(ty)) {
    uint64_t size = 0; const Type* eltTy = nullptr;
    tryBindConstantSizedArrayType(cat, eltTy, size);

    if (cat->getSizeModifier() != ArrayType::Normal) {
      llvm::outs() << "// TODO(f2c) handle size modified arrays\n";
    }
    return "(Ptr " + tyName(eltTy)
                     + " /*arrsize=" + s(size) + "*/ )";
  }

  if (const ElaboratedType* ety = dyn_cast<ElaboratedType>(ty)) {
    if (ety->isSugared()) {
      auto nm = tyName(ety->desugar().getTypePtr());
      if (!nm.empty()) return nm;
    }
  }

  if (const RecordType* rty = dyn_cast<RecordType>(ty)) {
    return getRecordDeclName(rty->getDecl());
  }
  if (const ParenType* rty = dyn_cast<ParenType>(ty)) { return tyName(rty->getInnerType().getTypePtr()); }

  if (const EnumType* ety = dyn_cast<EnumType>(ty)) {
    //return getEnumTypeName(ety);
    // We use the underlying representation (e.g. Int32) as the enum type name.
    // Since C allows things like direct addition of enums and numeric constants,
    // Clang doesn't explicitly represent all the coercions we'd need to
    // have strongly-typed enum values. Probably this should be configurable,
    // for users who'd prefer to get type errors for loose enum usage.
    return getEnumTypeReprName(ety);
  }

  // If we were going to handle fixed-size array types, this is probably where we'd do it.
  if (const DecayedType* dty = dyn_cast<DecayedType>(ty)) { return tyName(dty->getDecayedType().getTypePtr()); }

  // TODO handle constantarraytype

  if (defaultName == "C2FUNK") {
    llvm::outs().flush();
    llvm::errs() << "line 382:\n";
    ty->dump();
    llvm::errs().flush();
  }
  return defaultName;
}


std::string fnTyName(const FunctionProtoType* fpt) {
  std::string rv = "{";
  if (fpt->getNumParams() > 0) {
    for (auto p : fpt->getParamTypes()) {
      if (!isVoidPtr(p.getTypePtr())) {
        rv += " " + tyName(p.getTypePtr()) + " =>";
      }
    }
  }
  rv += " " + tyName(fpt->getReturnType().getTypePtr());
  rv += " }";
  return rv;
}

const Type* exprTy(const ValueDecl* e) { return e->getType().getTypePtr(); }
const Type* exprTy(const Expr* e) { return e->getType().getTypePtr(); }
std::string tyName(const Expr* e) { return tyName(exprTy(e)); }

std::string infixOp(const std::string& op, const std::string& ty) { return "`" + op + ty + "`"; }

std::string mkFosterBinop(const std::string& op, const clang::Type* typ, const clang::Type* typR) {
  if (op == "=") return op;

  std::string ty = tyOpSuffix(typ);
  if (op == "&") return infixOp("bitand-", ty);
  if (op == "|") return infixOp("bitor-" , ty);
  if (op == "^") return infixOp("bitxor-", ty);
  if (op == "<<") return infixOp("bitshl-",ty);
  if (op == ">>" && typ->hasSignedIntegerRepresentation()) return infixOp("bitashr-",ty);
  if (op == ">>") return infixOp("bitlshr-",ty);

  if (op == "%" && typ->hasSignedIntegerRepresentation()) return infixOp("srem-unsafe-", ty);
  if (op == "%" && typ->hasUnsignedIntegerRepresentation()) return infixOp("urem-unsafe-", ty);
  if (op == "/" && typ->hasSignedIntegerRepresentation()) return infixOp("sdiv-unsafe-", ty);
  if (op == "/" && typ->hasUnsignedIntegerRepresentation()) return infixOp("udiv-unsafe-", ty);

  if (op == "%") return infixOp("mod-", ty);
  if (op == "/") return infixOp("div-", ty);

  if (op[0] == '<' || op[0] == '>') {
    if (typ->hasSignedIntegerRepresentation())
      return op + "S" + ty;
    if (typ->hasUnsignedIntegerRepresentation())
      return op + "U" + ty;
  }

  if (op == "-") {
    if (typ->isPointerType() && typR->isPointerType()) {
      return infixOp("ptrDiff", "");
    } else {
      return "-" + ty;
    }
  }


  if (ty == "") {
    llvm::outs() << "/* no tyopsuffix for\n";
    llvm::outs().flush();
    typ->dump();
    llvm::errs().flush();
    llvm::outs() << "*/\n";
  }

  return op + ty;
}

std::string fosterizedNameChars(std::string nm) {
  for (size_t i = 0; i < nm.size(); ++i) {
    char c = nm[i];
    if (c == ' ' || c == '(' || c == ')') {
      nm[i] = '_';
    }
  }
  return nm;
}

std::string fosterizedName(const std::string& name) {
  if (name == "to" || name == "do" || name == "type" || name == "case"
    || name == "of" || name == "as" || name == "then" || name == "end"
    || name == "in" || name == "effect" || name == "handle") {
    return name + "_";
  }
  if (name.empty()) {
    return "__empty__";
  }
  if (isupper(name[0])) {
    return "v_" + name;
  }
  if (name == "strlen") return "ptrStrlen";
  if (name == "strcmp") return "ptrStrcmp";

  if (name == "fabs")   return "abs-f64";
  if (name == "fabsf")  return "abs-f32";

  if (name == "feof")   return "c2f_feof";
  if (name == "ferror") return "c2f_ferror";
  if (name == "fwrite") return "c2f_fwrite";
  if (name == "fread")  return "c2f_fread";
  if (name == "fopen")  return "c2f_fopen";
  if (name == "fclose") return "c2f_fclose";
  if (name == "fseek")  return "c2f_fseek";
  if (name == "ftell")  return "c2f_ftell";
  if (name == "fputs")  return "c2f_fputs";
  if (name == "fgetc")  return "c2f_fgetc";
  if (name == "getc")   return "c2f_fgetc";
  if (name == "_IO_getc") return "c2f_fgetc";
  if (name == "fputc")  return "c2f_fputc";
  if (name == "rewind") return "c2f_rewind";
  if (name == "exit")   return "c2f_exit";
  if (name == "stdin") return "(c2f_stdin !)";
  if (name == "stdout") return "(c2f_stdout !)";
  if (name == "stderr") return "(c2f_stderr !)";

  return name;
}

bool isAnonymousStructOrUnionType(const Type* ty) {
  if (auto ety = dyn_cast<ElaboratedType>(ty)) {
    if (auto rty = dyn_cast<RecordType>(ety->desugar().getTypePtr())) {
      auto d = rty->getDecl();
      return (d->getIdentifier() == NULL)
          && (d->getNameAsString().empty())
          && (d->getDeclName().isEmpty());
    }
  }
  return false;
}

// Convert v->f, if v has type T*, to (T_f v)
// Convert v->s.f, if v has type T*, and s is anonymous,
//                                   to (T_s_f v)
// Convert v->s.f, if v has type T*, and s has type S,
//                                   to (S_f (T_s v))
// Convert v.s->f, if v has type T*, and f has type X,
//                                   to (X_f (T_s v))
std::string fieldAccessorName(const MemberExpr* me, const Expr* & base, bool addressOf) {
  std::string path = "";
  base = me->getBase();
  const MemberExpr* baseme = me;
  while (true) {
    baseme = dyn_cast<MemberExpr>(baseme->getBase()->IgnoreImplicit());
    if (!baseme || !isAnonymousStructOrUnionType(baseme->getType().getTypePtr()))
      break;
    path = path + "_" + baseme->getMemberNameInfo().getAsString();
    base = baseme->getBase();
  }

  return tyName(exprTy(base)) + path + "_" + me->getMemberNameInfo().getAsString()
                              + (addressOf ? "_addr" : "");
}

std::string enumPrefix(const EnumDecl* ed) {
  std::string prefix = ed->getNameAsString();
  if (!prefix.empty()) prefix += "_";
  return prefix;
}

std::string enumConstantAccessor(const std::string& prefix,
                                 const EnumConstantDecl* ecd) {
  return prefix + ecd->getNameAsString();
}


void emitUTF8orAsciiStringLiteral(StringRef data) {
  // Clang's outputString uses octal escapes, but we only support
  // Unicode escape sequences in non-byte-strings.
  bool useTriple = data.count('\n') > 1;
  // TODO must also check the str doesn't contain 3 consecutive dquotes.
  // TODO distinguish text vs byte strings...?
  llvm::outs() << "(strLit " << "b" << (useTriple ? "\"\"\"" : "\"");
  for (char c : data) {
    switch(c) {
      case '\n': llvm::outs() << (useTriple ? "\n" : "\\n"); break;
      case '\t': llvm::outs() << "\\t"; break;
      case '\\': llvm::outs() << "\\\\"; break;
      case '"' : llvm::outs() << (useTriple ? "\"" : "\\\""); break;
      default:
        if (isprint(c)) {
          llvm::outs() << c;
        } else {
          llvm::outs() << llvm::format("\\u{%02x}", (unsigned char) c);
        }
        break;
    }
  }
  llvm::outs() << "\\x00";
  llvm::outs() << (useTriple ? "\"\"\"" : "\"");
  llvm::outs() << ")";
}

bool isPointerToPlainData(const clang::Type* ty) {
  if (auto pty = dyn_cast<PointerType>(ty)) {
    return pty->getPointeeType()->isScalarType();
  }
  return false;
}

void FieldPointernessTracker::notePointeryField(const FieldDecl* fd) {
  const RecordDecl* rd = fd->getParent();
  std::string accessor = fosterizedTypeName(getRecordDeclName(rd))
                          + "_" + fosterizedName(fd->getName());
  if (optC2FVerbose) { llvm::errs() << "noting pointery field: " << accessor << "\n"; }
  fullPtrFields[accessor] = true;
}

bool FieldPointernessTracker::isPointeryField(const FieldDecl* fd) {
  const RecordDecl* rd = fd->getParent();
  std::string accessor = fosterizedTypeName(getRecordDeclName(rd)) + "_" + fosterizedName(fd->getName());
  return fullPtrFields[accessor];
}

// Run across the whole program before emitting any code.
class PointerishFieldHandler : public MatchFinder::MatchCallback {
public:
  PointerishFieldHandler() {}

  virtual void run(const MatchFinder::MatchResult &Result) {
    if (auto e = Result.Nodes.getNodeAs<MemberExpr>("unaryopmem")) {
      if (auto md = e->getMemberDecl()) {
        if (!isPointerToPlainData(md->getType().getTypePtr())) {
          // pointers to plain data don't need to be extra pointery;
          // pointery-ness applies to pointers-to-structs and such,
          // which must choose between being represented as T or Ptr T.
          globals.fpt.notePointeryField(md);
        }
      }
    }
    if (auto e = Result.Nodes.getNodeAs<MemberExpr>("subscriptedfield")) {
      if (auto md = e->getMemberDecl()) {
        if (!isa<ConstantArrayType>(md->getType())) {
          globals.fpt.notePointeryField(md);
        }
      }
    }

    if (auto me = Result.Nodes.getNodeAs<MemberExpr>("binopfield")) {
      if (auto bo = Result.Nodes.getNodeAs<BinaryOperator>("binop")) {
        if (bo->isAssignmentOp() || bo->isCompoundAssignmentOp()) {
          auto rhs = bo->getRHS();
          if (rhs->getType().getTypePtr()->isPointerType()) {
            if (looksPointery(rhs->IgnoreParenImpCasts())) {
              globals.fpt.notePointeryField(me->getMemberDecl());
            }
          }
        }
      }
    }
  }

  bool looksPointery(const Expr* e) {
    // Note that this might give wrong answers depending on processing order
    // since we're not doing "real" unification.
    if (auto me  = dyn_cast<MemberExpr>(e)) { return globals.fpt.isPointeryField(me); }

    if (auto ase  = dyn_cast<ArraySubscriptExpr>(e)) { return false; } // convenient approximation...
    if (auto unop = dyn_cast<UnaryOperator>(e)) {
      if (unop->getOpcode() == UO_AddrOf) return true;
      return looksPointery(unop->getSubExpr());
    }
    
    return false;
  }
};

// Run across each function immediately before it is translated.
class MutableLocalHandler : public MatchFinder::MatchCallback {
public:
  MutableLocalHandler(VarMutabilityAndPointernessTracker& vmpt) : vmpt(vmpt) {}

  virtual void run(const MatchFinder::MatchResult &Result) {
    if (auto v = Result.Nodes.getNodeAs<DeclRefExpr>("binopvar")) {
      if (auto bo = Result.Nodes.getNodeAs<BinaryOperator>("binop")) {
        if (bo->isAssignmentOp() || bo->isCompoundAssignmentOp()) {
          if (optC2FVerbose) { llvm::errs() << "MutableLocalHandler: binopvar: "
                                            << v->getDecl()->getName() << "\n"; }
          vmpt.noteMutableVar(v->getDecl()->getName());

          auto rhs = bo->getRHS();
          if (rhs->getType().getTypePtr()->isPointerType()) {
            if (looksPointery(rhs->IgnoreParenImpCasts())) {
              vmpt.notePointeryVar(v->getDecl()->getName());
            } else {
              llvm::errs() << "didn't look pointery:\n";
              rhs->IgnoreParenImpCasts()->dump();
            }
          }
        }
      }
    }
    if (auto v = Result.Nodes.getNodeAs<DeclRefExpr>("unaryopvar")) {
      vmpt.noteMutableVar(v->getDecl()->getName());
    }
    if (auto v = Result.Nodes.getNodeAs<DeclRefExpr>("addrtakenvar"))
      vmpt.noteMutableVar(v->getDecl()->getName());
    if (auto v = Result.Nodes.getNodeAs<VarDecl>("vardecl-noinit"))
      vmpt.noteMutableVar(v->getName());
    if (auto v = Result.Nodes.getNodeAs<VarDecl>("vardecl")) {
      if (!v->hasInit()) {
        vmpt.noteMutableVar(v->getName());
      }
    }
  }

  bool looksPointery(const Expr* e) {
    // Note that this might give wrong answers depending on processing order
    // since we're not doing "real" unification.
    if (auto dre = dyn_cast<DeclRefExpr>(e)) { return vmpt.isPointeryVar(dre); }
    if (auto me  = dyn_cast<MemberExpr>(e)) { return globals.fpt.isPointeryField(me); }

    if (auto ase  = dyn_cast<ArraySubscriptExpr>(e)) { return false; } // convenient approximation...
    if (auto unop = dyn_cast<UnaryOperator>(e)) {
      if (unop->getOpcode() == UO_AddrOf) return true;
      return looksPointery(unop->getSubExpr());
    }
    
    return false;
  }

private:
  VarMutabilityAndPointernessTracker& vmpt;
};

template<typename T>
class ZeroOneTwoSet {
public:
  ZeroOneTwoSet() : sz(0) { }
  bool empty() const { return sz == 0; }
  bool unique() const { return sz == 1; }
  bool full() const { return !empty() && !unique(); }
  T front() const { return elts[0]; }
  void add(T elt) {
         if (sz == 0) { sz = 1; elts[0] = elt; }
    else if (sz == 1) { sz = 2; elts[1] = elt; }
  }
private:
  int sz;
  T elts[2];
};

typedef std::map<const Decl*, ZeroOneTwoSet<const Type*> > VoidPtrCasts;

// Rather than excise the special cases in our copy of Clang's CFG builder,
// it's much easier to just forcibly turn logical operators into bitwise
// operators for the purposes of CFG building.
class LogicalAndOrTweaker : public RecursiveASTVisitor<LogicalAndOrTweaker> {
public:
  LogicalAndOrTweaker(llvm::DenseMap<const Stmt*, BinaryOperatorKind>& tweaked) : tweaked(tweaked) {}
  bool VisitStmt(Stmt* s) {
    if (auto bo = dyn_cast<BinaryOperator>(s)) {
      if (bo->getOpcode() == BO_LAnd) {
        tweaked[bo] = BO_LAnd;
        bo->setOpcode(BO_And);
      }
      if (bo->getOpcode() == BO_LOr) {
        tweaked[bo] = BO_LOr;
        bo->setOpcode(BO_Or);
      }
    }
    return true;
  }

private:
  llvm::DenseMap<const Stmt*, BinaryOperatorKind>& tweaked;
};

class PointerUsageVisitor : public RecursiveASTVisitor<PointerUsageVisitor> {
  public:
  PointerUsageVisitor(ASTContext& ctx) : ctx(ctx) {}

  bool VisitStmt(Stmt* s) {
    MatchFinder mf;

    PointerishFieldHandler pfh;
    // ++SOMETHING->field, --SOMETHING->field
    mf.addMatcher( unaryOperator(hasOperatorName("++"), hasDescendant(memberExpr(hasType(isAnyPointer())).bind("unaryopmem"))) , &pfh);
    mf.addMatcher( unaryOperator(hasOperatorName("--"), hasDescendant(memberExpr(hasType(isAnyPointer())).bind("unaryopmem"))) , &pfh);
    // SOMETHING->field[...]
    mf.addMatcher( arraySubscriptExpr(hasBase(ignoringParenImpCasts(memberExpr().bind("subscriptedfield")))) , &pfh);

    // SOMETHING->field = ...
    mf.addMatcher( binaryOperator(hasLHS(memberExpr(hasType(isAnyPointer())).bind("binopfield"))).bind("binop") , &pfh);
    mf.match(*s, ctx);
    return true;
  }

  private:
  ASTContext& ctx;
};

class FnBodyVisitor : public RecursiveASTVisitor<FnBodyVisitor> {
  public:
  FnBodyVisitor(VarMutabilityAndPointernessTracker& vmpt,
                std::map<const Stmt*, bool>& innocuousReturns,
                VoidPtrCasts& casts,
                bool& needsCFG,
                ASTContext& ctx) : vmpt(vmpt), innocuousReturns(innocuousReturns),
                        casts(casts), needsCFG(needsCFG), ctx(ctx) {}

  // Note: statements are visited top-down / preorder;
  // we rely on this fact to identify and tag "innocuous" control flow
  // statements from their parents, before they are recursively visited.
  bool VisitStmt(Stmt* s) {
    MatchFinder mf;

    MutableLocalHandler mutloc_handler(vmpt);
    // assignments: x = ...
    mf.addMatcher( binaryOperator(hasLHS(declRefExpr().bind("binopvar"))).bind("binop") , &mutloc_handler);
    // address-of &x
    mf.addMatcher( unaryOperator(hasOperatorName("&"), hasUnaryOperand(declRefExpr().bind("addrtakenvar"))) , &mutloc_handler);
    // incr/decr unary operators
    mf.addMatcher( unaryOperator(hasOperatorName("++"), hasUnaryOperand(declRefExpr().bind("unaryopvar"))) , &mutloc_handler);
    mf.addMatcher( unaryOperator(hasOperatorName("--"), hasUnaryOperand(declRefExpr().bind("unaryopvar"))) , &mutloc_handler);

    mf.addMatcher( unaryOperator(hasOperatorName("++"), hasDescendant(memberExpr(hasType(isAnyPointer())).bind("unaryopmem"))) , &mutloc_handler);
    mf.addMatcher( unaryOperator(hasOperatorName("--"), hasDescendant(memberExpr(hasType(isAnyPointer())).bind("unaryopmem"))) , &mutloc_handler);
    mf.addMatcher( arraySubscriptExpr(hasBase(ignoringParenImpCasts(memberExpr().bind("subscriptedfield")))) , &mutloc_handler);
    // vars with no intializer
    //mf.addMatcher( varDecl(unless(hasInitializer())).bind("vardecl-noinit") , &mutloc_handler);
    mf.addMatcher( varDecl().bind("vardecl") , &mutloc_handler);

#if 0
    PointerClassifier ptr_classifier(locals);
    // Pointer arithmetic
    // ptr++, ptr[off] etc
    mf.addMatcher(arraySubscriptExpr(hasBase(declRefExpr().bind("ptrarithvar"))) , &ptr_classifier);
    mf.addMatcher(unaryOperator(hasOperatorName("++"),
                                hasUnaryOperand(declRefExpr().bind("ptrarithvar"))) , &ptr_classifier);
    mf.addMatcher(unaryOperator(hasOperatorName("--"),
                                hasUnaryOperand(declRefExpr().bind("ptrarithvar"))) , &ptr_classifier);

    // Pointer stores
    // *ptr = etc
    mf.addMatcher( binaryOperator(hasOperatorNme("="),
                                  hasLHS(unaryOperator(hasOperatorName("*"),
                                                       hasUnaryOperand(declRefExpr().bind("ptrstorevar")))))  , &ptr_classifier);

    // Pointer reads
    // = *ptr etc
    mf.addMatcher( binaryOperator(hasOperatorName("="),
                                  hasRHS(hasDescendant(
                                         unaryOperator(hasOperatorName("*"),
                                                      hasUnaryOperand(declRefExpr().bind("ptrreadvar")))))) , &ptr_classifier);
#endif

    // Quicker and easier than using the matcher framework for a single matcher.
    if (const CStyleCastExpr* cse = dyn_cast<CStyleCastExpr>(s)) {
      if (const DeclRefExpr* dre = dyn_cast<DeclRefExpr>(cse->getSubExpr()->IgnoreImpCasts())) {
        handlePotentialVoidPtrCast(dre->getDecl(), cse);
      }
    }

    if (const SwitchStmt* ss = dyn_cast<SwitchStmt>(s)) {
      inspectSwitchStmt(ss);
    }

    if (isa<GotoStmt>(s) || isa<LabelStmt>(s) || isa<ContinueStmt>(s)) {
      needsCFG = true;
    }

    if (isa<BreakStmt>(s) && !innocuousBreaks[s]) {
      needsCFG = true;
    }

    if (isa<ReturnStmt>(s) && !innocuousReturns[s]) {
      needsCFG = true;
    }


    mf.match(*s, ctx);
    return true;
  }

  // Switch statements need CFG translation if they contain
  // any cases which have non-empty fallthrough blocks.
  // Break statements are innocuous if they appear as the last
  // statement in a switch case.
  //                        (non-break)
  //   START ---->  SwitchCase -----> SwitchCaseWithBody
  //     \          / \                /       |
  //      (break)--/   --(non-break)--/        | (break)
  //                       needs CFG           v
  //                                        START
  //
  // TODO make sure this works for default blocks
  // that don't appear at the end.
  void inspectSwitchStmt(const SwitchStmt* ss) {
    enum State { ST_Start, ST_SwitchCase, ST_WithBody };
    if (const CompoundStmt* cs = dyn_cast<CompoundStmt>(ss->getBody())) {
      State state = ST_Start;
      for (auto part : cs->body()) {
        if (const SwitchCase* scase = dyn_cast<SwitchCase>(part)) {
          if (state == ST_WithBody || state == ST_SwitchCase) {
            needsCFG = true;
          }
          if (const BreakStmt* bs = dyn_cast<BreakStmt>(
                        lastStmtWithin(scase->getSubStmt()))) {
            state = ST_Start;
            innocuousBreaks[bs] = true;
          } else {
            state = ST_SwitchCase;
          }
        } else {
          if (isa<BreakStmt>(part)) {
            state = ST_Start;
            innocuousBreaks[part] = true;
          } else if (state == ST_SwitchCase) {
            state = ST_WithBody;
          }
        }
      }
    }
  }

  void handlePotentialVoidPtrCast(const ValueDecl* v, const CStyleCastExpr* cse) {
    if (isVoidPtr(exprTy(v))) {
      casts[v].add(exprTy(cse));
    }
  }

  private:
  VarMutabilityAndPointernessTracker& vmpt;
  std::map<const Stmt*, bool>& innocuousReturns;
  std::map<const Stmt*, bool> innocuousBreaks;
  VoidPtrCasts& casts;
  bool& needsCFG;
  ASTContext& ctx;
};

enum ContextKind {
  ExprContext,
  StmtContext,
  AssignmentTarget,
  BooleanContext
};

enum IfExprOrStmt {
  AnIfExpr,
  AnIfStmt,
};

std::unique_ptr<CFG>
  C2F_buildCFG(const Decl *D, Stmt *Statement, ASTContext *C, const CFG::BuildOptions &BO);

class FileClassifier {
public:
  FileClassifier(const SourceManager& sm) : SM(sm) {}

  bool isFromMainFile(const SourceLocation& loc) const {
    return SM.isWrittenInMainFile(loc);
  }

  bool isFromMainFile(const Decl* d) const {
    return isFromMainFile(d->getLocation());
  }

  bool isFromSystemHeader(const Decl* d) const {
    return SM.isInSystemHeader(d->getLocation());
  }

  std::string getText(const SourceLocation& locstt, const SourceLocation& locend) const {
    SourceLocation StartSpellingLocation = SM.getSpellingLoc(locstt);
    SourceLocation EndSpellingLocation = SM.getSpellingLoc(locend);
    if (!StartSpellingLocation.isValid() || !EndSpellingLocation.isValid()) {
      return std::string();
    }
    bool Invalid = true;
    const char *Text = SM.getCharacterData(StartSpellingLocation, &Invalid);
    if (Invalid) {
      return std::string();
    }
    std::pair<FileID, unsigned> Start =
        SM.getDecomposedLoc(StartSpellingLocation);
    std::pair<FileID, unsigned> End =
        SM.getDecomposedLoc(Lexer::getLocForEndOfToken(
            EndSpellingLocation, 0, SM, LangOptions()));
    if (Start.first != End.first) {
      // Start and end are in different files.
      return std::string();
    }
    if (End.second < Start.second) {
      // Shuffling text with macros may cause this.
      return std::string();
    }
    return std::string(Text, End.second - Start.second);
  }

  // Returns the text that makes up 'node' in the source.
  // Returns an empty string if the text cannot be found.
  template <typename T>
  std::string getText(const T &Node) const {
    return getText(Node.getLocStart(), Node.getLocEnd());
  }

  const SourceManager& getSourceMgr() const { return SM; }

private:
  const SourceManager& SM;
};

bool shouldProcessTopLevelDecl(const Decl* d, const FileClassifier& FC) {
  if (!FC.isFromMainFile(d)) {
    if (FC.isFromSystemHeader(d)) return false;
    if (auto nd = dyn_cast<NamedDecl>(d)) {
      if (globals.shouldIgnore(nd->getNameAsString())) {
        return false;
      }
    }
    if (auto td = dyn_cast<TagDecl>(d)) {
      if (td->isThisDeclarationADefinition() && td->isCompleteDefinition()) {
        return true;
      }
    }
    if (isa<FunctionDecl>(d)) {
      return true;
    }

    // skip it if incomplete or from system header
    return false;
  }

  if (auto nd = dyn_cast<NamedDecl>(d)) {
    if (globals.shouldIgnore(nd->getNameAsString())) {
      return false;
    }
  }
  return true;
}

class C2F_TypeDeclHandler : public ASTConsumer {
public:
  C2F_TypeDeclHandler(const SourceManager &SM) : FC(SM) {}
  const FileClassifier FC;

  bool HandleTopLevelDecl(DeclGroupRef DR) override {
    for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b) {
      Decl* decl = *b;
      if (shouldProcessTopLevelDecl(decl, FC)) {

        if (const RecordDecl* rdo = dyn_cast<RecordDecl>(decl)) {
          if (!rdo->isThisDeclarationADefinition()) {
            continue;
          }
          if (RecordDecl* rd = rdo->getDefinition()) {
            if (rd->isEnum()) {
              llvm::outs() << "// TODO: translate enum definitions\n";
              continue;
            }
            if (!(rd->isClass() || rd->isStruct())) {
              llvm::outs() << "// TODO: handle non-class, non-struct record definitions\n";
              continue;
            }

            handleRecordDecl(rd);
          }
        } else if (const TypedefDecl* fd = dyn_cast<TypedefDecl>(decl)) {
          llvm::outs() << "/* " << FC.getText(*fd) << ";*/\n";
        } else if (const EnumDecl* ed = dyn_cast<EnumDecl>(decl)) {
          // Even if we skip emitting this particular declaration, we still want
          // to associate the enum constants with their corresponding EnumDecl.
          handleEnumDecl(ed);
        }

      }
    }
    return true;
  }

  void handleRecordDecl(const RecordDecl* rd) {
    std::string name = fosterizedTypeName(getRecordDeclName(rd));

    // When processing multiple source files that include common headers,
    // Clang will generate multiple RecordDecl nodes, but we only want
    // to emit code once.
    if (globals.alreadyHandled(name)) return;

    // Handle any anonymous struct/enum fields.
    for (auto d : rd->decls()) {
      if (const RecordDecl* erd = dyn_cast<RecordDecl>(d)) {
        handleRecordDecl(erd);
      } else if (auto ed = dyn_cast<EnumDecl>(d)) {
        handleEnumDecl(ed);
      }
    }

    llvm::outs() << "type case " << name
      << "\n       of $" << name << "_nil\n"
      // TODO when foster better supports unboxed datatypes, we should probably
      // split record translation into boxed and unboxed portions.
      << "\n       of $" << name << "\n";
    for (auto d : rd->decls()) {
      if (auto fd = dyn_cast<FieldDecl>(d)) {
        llvm::outs() << "             " << fieldOfType(fd) << " // " << fd->getName() << "\n";
      }
    }
    llvm::outs() << ";\n\n";

    llvm::outs() << name << "_isnil = { v => case v of $" << name << "_nil -> True of _ -> False end };\n";
    llvm::outs() << name << "_notnil = { v => case v of $" << name << "_nil -> False of _ -> True end };\n";

    // Emit field getters
    for (auto d : rd->decls()) {
      if (auto fd = dyn_cast<FieldDecl>(d)) {
        auto fieldType = fd->getType().getTypePtr();
        emitFieldGetter(rd, fd, name);
        emitFieldAddrGetter(rd, fd, name);
        if (isAnonymousStructOrUnionType(fieldType)) {
          std::string fieldName = fosterizedName(fd->getName());
          emitAnonFieldGetters(rd, fd, name,
                                getRecordDeclFromType(fieldType));
        }
      }
    }

    // Emit field setters
    for (auto d : rd->decls()) {
      if (const FieldDecl* fd = dyn_cast<FieldDecl>(d)) {
        std::string fieldName = fosterizedName(fd->getName());
        std::string fieldType = tyName(fd->getType().getTypePtr());
        if (globals.fpt.isPointeryField(fd)) {
            fieldType = "(Ptr " + fieldType + ")";
        }
        llvm::outs() << "set_" << name << "_" << fieldName
          << " = { sv : " << name << " => v : " << fieldType
          << " => case sv\n"
          << "of $" << name << "_nil" << " -> prim kill-entire-process \""
                                      << "set_" << name << "_" << fieldName << " called on "
                                      << name << "_nil" << "\"" << "\n"
          << "of $" << name;
        emitFieldsAsUnderscoresExcept(rd, fd, fieldName);
        llvm::outs() << " -> setField " << fieldName << " v end };\n";
      }
    }
  }

  void handleEnumDecl(const EnumDecl* ed) {
    for (auto e : ed->enumerators()) {
      globals.enumPrefixForConstants[e->getNameAsString()] = enumPrefix(ed);
    }

    if (globals.alreadyHandled(getEnumDeclName(ed))) return;

    for (auto e : ed->enumerators()) {
      llvm::outs() << enumConstantAccessor(enumPrefix(ed), e)
                    << " = { " << e->getInitVal().getSExtValue()
                    << " };\n";
    }
  }

  std::string fieldOfType(const FieldDecl* fd) {
    llvm::errs() << "fieldOfType; decl: ";
    fd->dump();
    if (globals.fpt.isPointeryField(fd)) {
      return "(Field (Ptr " + tyName(exprTy(fd)) + "))";
    } else {
      return "(Field " + tyName(exprTy(fd)) + ")";
    }
  }

  void emitFieldsAsUnderscoresExcept(const RecordDecl* rd,
                                     const FieldDecl* fd, const std::string& fieldName) {
    for (auto d2 : rd->decls()) {
      if (const FieldDecl* fd2 = dyn_cast<FieldDecl>(d2)) {
        if (fd2 == fd) {
          llvm::outs() << " " << fieldName;
        } else {
          llvm::outs() << " _";
        }
      }
    }
  }

  void emitFieldGetter(const RecordDecl* rd, const FieldDecl* fd,
                       const std::string& name, bool mightBeNil = true) {
    std::string fieldName = fosterizedName(fd->getName());
    //llvm::outs() << name << "_" << fieldName << " :: { " << name << " => ... }";
    llvm::outs() << name << "_" << fieldName << " = { sv : " << name << " => case sv ";
    if (mightBeNil) {
      llvm::outs() << "of $" << name << "_nil" << " -> prim kill-entire-process \""
                                    << "get_" << name << "_" << fieldName << " called on "
                                    << name << "_nil" << "\"" << "\n";
    }
    llvm::outs() << "of $" << name;
    emitFieldsAsUnderscoresExcept(rd, fd, fieldName);
    llvm::outs() << " -> getField " << fieldName << " end };\n";
  }

  void emitFieldAddrGetter(const RecordDecl* rd, const FieldDecl* fd,
                           const std::string& name, bool mightBeNil = true) {
    std::string fieldName = fosterizedName(fd->getName());
    llvm::outs() << name << "_" << fieldName << "_addr = { sv : " << name << " => case sv ";
    if (mightBeNil) {
      llvm::outs() << "of $" << name << "_nil" << " -> prim kill-entire-process \""
                                    << "get_" << name << "_" << fieldName << " called on "
                                    << name << "_nil" << "\"" << "\n";
    }
    llvm::outs() << "of $" << name;
    emitFieldsAsUnderscoresExcept(rd, fd, fieldName);
    llvm::outs() << " -> getFieldRef " << fieldName << " |> PtrRef end };\n";
  }
  
  void emitAnonFieldGetters(const RecordDecl* ord, const FieldDecl* ofd,
                            const std::string& name,
                            const RecordDecl* erd) {
    for (auto d : erd->decls()) {
      if (auto efd = dyn_cast<FieldDecl>(d)) {
        llvm::outs() << name << "_" << fosterizedName(ofd->getName())
                             << "_" << fosterizedName(efd->getName())
                     << " = { sv : " << name << " => "
                     << getRecordDeclName(erd) << "_"
                                    << fosterizedName(efd->getName())
                                    << " (" <<
                     name << "_" << fosterizedName(ofd->getName())
                                 << " " << "sv" << ") };\n";
      }
    }
  }
};

class MyASTConsumer;

class C2F_FormatStringHandler : public clang::analyze_format_string::FormatStringHandler {
public:
  const std::string& fmtstring;
  const char* base;
  const char* prevBase;
  ASTContext& ctx;
  const CallExpr* ce;
  MyASTConsumer& cons;

  C2F_FormatStringHandler(const std::string& fmtstring, const char* base, ASTContext& ctx,
                          const CallExpr* ce, MyASTConsumer& cons)
    : fmtstring(fmtstring), base(base), prevBase(base), ctx(ctx), ce(ce), cons(cons) {}
  ~C2F_FormatStringHandler() {
    emitStringContentsUpTo(base + fmtstring.size(), 0);
  }

  void emitStringContentsUpTo(const char* place, unsigned offset) {
    if (place == prevBase) {
      prevBase += offset;
      return;
    }

    llvm::outs() << "(printStrBare ";
    emitUTF8orAsciiStringLiteral(StringRef(prevBase, (place - prevBase)));
    llvm::outs() << ");\n";
    prevBase = place + offset;
  }

  void HandleNullChar(const char* nullChar) override {
    emitStringContentsUpTo(nullChar, 1);
    if (fmtstring != "%d\n") { printf("/* handle null char */\n"); }
    return;
  }

  void HandlePosition(const char* startPos, unsigned len) override {
    emitStringContentsUpTo(startPos, len);
    if (fmtstring != "%d\n") { printf("/* handle position: %.*s */\n", len, startPos); }
    return;
  }

  void HandleInvalidPosition(const char* startPos, unsigned len, clang::analyze_format_string::PositionContext p) override {
    //emitStringContentsUpTo(startPos, len);
    if (fmtstring != "%d\n") { printf("/* handle invalid position: %.*s */\n", len, startPos); }
    return;
  }

  void HandleZeroPosition(const char* startPos, unsigned len) override {
    emitStringContentsUpTo(startPos, len);
    if (fmtstring != "%d\n") { printf("/* handle zero position: %.*s */\n", len, startPos); }
    return;
  }

  void HandleEmptyObjCModifierFlag(const char* startFlags, unsigned len) override {
    emitStringContentsUpTo(startFlags, len);
    if (fmtstring != "%d\n") { printf("/* handle emtpy objc flags: %.*s */\n", len, startFlags); }
    return;
  }

  void HandleInvalidObjCModifierFlag(const char* startFlag, unsigned len) override {
    emitStringContentsUpTo(startFlag, len);
    if (fmtstring != "%d\n") { printf("/* handle invalid objc flags: %.*s */\n", len, startFlag); }
    return;
  }

  void HandleObjCFlagsWithNonObjCConversion(const char* flagsStart, const char* flagsEnd, const char* conversionPos) override {
    emitStringContentsUpTo(flagsStart, flagsEnd - flagsStart);
    if (fmtstring != "%d\n") { printf("/* handle objc flags: %.*s */\n", int(flagsEnd - flagsStart), flagsStart); }
    return;
  }

  bool HandleScanfSpecifier(const analyze_scanf::ScanfSpecifier& fs, const char* startSpecifier, unsigned specifierLen) override {
    return true;
  }

  bool HandlePrintfSpecifier(const analyze_printf::PrintfSpecifier& fs, const char* startSpecifier, unsigned specifierLen) override;

  bool HandleInvalidPrintfConversionSpecifier(const analyze_printf::PrintfSpecifier& fs, const char* startSpecifier, unsigned specifierLen) override {
    emitStringContentsUpTo(startSpecifier, specifierLen);
    fprintf(stderr, "/* invalid printf conversion specifier: %.*s */\n", specifierLen, startSpecifier);
    return true;
  }

  bool HandleInvalidScanfConversionSpecifier(const analyze_scanf::ScanfSpecifier& fs, const char* startSpecifier, unsigned specifierLen) override {
    emitStringContentsUpTo(startSpecifier, specifierLen);
    fprintf(stderr, "/* invalid scanf conversion specifier: %.*s */\n", specifierLen, startSpecifier);
    return true;
  }

  void HandleIncompleteScanList(const char* start, const char* end) override {
    emitStringContentsUpTo(start, end - start);
    printf("/* incomplete scan list: %.*s */\n", int(end - start), start);
  }
};


class C2F_GlobalVariableDetector : public ASTConsumer {
public:
  C2F_GlobalVariableDetector(const SourceManager &SM) : FC(SM) {}
  const FileClassifier FC;

  bool HandleTopLevelDecl(DeclGroupRef DR) override {
    for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b) {
      if (shouldProcessTopLevelDecl(*b, FC)) {
        if (const VarDecl* vd = dyn_cast<VarDecl>(*b)) {
          globals.uglyhack.SawGlobalVariables = true;
        } else {
          PointerUsageVisitor v((*b)->getASTContext());
          v.TraverseDecl(*b);
        }
      }
    }
    return true;
  }
};

class MyASTConsumer : public ASTConsumer {
public:
  MyASTConsumer(const CompilerInstance &CI) : lastloc(), CI(CI), FC(CI.getSourceManager()) { }

  void handleIfThenElse(ContextKind ctx, IfExprOrStmt ies, const Stmt* cnd, const Stmt* thn, const Stmt* els) {
    bool needTrailingUnit = ies == AnIfStmt && !isCompoundWithTrailingReturn(thn);
    llvm::outs() << "if ";
    visitStmt(cnd, BooleanContext);
    llvm::outs() << " then ";
    visitStmt(thn, ctx);
    if (needTrailingUnit || !els) {
      llvm::outs() << "; ()";
    }
    if (els) {
      llvm::outs() << " else ";
      visitStmt(els, ctx);
      if (needTrailingUnit) {
        llvm::outs() << "; ()";
      }
    }
    llvm::outs() << " end";
  }

  bool isCompoundWithTrailingReturn(const Stmt* s) {
    auto fin = lastStmtWithin(s);
    return (fin && isa<ReturnStmt>(fin));
  }

  std::string getBlockName(const CFGBlock& cb) {
    std::string s;
    std::stringstream ss(s);
    ss << "forcecont_";

    if (const Stmt* lab = cb.getLabel()) {
      if (const LabelStmt* labstmt = dyn_cast<LabelStmt>(lab)) {
        ss << labstmt->getName();
        return ss.str();
      }
    }
    ss << "block_" << cb.getBlockID();
    return ss.str();
  }

  std::string getBlockName(const CFGBlock* cb,
                           std::map<const CFGBlock*, const CFGBlock*>& aliased_blocks) {
    auto it = aliased_blocks.find(cb);
    if (it == aliased_blocks.end()) {
      return getBlockName(*cb);
    } else {
      return getBlockName(*it->second);
    }
  }

  bool isExitBlock(const CFGBlock* next) const {
    return next->getBlockID() == next->getParent()->getExit().getBlockID();
  }

  const Stmt*
  getBlockTerminatorOrLastStmt(const CFGBlock* b) const {
    // Return statements are not terminators (???) so we fish them
    // (or whatever else) out of the block if there's no actual terminator.
    const Stmt* s = b->getTerminator().getStmt();
    if (!s && !b->empty()) {
      CFGElement ce = b->back();
      if (ce.getKind() == CFGElement::Kind::Statement) {
        s = ce.castAs<CFGStmt>().getStmt();
      }
    }
    return s;
  }

  bool isEmptyFallthroughAdjacent(CFGBlock::AdjacentBlock* ab) {
    return ab->isReachable() && ab->getReachableBlock()->empty()
                             && ab->getReachableBlock()->getTerminator() == nullptr;
  }

  bool stmtHasValue(const Stmt* s) {
    if (!s) return false;
    if (isa<GotoStmt>(s) || isa<WhileStmt>(s)
     || isa<ForStmt>(s) || isa<IfStmt>(s)) return false;
    if (auto rs = dyn_cast<ReturnStmt>(s)) {
      return rs->getRetValue() != nullptr;
    }
    return true;
  }

  void emitJumpTo(CFGBlock::AdjacentBlock* ab, const Stmt* last,
                  std::map<const CFGBlock*, const CFGBlock*>& aliased_blocks) {
    bool hasValue = last ? stmtHasValue(last) : true;

    if (CFGBlock* next = ab->getReachableBlock()) {
      if (isExitBlock(next)) {
        if (!hasValue) {
          llvm::outs() << "(jump = (); jump)";
        } else {
          if (last && !isa<ReturnStmt>(last)) {
            llvm::outs() << "(prim kill-entire-process \"missing-return\")";
          } else {
            //llvm::outs() << "/*exit block, hasValue; reachable? " << ab->isReachable() << "*/";
          }
        }
      } else {
        llvm::outs() << getBlockName(next, aliased_blocks) << " !;\n"; // emitCall
      }
    } else if (CFGBlock* next = ab->getPossiblyUnreachableBlock()) {
      llvm::outs() << getBlockName(next, aliased_blocks) << " !; // unreachable\n"; // emitCall
    } else {
      llvm::outs() << "prim kill-entire-process \"no-next-block\"";
    }
  }

  std::vector<const DeclStmt*> collectDeclsAndBuildStmtMap(std::unique_ptr<CFG>& cfg) {
    std::vector<const DeclStmt*> rv;
    for (auto it = cfg->nodes_begin(); it != cfg->nodes_end(); ++it) {
      CFGBlock* cb = *it;
      unsigned j = 0;
      for (auto cbit = cb->begin(); cbit != cb->end(); ++cbit) {
        CFGElement ce = *cbit;
        if (ce.getKind() == CFGElement::Kind::Statement) {
          if (const Stmt* s = ce.castAs<CFGStmt>().getStmt()) {
            if (auto ds = dyn_cast<DeclStmt>(s)) {
              rv.push_back(ds);
              continue;
            }
            // else:
            StmtMap[s] = std::make_pair(cb->getBlockID(), j++);
          }
        }
      }
    }
    return rv;
  }

  void markDuplicateVarDecls(const std::vector<const DeclStmt*>& decls) {
    std::map<std::string, int> namesSeen;
    for (auto d : decls) {
      if (d->isSingleDecl()) {
        if (auto vd = dyn_cast<ValueDecl>(d->getSingleDecl())) {
          namesSeen[emitVarName(vd)]++;
        }
      }
    }

    int uniq = 0;
    for (auto d : decls) {
      if (d->isSingleDecl()) {
        if (auto vd = dyn_cast<ValueDecl>(d->getSingleDecl())) {
          if (namesSeen[emitVarName(vd)] > 1) {
            duplicateVarDecls[vd] = uniq++;
          }
        }
      }
    }
  }

  void handleSwitchTerminator(CFGBlock* cb, const SwitchStmt* ss,
                              std::map<const CFGBlock*, const CFGBlock*>& aliased_blocks) {
        // SwitchStmt terminator
        llvm::outs() << "case ";
        visitStmt(cb->getTerminatorCondition(), StmtContext);
        llvm::outs() << "\n";

        // Walk through the successor blocks.
        // If it's a fallthrough, associate the case label with the
        // target block.
        // If it's not a fallthrough, associate with our own block.

        CFGBlock::AdjacentBlock* defaultBlock = nullptr;
        std::map<CFGBlock*, CFGBlock* > fallthrough;
        std::map<CFGBlock*, std::vector<Stmt*> > labelsFor;

        std::vector<CFGBlock::AdjacentBlock*> adjs;
        for (auto it = cb->succ_rbegin(); it != cb->succ_rend(); ++it) {
          CFGBlock* b = it->getReachableBlock();
          if (!b) { b = it->getPossiblyUnreachableBlock(); }
          if (!b) {
            llvm::errs() << "// Saw CFG adjacent block with no adjacency at all??" << "\n";
            continue;
          }
          if (isEmptyFallthroughAdjacent(&*it)) {
            CFGBlock* direct = *(b->succ_begin());
            auto tgt0 = fallthrough[direct];
            auto tgt  = tgt0 ? tgt0 : direct;
            labelsFor[tgt].push_back(b->getLabel());
            fallthrough[b] = tgt;
          } else {
            adjs.push_back(&*it);
            labelsFor[b].push_back(b->getLabel());
          }
        }

        // TODO does this handle fallthrough into the default block?
        for (auto adj : adjs) {
          const std::vector<Stmt*>& labels = labelsFor[*adj];
          for (size_t i = 0; i < labels.size(); ++i) {
            auto idx = labels.size() - (i + 1);
            const Stmt* lab = labels[labels.size() - (i + 1)];
            if (!lab) {
              llvm::outs() << "/*no label?!? size = " << labels.size() << " ; i = " << i << " ; idx = " << idx << "*/\n";
            } else if (isa<DefaultStmt>(lab)) {
              defaultBlock = adj;
            } else if (const CaseStmt* cs = dyn_cast<CaseStmt>(lab)) {
              llvm::outs() << "  " << (i == 0 ? "of" : "or") << " ";

              visitCaseValue(cs->getLHS());

              if (i == labels.size() - 1) {
                llvm::outs() << " -> ";
                emitJumpTo(adj, nullptr, aliased_blocks);
              } else {
                llvm::outs() << "\n";
              }
            } else {
              llvm::outs() << "/*non-default, non-case label?!?*/\n";
            }
          }
        }

        if (defaultBlock) {
          llvm::outs() << "\n of _ -> ";
          emitJumpTo(defaultBlock, nullptr, aliased_blocks);
        }

        llvm::outs() << "\nend\n";
  }

  void visitStmtCFG(const Stmt* stmt) {
    // Make sure that binary operators, like || and &&,
    // don't get split up into separate CFG blocks, since
    // the way Clang does so is a pain to reconstruct into
    // well-scoped CPS-style expressions.
    LogicalAndOrTweaker tweaker(tweakedStmts);
    tweaker.TraverseStmt(const_cast<Stmt*>(stmt));

    CFG::BuildOptions BO;
    std::unique_ptr<CFG> cfg = C2F_buildCFG(nullptr, const_cast<Stmt*>(stmt), Ctx, BO);

    if (optDumpCFGs) {
      llvm::outs().flush();
      llvm::errs() << "/*\n";
      //LangOptions LO;
      cfg->dump(CI.getLangOpts(), false);
      llvm::errs() << "\n*/\n";
      llvm::errs().flush();
    }

    if (optDumpOrigSource) {
      llvm::outs() << "/*\n";
      llvm::outs() << FC.getText(*stmt) << "\n";
      llvm::outs() << "*/\n";
    }

    // One not-completely-obvious thing about Clang's CFG construction
    // is that it can lead to "duplicated" statements, potentially across
    // block boundaries. For example::
    //
    //    [B3]
    //      1: ([B5.3]) || [B4.1]
    //      2: l_24 = ((int16_t)((int16_t)(([B3.1]) & l_16) << (int16_t)l_26) % (int16_t)l_59)
    //      Preds (2): B4 B5
    //      Succs (1): B2
    //
    //    [B4]
    //      1: 52693
    //      Preds (1): B5
    //      Succs (1): B3
    //
    //    [B5]
    //      1: l_16 = l_26
    //      2: func_31(((int16_t)15524 << (int16_t)p_12), p_12)
    //      3: [B5.2] != l_26
    //      T: ([B5.3]) || ...
    //      Preds (1): B12
    //      Succs (2): B3 B4
    //
    // Clang pretty-prints statement references of the form [B5.3],
    // but it's just indicating that the same Stmt pointer occurs in
    // the block element list and the LHS of the binary operator.

    // Add all var decls
    StmtMap.clear();
    std::vector<const DeclStmt*> decls = collectDeclsAndBuildStmtMap(cfg);
    markDuplicateVarDecls(decls);

    for (auto d : decls) {
      bool needsVisit = true;
      if (d->isSingleDecl()) {
        if (const VarDecl* vd = dyn_cast<VarDecl>(d->getSingleDecl())) {
          vmpt.noteMutableVar(vd->getName());
          // Unfortunately, all variables must be treated as mutable
          // when we are doing CFG-based generation, because the CFG
          // doesn't respect variable scoping rules.

          // We don't visit the decl itself here because it may refer to
          // out-of-scope variables.
          currentVars.push_back(vd->getName());
          llvm::outs() << emitVarName(vd)
                       << " = PtrRef (prim ref "
                       << zeroValue(vd->getType().getTypePtr()) << ") /*cfg-mutlocal*/";
          currentVars.pop_back();
          needsVisit = false;
        }
      }
      
      if (needsVisit) { visitStmt(d, StmtContext); }
      

      llvm::outs() << ";\n";
    }

    std::map<const CFGBlock*, const CFGBlock*> aliased_blocks;
    // Do a pre-pass to identify aliased blocks
    for (auto it = cfg->rbegin(); it != cfg->rend(); ++it) {
      CFGBlock* cb = *it;
      if (isExitBlock(cb)) continue;
      if (cb->begin() == cb->end() && cb->succ_size() == 1) {
        CFGBlock::AdjacentBlock* ab = cb->succ_begin();
        CFGBlock* next = ab->getReachableBlock();
        if (!next) next = ab->getPossiblyUnreachableBlock();
        if (next) {
          aliased_blocks[cb] = next;
        }
      }
    }

    for (auto it = cfg->rbegin(); it != cfg->rend(); ++it) {
      CFGBlock* cb = *it;
      if (isExitBlock(cb)) continue;

      if (aliased_blocks.find(cb) != aliased_blocks.end()) {
        continue; // don't emit anything for aliased blocks!
      }

      llvm::outs() << "REC " << getBlockName(*cb) << " = {\n";

      //const Stmt* termin = cb->getTerminator().getStmt();
      for (auto cbit = cb->begin(); cbit != cb->end(); ++cbit) {
        CFGElement ce = *cbit;
        if (ce.getKind() == CFGElement::Kind::Statement) {
          if (const Stmt* s = ce.castAs<CFGStmt>().getStmt()) {
            if (auto ds = dyn_cast<DeclStmt>(s)) {
              // If we see a (mutable) variable declaration in a loop,
              // we must re-initialize the variable.
              if (ds->isSingleDecl()) {
                if (const VarDecl* vd = dyn_cast<VarDecl>(ds->getSingleDecl())) {
                  bool isMut = vmpt.isMutableVar(vd->getName());
                  if (vd->hasInit() && isMut) {
                    emitPoke(vd, vd->getInit());
                  } else if (!isMut) {
                    // Non-mutable declarations should be visited in-place.
                    currStmt = s;
                    visitStmt(s, StmtContext);
                    currStmt = nullptr;
                    llvm::outs() << ";\n";
                  }
                }
              } else {
                llvm::outs() << "/*skipped multi decl*/\n";
              }
            } else {
              // Non-declaration statement: visit it regularly.
              currStmt = s;
              visitStmt(s, StmtContext);
              currStmt = nullptr;
              llvm::outs() << ";\n";
            }
          } else {
            llvm::outs() << "/*no stmt?*/\n";
          }
        } else {
          llvm::outs() << "// non-stmt cfg element...\n";
        }
      }

      if (cb->succ_size() == 1) {
        emitJumpTo(cb->succ_begin(), getBlockTerminatorOrLastStmt(cb), aliased_blocks);
      } else if (const SwitchStmt* ss = dyn_cast<SwitchStmt>(cb->getTerminator())) {
        handleSwitchTerminator(cb, ss, aliased_blocks);
      } else if (cb->succ_size() == 2) {
        if (const Stmt* tc = cb->getTerminatorCondition()) {
          // Similar to handleIfThenElse, but with emitJumpTo instead of visitStmt.
          const Stmt* last = getBlockTerminatorOrLastStmt(cb);
          //bool hasVal = stmtHasValue(last);
          //llvm::outs() << "/* hasVal=" << hasVal << "*/ ";
          llvm::outs() << "if ";
          visitStmt(tc, BooleanContext);
          llvm::outs() << " then ";
          emitJumpTo(cb->succ_begin(), last, aliased_blocks);
          llvm::outs() << " else ";
          emitJumpTo(cb->succ_begin() + 1, last, aliased_blocks);
          llvm::outs() << "end";
        } else {
          auto s = cb->succ_begin();
          auto s1 = *s++;
          auto s2 = *s;
          if (s1 && !s2) {
            emitJumpTo(&s1, getBlockTerminatorOrLastStmt(cb), aliased_blocks);
          } else {
            llvm::outs() << "/* two succs but no terminator condition? */\n";
          }
        }
      }

      llvm::outs() << "};\n";

    }

    llvm::outs() << getBlockName(&(cfg->getEntry()), aliased_blocks) << " !;\n"; // emitCall
    StmtMap.clear();
  }

  void handleSwitch(const SwitchStmt* ss) {
    if (ss->getConditionVariable()) {
      llvm::outs() << "/*TODO(c2f) handle var decl in switch*/\n";
    }

    /*
    if (ss->getInit()) {
      visitStmt(ss->getInit());
    }
    */

    llvm::outs() << "case ";
    visitStmt(ss->getCond());
    llvm::outs() << "\n";
    // Assuming the body is a CompoundStmt of CaseStmts...
    visitStmt(ss->getBody(), StmtContext);

/*
    if (ss->isAllEnumCasesCovered()) {
      llvm::outs() << "// all enum cases covered\n";
    } else {
      llvm::outs() << "// not all enum cases (explicitly) covered...\n";
    }
    */

    llvm::outs() << "end\n";

  }

  std::string emitBooleanCoercion(const Type* ty) {
    if (auto rty = tryGetRecordPointee(ty)) {
      return "|> " + recordName(rty->getDecl()) + "_notnil";
    } else return mkFosterBinop("!=", ty, ty) + " " + zeroValue(ty);
  }

  typedef std::vector< std::pair<const clang::Expr*, int> > Indices;

  void emitSubscriptIndex(Indices& indices) {
    llvm::outs() << "(";
    for (size_t i = 0; i < indices.size(); ++i) {
      if (i > 0) { llvm::outs() << " +Int32 "; }
      llvm::outs() << "(";
      visitStmtWithIntCastTo(indices[i].first, "Int32");
      if (indices[i].second > 1) {
        llvm::outs() << " *Int32 " << indices[i].second;
      }
      llvm::outs() << ")";
    }
    llvm::outs() << ")";
  }

  void emitPeek(const Expr* base, Indices& indices) {
    llvm::outs() << "(ptrGetIndex ";
    visitStmt(base);
    llvm::outs() << " ";
    emitSubscriptIndex(indices);
    llvm::outs() << ")";
  }

  template <typename Lam>
  void emitPokeIdx(const Expr* base, Indices& indices,
                   Lam& valEmitter, ContextKind ctx) {
      std::string tynm = tyName(exprTy(base));
      llvm::outs() << "(ptrSetIndex ";
      visitStmt(base);
      llvm::outs() << " ";
      emitSubscriptIndex(indices);
      llvm::outs() << " ";
      valEmitter();

      if (ctx == ExprContext) {
        llvm::outs() << "; "; emitPeek(base, indices);
      }
      // TODO BooleanContext
      llvm::outs() << ");";
  }

  template <typename Lam>
  void emitPoke_(const Expr* ptr, Lam valEmitter, ContextKind ctx) {
      //std::string tynm = tyName(exprTy(ptr));
      Indices indices;
      if (auto base = extractBaseAndArraySubscripts(ptr, indices)) {
        emitPokeIdx(base, indices, valEmitter, ctx);
      } else {
        // If we have something like (c = (b = a)),
        // translate it to (a >^ b; b) >^ c
        llvm::outs() << "(ptrSet (";
        visitStmt(ptr, AssignmentTarget);
        llvm::outs() << ") (";
        valEmitter();
        llvm::outs() << ")";
        if (ctx == ExprContext) {
          llvm::outs() << "; "; visitStmt(ptr);
        } else if (ctx == BooleanContext) {
          llvm::outs() << "; "; visitStmt(ptr);
          llvm::outs() << " " << emitBooleanCoercion(exprTy(ptr));
        }
        llvm::outs() << ");";
      }
  }

  void emitPoke(const Expr* ptr, const Expr* val, ContextKind ctx) {
    emitPoke_(ptr, [=]() { visitStmt(val); }, ctx);
  }

  void emitPoke(const VarDecl* ptr, const Expr* val) {
      llvm::outs() << "(ptrSet " << emitVarName(ptr) << " (";
      visitStmt(val);
      llvm::outs() << "));";
    /*
      llvm::outs() << "((";
      visitStmt(val);
      llvm::outs() << ") >^ " << emitVarName(ptr) << ");";
      */
  }

  bool isNumericLiteral(const Stmt* stmt) {
    return (isa<IntegerLiteral>(stmt) || isa<FloatingLiteral>(stmt));
  }

  bool tryHandleAtomicExpr(const Stmt* stmt, ContextKind ctx) {
    if (const ConditionalOperator* co = dyn_cast<ConditionalOperator>(stmt)) {
      handleIfThenElse(ctx, AnIfExpr, co->getCond(), co->getTrueExpr(), co->getFalseExpr());
      return true;
    }
    if (isNumericLiteral(stmt)) {
      visitStmt(stmt, ctx); return true;
    }

    return false;
  }

  bool isDeclRefOf(const Expr* e, const Decl* d) {
    if (const DeclRefExpr* dre = dyn_cast<DeclRefExpr>(e)) {
      return dre->getDecl() == d;
    }
    return false;
  }

  // Precondition: op should not be "&&" or "||".
  const Expr* bindOperator(const Expr* e, const std::string& op, const Decl* d) {
    if (const BinaryOperator* boe = dyn_cast<BinaryOperator>(e)) {
      if (boe->getOpcodeStr() == op) {
        if (isDeclRefOf(boe->getLHS()->IgnoreParenImpCasts(), d)) {
          return boe->getRHS();
        }
      }
    }
    return nullptr;
  }

  bool isIncrementOf(const Expr* e, const Decl* d) {
    if (const UnaryOperator* unop = dyn_cast<UnaryOperator>(e)) {
      return unop->isIncrementOp() && isDeclRefOf(unop->getSubExpr()->IgnoreParenImpCasts(), d);
    }
    return false;
  }

  bool tryHandleEnumRange(const ForStmt* fs) {
    return false; // needs more work to be correct
    if (const Stmt* init = fs->getInit()) {
      if (const BinaryOperator* init_binop = dyn_cast<BinaryOperator>(init)) {
        if (init_binop->getOpcodeStr() == "=") {
          if (const DeclRefExpr* dre = dyn_cast<DeclRefExpr>(init_binop->getLHS())) {
            if (isIncrementOf(fs->getInc(), dre->getDecl())) {
              const Expr* cmplt  = bindOperator(fs->getCond(), "<",  dre->getDecl());
              const Expr* cmplte = bindOperator(fs->getCond(), "<=", dre->getDecl());
              if (cmplt || cmplte) {
                std::string ty = tyName(exprTy(dre->getDecl()));
                if (cmplt) llvm::outs() << "enumRange (";
                else if (cmplte) llvm::outs() << "enumRangeInc (";
                visitStmt(init_binop->getRHS());
                llvm::outs() << ") (";
                if (cmplt) visitStmt(cmplt);
                else if (cmplte) visitStmt(cmplte);
                // give the loop var a different name, since the actual declaration
                // is (by definition) mutable.
                llvm::outs() << ") { " << dre->getDecl()->getName() << "_loop"
                             << " : " << ty << " =>" << "\n";
                visitStmt(fs->getBody());
                llvm::outs() << "}";
                return true;
              }
            }
          }
        }
      }
    }
    return false;
  }

  template <typename T>
  void translateWhileLoop(const T* stmt, std::string loopname, const Stmt* extra = nullptr) {
    llvm::outs() << loopname << " { ";
      if (stmt->getCond()) {
        visitStmt(stmt->getCond(), BooleanContext);
      } else llvm::outs() << "True";
    llvm::outs() << " } {\n";
      visitStmt(stmt->getBody(), StmtContext);
      // If the body wasn't a compound, we'll be missing a semicolon...
      if (extra) { llvm::outs() << "\n"; visitStmt(extra, StmtContext); }

      llvm::outs() << ";\n()";
    llvm::outs() << "}";
  }

  void translateGeneralForLoop(const ForStmt* fs) {
    if (fs->getInit()) { visitStmt(fs->getInit(), StmtContext); llvm::outs() << ";\n"; }
    translateWhileLoop(fs, "while", fs->getInc());
  }

  void handleIncrDecr(const std::string& incdec, const UnaryOperator* unop) {
      if (const ArraySubscriptExpr* ase = dyn_cast<ArraySubscriptExpr>(unop->getSubExpr())) {
        llvm::outs() << "(" << incdec << "Array" << tyName(unop) << " ";
        visitStmt(ase->getBase());
        llvm::outs() << " ";
        visitStmt(ase->getIdx());
        llvm::outs() << ")";
      } else {
        // Pointer-typed things can use a generic version;
        // non-pointer types require specific versions.
        std::string version = (unop->getType().getTypePtr()->isPointerType())
                              ? "" : fosterizedNameChars(tyName(unop));
        llvm::outs() << "(" << incdec << version << " ";
        visitStmt(unop->getSubExpr(), AssignmentTarget);
        llvm::outs() << ")";
      }
  }

  const clang::Expr* extractBaseAndArraySubscripts(const clang::Stmt* e, Indices& indices) {
    if (const ArraySubscriptExpr* ase = dyn_cast<ArraySubscriptExpr>(e)) {
      // Extract the number of slots represented by the base type
      // defaulting to one for non-array types.
      uint64_t n = 1; const clang::Type* eltTy = nullptr;
      tryBindConstantSizedArrayType(ase->getType().getTypePtr(), eltTy, n);

      indices.push_back( std::make_pair(ase->getIdx(), n ));
      auto rv = extractBaseAndArraySubscripts(ase->getBase()->IgnoreParenImpCasts(), indices);
      return (rv ? rv : ase->getBase());
    } else return nullptr;
  }

/* TODO
code like sizeof(mathlib)/sizeof((mathlib)[0])
should be translated to the statically-known length
of the array type for mathlib.

The corresponding AST to be matched is
    BinaryOperator ... 'unsigned long' '/'
    |-UnaryExprOrTypeTraitExpr ... 'unsigned long' sizeof
    | `-ParenExpr ... 'const luaL_Reg [28]' lvalue
    |   `-DeclRefExpr ... 'const luaL_Reg [28]' lvalue Var 0x7f8daa905398 'mathlib' 'const luaL_Reg [28]'
    `-UnaryExprOrTypeTraitExpr ... 'unsigned long' sizeof
      `-ParenExpr ... 'const luaL_Reg':'const struct luaL_Reg' lvalue
        `-ArraySubscriptExpr ... 'const luaL_Reg':'const struct luaL_Reg' lvalue
          |-ImplicitCastExpr ... 'const luaL_Reg *' <ArrayToPointerDecay>
          | `-ParenExpr ... 'const luaL_Reg [28]' lvalue
          |   `-DeclRefExpr ... 'const luaL_Reg [28]' lvalue Var 0x7f8daa905398 'mathlib' 'const luaL_Reg [28]'
          `-IntegerLiteral ... 'int' 0
*/

  bool isComparisonOp(const std::string& op) {
    return (op == "!=" || op == "=="
         || op == "<=" || op == ">="
         || op == "<"  || op == ">");
  }

  std::string getBinaryOperatorString(const BinaryOperator* binop) {
    auto it = tweakedStmts.find(binop);
    if (it != tweakedStmts.end()) {
      if (it->second == BO_LAnd) return "&&";
      if (it->second == BO_LOr)  return "||";
    }
    return binop->getOpcodeStr();
  }

  void handleBinaryOperator(const BinaryOperator* binop,
                            ContextKind ctx) {
    std::string op = getBinaryOperatorString(binop);

    bool isBooleanContext = ctx == BooleanContext;
    if (op == "=") {
      handleAssignment(binop, ctx);
    } else if (op == ",") {
      llvm::outs() << "( _ = ";
      visitStmt(binop->getLHS(), StmtContext);
      llvm::outs() << ";\n";
      visitStmt(binop->getRHS(), ctx);
      llvm::outs() << " )";
    } else if (op == "&&" || op == "||") {
      bool needsBoolToIntCoercion = !isBooleanContext;
      if (needsBoolToIntCoercion) { llvm::outs() << "if "; }

      std::string tgt = (op == "&&" ? "`andand`" : "`oror`");
      llvm::outs() << "({ ";
      visitStmt(binop->getLHS(), BooleanContext);
      llvm::outs() << " } " << tgt << " { ";
      visitStmt(binop->getRHS(), BooleanContext);
      llvm::outs() << " })";

      if (needsBoolToIntCoercion) { llvm::outs() << " then 1 else 0 end"; }
    } else {
      // TODO account for the fact that compound operations may occur in a
      // different intermediate type...
      bool isComparison = isComparisonOp(op);
      if ((!isBooleanContext) && isComparison) { llvm::outs() << "if "; }
      if (isBooleanContext && !isComparison) { llvm::outs() << "("; }

      const Type* ty = exprTy(binop->getLHS());
      std::string tgt = mkFosterBinop(op, ty, exprTy(binop->getRHS()));

      bool isRecordPtrNilComparison = false;

      if (auto rty = tryGetRecordPointee(ty)) {
        if (op == "==" || op == "!=") {
          auto npstatus = binop->getRHS()->isNullPointerConstant(*Ctx, clang::Expr::NPC_ValueDependentIsNull);
          isRecordPtrNilComparison = npstatus != clang::Expr::NPCK_NotNull;
          tgt = recordName(rty->getDecl()) + (op == "==" ? "_isnil" : "_notnil");
        }
      }
      
      llvm::outs() << "(";
      visitStmt(binop->getLHS(), (binop->isCompoundAssignmentOp() ? AssignmentTarget : ExprContext));
      if (isRecordPtrNilComparison) {
        llvm::outs() << "|> " + tgt;
      } else {
        llvm::outs() << " " << tgt << " ";

        if (tgt == "+Ptr" || tgt == "-Ptr") {
          visitStmtWithIntCastTo(binop->getRHS(), "Int32");
        } else {
          visitStmt(binop->getRHS());
        }
      }
      llvm::outs() << ")";

      if (isBooleanContext && !isComparison) {
          llvm::outs() << " " << emitBooleanCoercion(exprTy(binop)) << "/*L1390*/)"; }
      if ((!isBooleanContext) && isComparison) { llvm::outs() << " then 1 else 0 end"; }
    }
  }

  // clang::UnaryOperatorKind
  void handleUnaryOperator(const UnaryOperator* unop, ContextKind ctx) {
    if (unop->getOpcode() == UO_LNot) {
      // We translate logical-not to either an integer or boolean:
      //   (!0 + 2)   ==> ((if 0 !=Int32 0 then 1 else 0) +Int32 2)
      //  if (!0) ... ==>   if 0 !=Int32 0 then ...
      if (ctx == ExprContext) {
        llvm::outs() << "(if ";
        visitStmt(unop->getSubExpr(), BooleanContext);
        llvm::outs() << " then 0 else 1 end)";
      } else {
        // If ctx is BooleanContext, there'll be a coercion inserted
        // around the call to handleUnaryOperator, which means the
        // subexpr here should be visited in expr context.
        llvm::outs() << "(if ";
        visitStmt(unop->getSubExpr(), BooleanContext);
        llvm::outs() << " then 0 else 1 end)";
      }
    } else if (unop->getOpcode() == UO_Not) {
      llvm::outs() << "(bitnot-" + tyName(unop) << " ";
      visitStmt(unop->getSubExpr());
      llvm::outs() << ")";
    } else if (unop->getOpcode() == UO_Minus) {
      // We make the minus sign a lexical part of numeric literals,
      // rather than an operator, which means it cannot have intervening
      // whitespace. Other cases turn into zero-minus-whatever.
      if (isNumericLiteral(unop->getSubExpr())) {
        llvm::outs() << "-";
        visitStmt(unop->getSubExpr());
      } else {
        auto ty = exprTy(unop->getSubExpr());
        std::string tgt = mkFosterBinop("-", ty, ty);
        llvm::outs() << "(0 " << tgt << " ";
        visitStmt(unop->getSubExpr());
        llvm::outs() << ")";
      }
    } else if (unop->getOpcode() == UO_Plus) {
      // Unary plus gets ignored, basically.
      visitStmt(unop->getSubExpr());
    } else if (unop->getOpcode() == UO_PreDec) {
      handleIncrDecr("ptrDecr", unop);
    } else if (unop->getOpcode() == UO_PostDec) {
      handleIncrDecr("ptrPostDecr", unop);
    } else if (unop->getOpcode() == UO_PostInc) {
      handleIncrDecr("ptrPostIncr", unop);
    } else if (unop->getOpcode() == UO_PreInc) {
      handleIncrDecr("ptrIncr", unop);
    } else if (unop->getOpcode() == UO_AddrOf) {
      Indices indices;
      if (auto base = extractBaseAndArraySubscripts(unop->getSubExpr(), indices)) {
        // Translate (&a[i]) as (ptrPlus a i)
        llvm::outs() << "(ptrPlus ";
        visitStmt(base);
        llvm::outs() << " ";
        emitSubscriptIndex(indices);
        llvm::outs() << ")";
      } else {
        visitStmt(unop->getSubExpr(), AssignmentTarget);
      }
    } else if (unop->getOpcode() == UO_Deref) {
      // Relevant testcases:
      //   nestedarrs_001.c
      //                     int* p = ...; *p = 3;
      //                                    ^- not mutable local ===> ptrSet p 3
      //   ptr_ref_001.c
      //   ptr_ref_002.c
      //          
      //    int bar(int a) { int* z = &a; --a; ++*z; return foo(z) + *z; }
      //                                          ^                   ^
      //                                          |     not assignment ctx ==> ptrGet z
      //                                          +- declrefofmutablealias ==> ptrIncr (z)
      //
      //    int baz(int a) { int* z = &a; --a; ++*z; int* q1 = ++z; --z; return foo(z) + *z; }
      //                                          ^-  !DRMA                ==> ptrIncr (ptrGet z)
      if (ctx == AssignmentTarget) {
        if (optC2FVerbose) { llvm::outs() << "/*L1774->*/ "; }
        visitStmt(unop->getSubExpr()); // elide deref, thus not assignment context anymore
      } else {
        llvm::outs() << "(ptrGet ";
        //llvm::outs() << "/* " << tyName(exprTy(unop->getSubExpr())) << " */";
        visitStmt(unop->getSubExpr(), ctx);
        llvm::outs() << ")";
        if (optC2FVerbose) { llvm::outs() << "/*2150*/"; }
      }
    } else if (unop->getOpcode() == UO_Extension) {
      visitStmt(unop->getSubExpr());
    } else {
      llvm::outs() << "/* Unhandled unary operator:\n";
      llvm::outs().flush();
      unop->dump();
      llvm::errs().flush();
      llvm::outs() << "\n*/\n";
      llvm::outs() << FC.getText(*unop) << "\n";
    }
  }

/*
  bool isDeclRefOfMutableAlias(const ValueDecl* d) { return mutableLocalAliases[d->getName()]; }

  bool isDeclRefOfMutableAlias(const Expr* e) {
    if (auto dre = dyn_cast<DeclRefExpr>(e->IgnoreParenImpCasts())) {
      return isDeclRefOfMutableAlias(dre->getDecl());
    }
    return false;
  }
*/

/*
  bool isDeclRefOfMutableLocal(const Expr* e) {
    if (auto dre = dyn_cast<DeclRefExpr>(e->IgnoreParenImpCasts())) {
      return mutableLocals[dre->getDecl()->getName()]
            || isDeclRefOfMutableAlias(e);
    }
    return false;
  }
  */

  bool isDeclNamed(const std::string& nm, const Expr* e) {
   if (const DeclRefExpr* dre = dyn_cast<DeclRefExpr>(e)) {
     return dre->getDecl()->getName() == nm;
   }
   return false;
  }

  const Type* bindSizeofType(const Expr* e) {
    if (const UnaryExprOrTypeTraitExpr* ue = dyn_cast<UnaryExprOrTypeTraitExpr>(e)) {
      if (ue->getKind() == UETT_SizeOf) {
        if (ue->isArgumentType()) {
          return ue->getArgumentType().getTypePtr();
        } else {
          return exprTy(ue->getArgumentExpr());
        }
      }
    }
    return nullptr;
  }

  bool tryHandleCallBuiltin(const CallExpr* ce) {
    if (const DeclRefExpr* dre = dyn_cast<DeclRefExpr>(ce->getCallee()->IgnoreParenImpCasts())) {
      if (dre->getDecl()->getNameAsString() == "__builtin_clz") {
        llvm::outs() << "cltz-" << tyName(exprTy(ce->getArg(0)));
        return true;
      }
      if (dre->getDecl()->getNameAsString() == "__builtin_inff") {
        llvm::outs() << "c2f_inf_f32";
        return true;
      }
      // TODO handle more builtins
    }
    return false;
  }

  bool tryHandleCallMallocCasted(const CStyleCastExpr* e) {
    if (const CallExpr* ce = dyn_cast<CallExpr>(e->getSubExpr())) {
      return tryHandleCallMalloc(ce, exprTy(e));
    }
    return false;
  }

  void handleCall(const CallExpr* ce) {
    llvm::outs() << "(";
    if (tryHandleCallBuiltin(ce)) {
    } else {
      visitStmt(ce->getCallee());
    }
    for (const Expr* e : ce->arguments()) {
      llvm::outs() << " ";
      visitStmt(e);
    }
    if (ce->getNumArgs() == 0) { llvm::outs() << " !"; } // emitCall
    llvm::outs() << ")";
  }

  bool tryHandleCallPrintf(const CallExpr* ce) {
    // TODO handle fprintf, etc.
    if (!isDeclNamed("printf", ce->getCallee()->IgnoreParenImpCasts())) return false;

    if (ce->getNumArgs() == 1) {
      // Assume one-arg printf means literal text.
      llvm::outs() << "(printStr ";
      visitStmt(ce->getArg(0));
      llvm::outs() << ")";
      return true;
    }

    if (auto slit = dyn_cast<StringLiteral>(ce->getArg(0)->IgnoreParenImpCasts())) {
      const std::string& s = slit->getString();
      bool isFreeBSDkprintf = false;
      C2F_FormatStringHandler handler(s, s.c_str(), *Ctx, ce, *this);
      clang::analyze_format_string::ParsePrintfString(handler, &s[0], &s[s.size()],
          CI.getLangOpts(), CI.getTarget(), isFreeBSDkprintf);
      return true;
#if 0
      if (slit->getString() == "%d\n") {
        std::string tynm = tyName(ce->getArg(1)->getType().getTypePtr());
        std::string printfn;
        if (tynm == "Int8") printfn = "print_i8";
        if (tynm == "Int32") printfn = "print_i32";
        if (tynm == "Int64") printfn = "print_i64";
        if (printfn.empty()) return false;

        llvm::outs() << "(" << printfn << " ";
        visitStmt(ce->getArg(1));
        llvm::outs() << ")";
        return true;
      } else if (slit->getString() == "%f\n") {
        std::string tynm = tyName(ce->getArg(1)->getType().getTypePtr());
        std::string printfn;
        if (tynm == "Float32") printfn = "print_float_f32";
        if (tynm == "Float64") printfn = "print_float_f64";
        if (printfn.empty()) return false;

        llvm::outs() << "(" << printfn << " ";
        visitStmt(ce->getArg(1));
        llvm::outs() << ")";
        return true;

      } else if (slit->getString() == "%s\n") {
        std::string tynm = tyName(ce->getArg(1)->getType().getTypePtr());
        if (tynm == "(Ptr Int8)") {
          llvm::outs() << "(printStr ";
          visitStmt(ce->getArg(1));
          llvm::outs() << ")";
          return true;
        }
        llvm::errs() << "printf %s format for type " << tynm << "\n";
        return false;
      } else if (slit->getString() == "0x%X\n"
              || slit->getString() == "0x%lX\n"
              || slit->getString() == "0x%llX\n") {
        // TODO force tynm to be Int64 for %llX ?
        std::string tynm = tyName(ce->getArg(1)->getType().getTypePtr());
        std::string printfn;
        if (tynm == "Int32") printfn = "print_i32x";
        if (tynm == "Int64") printfn = "print_i64x";
        if (printfn.empty()) return false;

        llvm::outs() << "(" << printfn << " ";
        visitStmt(ce->getArg(1));
        llvm::outs() << ")";
        return true;
      }
  #endif
    }
    return false;
  }

  // Emit calls to free() as comments, since we're presumably doing GC.
  bool tryHandleCallFree(const CallExpr* ce) {
    if (!isDeclNamed("free", ce->getCallee()->IgnoreParenImpCasts())) return false;
    if (ce->getNumArgs() != 1) return false;
    llvm::outs() << "// "; handleCall(ce); llvm::outs() << "\n";
    llvm::outs() << "()";
    return true;
  }

  // Given an expression presumed to be an element count (in bytes),
  // as used in memset/memcmp/etc, try to extract the underlying
  // number of elements (rather than bytes).
  //
  // Given e = (sizeof X) * C, return C
  // Otherwise, return e, which is (presumably) either a non-sizeof constant,
  // or a sizeof expr used as a count of byte-sized elements.
  const Expr* extractElementCount(const Expr* e) {
    if (const BinaryOperator* binop = dyn_cast<BinaryOperator>(e)) {
      if (binop->getOpcodeStr() != "*") return nullptr;

      const Type* sztyL = bindSizeofType(binop->getLHS());
      const Type* sztyR = bindSizeofType(binop->getRHS());
      if (sztyL && (!sztyR)) return binop->getRHS();
      if ((!sztyL) && sztyR) return binop->getLHS();
      return nullptr;
    }
    return e;
  }

  const Type* getElementType(const Type* ptrOrArrayType) {
    if (auto pty = dyn_cast<clang::PointerType>(ptrOrArrayType)) {
      return pty->getPointeeType().getTypePtr();
    }
    if (auto pty = dyn_cast<clang::ArrayType>(ptrOrArrayType)) {
      return pty->getElementType().getTypePtr();
    }
    return ptrOrArrayType;
  }

  void visitStmtWithIntCastTo(const Expr* e, const std::string& dstTy) {
    auto srcTy = tyName(exprTy(e));
    if (srcTy == dstTy
       || isa<CharacterLiteral>(e)
       || guaranteedNotToTruncate(e, dstTy, exprTy(e))) {
      visitStmt(e);
    } else {
      llvm::outs() << "(" << intCastFromTo(srcTy, dstTy, exprTy(e)->isSignedIntegerType()) << " ";
      visitStmt(e);
      llvm::outs() << ")";
    }
  }

  // Recognize calls of the form memcpy(A1, A2, sizeof(T) * SIZE);
  // and emit                 ptrMemcpy A1  A2 SIZE
  bool tryHandleCallMemop_(const CallExpr* ce, const std::string& variant) {
    if (!isDeclNamed("mem" + variant, ce->getCallee()->IgnoreParenImpCasts())) return false;
    if (ce->getNumArgs() != 3) return false;

    if (auto count = extractElementCount(ce->getArg(2)->IgnoreParenImpCasts())) {
      llvm::outs() << "(ptrMem" << variant << " ";
      visitStmt(ce->getArg(0));
      llvm::outs() << " ";
      visitStmt(ce->getArg(1));
      llvm::outs() << " ";

      visitStmtWithIntCastTo(count, "Int32");

      if (variant == "cmp") {
        auto ty = getElementType(exprTy(ce->getArg(0)->IgnoreParenImpCasts()));
        std::string suffix = (ty->hasSignedIntegerRepresentation()) ? "S" : "U";
        llvm::outs() << " " << mkFosterBinop("cmp-" + suffix, ty, ty);
      }
      llvm::outs() << ")";
      return true;
    }
    return false;
  }

  // Recognize calls of the form memset(ARR, VAL, sizeof(T) * SIZE);
  // and emit                 ptrMemset ARR VAL SIZE
  bool tryHandleCallMemop(const CallExpr* ce) {
    return tryHandleCallMemop_(ce, "cpy")
        || tryHandleCallMemop_(ce, "set")
        || tryHandleCallMemop_(ce, "cmp");
  }

  bool tryHandleCallMalloc(const CallExpr* ce, const Type* result_typ) {
    if (!isDeclNamed("malloc", ce->getCallee()->IgnoreParenImpCasts())) return false;
    if (ce->getNumArgs() != 1) return false;
    // Recognize calls of the form malloc(sizeof(T) * EXPR);
    // and emit               strLit (allocDArray:[T] EXPR)
    if (const BinaryOperator* binop = dyn_cast<BinaryOperator>(ce->getArg(0)->IgnoreParenImpCasts())) {
      if (binop->getOpcodeStr() != "*") return false;
      const Type* sztyL = bindSizeofType(binop->getLHS());
      const Type* sztyR = bindSizeofType(binop->getRHS());
      if (sztyL || sztyR || result_typ) {
        const Type* szty = sztyL ? sztyL
                         : sztyR ? sztyR
                         : result_typ;
        if (result_typ && szty != result_typ) {
          llvm::outs() << "// WARNING: conflicting types for this malloc... (" << tyName(result_typ) << ")\n";
        }
        llvm::outs() << "(ptrOfArr (newDArray0:[" << tyName(szty) << "] ";
        visitStmtWithIntCastTo(sztyL ? binop->getRHS() :  binop->getLHS(), "Int32");
        llvm::outs() << " { i => " << zeroValue(szty) << " }";
        llvm::outs() << "))";
        return true;
      }
    } else {
      // Recognize calls of the form malloc(sizeof(T));
      // and emit T's zero constructor.
      if (const Type* ty = bindSizeofType(ce->getArg(0)->IgnoreParenImpCasts())) {
        llvm::outs() << zeroValue(ty);
        return true;
      }
    }
    return false;
  }

  std::string recordName(const RecordDecl* rd) {
    std::string name = rd->getName();
    if (TypedefNameDecl* tnd = rd->getTypedefNameForAnonDecl()) {
      name = tnd->getName();
    }
    if (name == "") {
      name = getRecordDeclName(rd);
    }
    return fosterizedTypeName(name);
  }

  std::string zeroValueRecord(const RecordDecl* rd) {
    std::string name = recordName(rd);

    if (name == "") {
      llvm::outs() << "// TODO handle this better...\n";
      llvm::errs() << "anon record\n";
      rd->dump();
      llvm::outs() << FC.getText(*rd) << "\n";
      return "";
    }

    std::string rv = "(" + name;
    for (auto d : rd->decls()) {
      if (const FieldDecl* fd = dyn_cast<FieldDecl>(d)) {
        rv = rv + " " + zeroValueField(fd);
      }
    }
    return rv + ")";
  }

  std::string zeroValueField(const FieldDecl* fd) {
    if (globals.fpt.isPointeryField(fd)) {
      return "(mkField PtrNil)";
    } else {
      return "(mkField " + zeroValue(exprTy(fd)) + " )";
    }
  }

  const RecordType* tryGetRecordPointee(const Type* typ) {
    if (auto pty = dyn_cast<PointerType>(typ)) {
      return bindRecordType(pty->getPointeeType().getTypePtr());
    }
    return nullptr;
  }

  std::string zeroValue(const Type* typ) {
    if (typ->isFloatingType()) return "0.0";
    if (typ->isIntegerType()) return "0";
    if (auto rty = tryGetRecordPointee(typ)) {
      if (!currentVars.empty() && vmpt.isPointeryVar(currentVars.back())) {
        return "PtrNil";
      } else {
        return recordName(rty->getDecl()) + "_nil";
      }
    }
    if (typ->isPointerType()) return "PtrNil";
    if (auto tty = dyn_cast<TypedefType>(typ)) {
      return zeroValue(tty->desugar().getTypePtr());
    }
    if (auto rty = dyn_cast<ElaboratedType>(typ)) {
      return zeroValue(rty->getNamedType().getTypePtr());
    }
    if (auto rty = dyn_cast<RecordType>(typ)) {
      return zeroValueRecord(rty->getDecl());
    }

    {
      uint64_t size = 0; const Type* eltTy = nullptr;
      if (tryBindConstantSizedArrayType(typ, eltTy, size)) {
        return "(ptrOfArr (newDArray " + s(size) + " { i => " + zeroValue(eltTy) + "}))";
      }
    }

    return "None";
  }

  void visitWithDerefIf(const Expr* e, bool shouldDeref) {
    if (shouldDeref) {
      llvm::outs() << "(ptrGet ";
    }
    visitStmt(e, ExprContext);
    if (shouldDeref) {
      llvm::outs() << ")";
      if (optC2FVerbose) { llvm::outs() << "/*2516*/"; }
    }
  }

  void handleAssignment(const BinaryOperator* binop, ContextKind ctx) {
    // TODO handle implicit deref if me->isArrow()
    if (const MemberExpr* me = dyn_cast<MemberExpr>(binop->getLHS())) {
      // translate p->f = x;  to  (set_pType_f p x)
      if (optC2FVerbose) { llvm::outs() << "/* ctx : " << ctx << " */"; }
      const Expr* base = nullptr;
      llvm::outs() << "(set_" << fieldAccessorName(me, base, false) << " ";
      llvm::outs() << "(";
      //visitStmt(base, ExprContext);
      visitWithDerefIf(base, me->isArrow() && vmpt.isMutableVar(base));
      llvm::outs() << ") (";
      visitStmt(binop->getRHS());
      llvm::outs() << ")";

      // If we have code like blah = (p->f = x)
      // we need the assignment of p->f to evaluate to p->f.
      if (ctx == ExprContext) {
        llvm::outs() << "; ";
        llvm::outs() << fieldAccessorName(me, base, false) << " " << "(";
          //visitStmt(base, ExprContext);
          visitWithDerefIf(base, me->isArrow() && vmpt.isMutableVar(base));
        llvm::outs() << ")";
      }
      llvm::outs() << ")";
    } else {
      // translate v = x;  to  (x) >^ v;
      emitPoke(binop->getLHS(), binop->getRHS(), ctx);
    }
  }

  void handleCompoundAssignment(const BinaryOperator* binop, ContextKind ctx) {
    std::string op = binop->getOpcodeStr();
    if (op.back() == '=') op.pop_back();

    std::string tgt = mkFosterBinop(op, exprTy(binop->getLHS()), exprTy(binop->getRHS()));

    if (const MemberExpr* me = dyn_cast<MemberExpr>(binop->getLHS())) {
      // translate p->f OP= v;  to  (set_pType_f p ((pType_f p) OP v))
      const Expr* base = nullptr;
      std::string accessor = fieldAccessorName(me, base, false);
      llvm::outs() << "(set_" << accessor << " ";
      llvm::outs() << "(";
      //visitStmt(base, ExprContext);
      visitWithDerefIf(base, me->isArrow() && vmpt.isMutableVar(base));
      llvm::outs() << ") (";

        llvm::outs() << "(" << accessor << " ";
        llvm::outs() << "(";
        visitStmt(base, ExprContext); // ExprContext?
        llvm::outs() << ")";
        llvm::outs() << ")";

        llvm::outs() << " " << tgt << " ";

        if (tgt == "-Ptr" || tgt == "+Ptr") {
          visitStmtWithIntCastTo(binop->getRHS(), "Int32");
        } else {
          visitStmt(binop->getRHS());
        }
        
      llvm::outs() << ")";
      llvm::outs() << ")";
    } else {
      // translate v OP= x;  to  (v^ OP x) >^ v
      emitPoke_(binop->getLHS(), [=]() {
        llvm::outs() << "(";
        visitStmt(binop->getLHS(), ExprContext);
        llvm::outs() << " " << tgt << " ";
        {
          std::string srcTy = tyName(exprTy(binop->getRHS()));
          std::string dstTy = tyName(exprTy(binop->getLHS()));
          // Usually integral type mismatches are explicitly represented with
          // an IntegralCast node in the AST, but for some reason that doesn't
          // happen with compound assignments.
          if (srcTy != dstTy && !(exprTy(binop->getLHS())->isPointerType())) {
            llvm::outs() << "("
              << intCastFromTo(srcTy, dstTy, exprTy(binop->getRHS())->isSignedIntegerType())
              << " ";
            visitStmt(binop->getRHS(), ExprContext);
            llvm::outs() << " )";
          } else {
            visitStmt(binop->getRHS(), ExprContext);
          }
        }
        llvm::outs() << ")";
      }, ctx);
    }
  }

  bool guaranteedNotToTruncate(const Expr* e, const std::string& ty, const Type* t) {
    // t and ty are the destination type; the source "type" is irrelevant for literals.
    if (ty == "Int8") {
      return t->isSignedIntegerType()
                ? isTrivialIntegerLiteralInRange(e, 0 - (1 << 7), (1 << 7) - 1)
                : isTrivialIntegerLiteralInRange(e, 0           , (1 << 8) - 1);
    } else if (ty == "Int16") {
      return t->isSignedIntegerType()
                ? isTrivialIntegerLiteralInRange(e, 0 - (1 << 15), (1 << 15) - 1)
                : isTrivialIntegerLiteralInRange(e, 0            , (1 << 16) - 1);
    } else if (ty == "Int32") {
      return t->isSignedIntegerType()
                ? isTrivialIntegerLiteralInRange(e, 0 - (1 << 31), (1 << 31) - 1)
                : isTrivialIntegerLiteralInRange(e, 0            , 4294967295);
    } else if (ty == "Int64") {
      return true;
    }

    return false;
  }

  bool isLargerOrEqualSizedType(const Type* t1, const Type* t2) {
    return Ctx->getTypeSize(t1) >= Ctx->getTypeSize(t2);
  }

  bool isNestedCastThatCancelsOut(const CastExpr* ce) {
/* Example:
ce:  | | |-ImplicitCastExpr 0x55b68a4daf48 <./http_parser.h:289:41, col:75> 'unsigned int' <IntegralCast>
     | | | `-ParenExpr 0x55b68a4daf00 <col:41, col:75> 'enum http_errno':'enum http_errno'
sce: | | |   `-CStyleCastExpr 0x55b68a4daed8 <col:42, col:65> 'enum http_errno':'enum http_errno' <IntegralCast>
     | | |     `-ImplicitCastExpr 0x55b68a4daec0 <col:60, col:65> 'unsigned int' <LValueToRValue>
     | | |       `-MemberExpr 0x55b68a4dae68 <col:60, col:65> 'unsigned int' lvalue bitfield ->http_errno 0x55b68a42fcc0
*/
    if (const CastExpr* sce = dyn_cast<CastExpr>(ce->getSubExpr()->IgnoreParens())) {
      if (exprTy(ce) == exprTy(sce->getSubExpr())) {
        // The cast is only a no-op if the size
        // of sce's type is >= the size of ce's type.
        return isLargerOrEqualSizedType(exprTy(sce), exprTy(ce));
      }
    }
    return false;
  }

  std::string intCastFromTo(const std::string& srcTy, const std::string& dstTy, bool isSigned) {
    if (srcTy == "Int16" && dstTy == "Int8" ) return "trunc_i16_to_i8";
    if (srcTy == "Int32" && dstTy == "Int8" ) return "trunc_i32_to_i8";
    if (srcTy == "Int64" && dstTy == "Int8" ) return "trunc_i64_to_i8";
    if (srcTy == "Int32" && dstTy == "Int16") return "trunc_i32_to_i16";
    if (srcTy == "Int64" && dstTy == "Int16") return "trunc_i64_to_i16";
    if (srcTy == "Int64" && dstTy == "Int32") return "trunc_i64_to_i32";
    if (srcTy == "Int8"  && dstTy == "Int16" && isSigned) return "sext_i8_to_i16";
    if (srcTy == "Int8"  && dstTy == "Int32" && isSigned) return "sext_i8_to_i32";
    if (srcTy == "Int8"  && dstTy == "Int64" && isSigned) return "sext_i8_to_i64";
    if (srcTy == "Int16" && dstTy == "Int32" && isSigned) return "sext_i16_to_i32";
    if (srcTy == "Int16" && dstTy == "Int64" && isSigned) return "sext_i16_to_i64";
    if (srcTy == "Int32" && dstTy == "Int64" && isSigned) return "sext_i32_to_i64";
    if (srcTy == "Int8"  && dstTy == "Int16" && !isSigned) return "zext_i8_to_i16";
    if (srcTy == "Int8"  && dstTy == "Int32" && !isSigned) return "zext_i8_to_i32";
    if (srcTy == "Int8"  && dstTy == "Int64" && !isSigned) return "zext_i8_to_i64";
    if (srcTy == "Int16" && dstTy == "Int32" && !isSigned) return "zext_i16_to_i32";
    if (srcTy == "Int16" && dstTy == "Int64" && !isSigned) return "zext_i16_to_i64";
    if (srcTy == "Int32" && dstTy == "Int64" && !isSigned) return "zext_i32_to_i64";
    return "/*unhandled cast from " + srcTy + " to " + dstTy + "*/";
  }

  void handleCastExpr(const CastExpr* ce, ContextKind ctx) {
    switch (ce->getCastKind()) {
    case CK_NullToPointer:
      llvm::outs() << zeroValue(ce->getType().getTypePtr());
      break;
    case CK_ToVoid:
      if (isa<IntegerLiteral>(ce->getSubExpr()->IgnoreParens())) {
        llvm::outs() << "(tovoid = (); tovoid)";
      } else {
        visitStmt(ce->getSubExpr(), ctx);
      }
      break;
    case CK_FloatingCast:
      llvm::outs() << "(" << floatToFloat(ce->getSubExpr(), exprTy(ce)) << " ";
      visitStmt(ce->getSubExpr(), ctx);
      llvm::outs() << ")";
      break;
    case CK_FloatingToIntegral:
      llvm::outs() << "(" << floatToInt(ce->getSubExpr(), exprTy(ce)) << " ";
      visitStmt(ce->getSubExpr(), ctx);
      llvm::outs() << ")";
      break;
    case CK_IntegralToFloating: {
      const clang::Expr* mut_subExpr = ce->getSubExpr();
      llvm::outs() << "(" << intToFloat(mut_subExpr, exprTy(ce)) << " ";
      visitStmt(mut_subExpr);
      llvm::outs() << ")";
    }
      if (ctx != ExprContext) { llvm::outs() << "/*TODO(c2f) i2f cast in non-epxr ctx*/"; }
      break;
    case CK_PointerToBoolean:
      llvm::outs() << " /*pointer-to-bool cast*/ ";
      visitStmt(ce->getSubExpr(), ctx);
      break;
    case CK_IntegralToBoolean:
      llvm::outs() << " /*integral-to-bool cast*/ ";
      visitStmt(ce->getSubExpr(), ctx);
      break;
    case CK_IntegralCast: {
      std::string cast = "";
      std::string srcTy = tyName(exprTy(ce->getSubExpr()));
      std::string dstTy = tyName(exprTy(ce));

      if (srcTy == dstTy
       || isNestedCastThatCancelsOut(ce)
       || isa<CharacterLiteral>(ce->getSubExpr())
       || guaranteedNotToTruncate(ce->getSubExpr(), dstTy, exprTy(ce))) {
        // don't print anything, no cast needed
      } else {
        cast = intCastFromTo(srcTy, dstTy, exprTy(ce->getSubExpr())->isSignedIntegerType());
      }

      if (cast == "") {
        if (isNestedCastThatCancelsOut(ce)) {
          visitStmt(ce->getSubExpr()->IgnoreParenCasts(), ctx);
        } else {
          visitStmt(ce->getSubExpr(), ctx);
        }
      } else {
        if (ctx == BooleanContext) { llvm::outs() << "("; }
        llvm::outs() << "(" << cast << " ";
        visitStmt(ce->getSubExpr());
        llvm::outs() << ")";
        if (ctx == BooleanContext) { llvm::outs() << " " << emitBooleanCoercion(exprTy(ce)) << ")"; }
        if (ctx == AssignmentTarget) { llvm::outs() << "/*TODO(c2f) cast in assignment ctx!!!*/"; }
      }
      break;
    }
    default:
      visitStmt(ce->getSubExpr(), ctx);
    }
  }

  void visitCaseValue(const Expr* lhs) {
    bool handledSpecially = false;

    // Redundant with constant handling, but gives us something nicer to print.
    if (auto dre = dyn_cast<DeclRefExpr>(lhs->IgnoreImpCasts())) {
      // Special case handling of enum constants: as values they get codegenned to
      // function calls, but in pattern context they must become constant integers.
      if (auto ecd = dyn_cast<EnumConstantDecl>(dre->getDecl())) {
        handledSpecially = true;
        llvm::outs() << ecd->getInitVal().getSExtValue()
            << "/* " << ecd->getNameAsString() << " */";
      }
    }


    llvm::APSInt result;
    if (!handledSpecially && lhs->EvaluateAsInt(result, *Ctx)) {
      handledSpecially = true;
      llvm::outs() << result.getSExtValue();
    }


    if (!handledSpecially) {
      visitStmt(lhs);
    }
  }

  void visitCaseStmt(const CaseStmt* cs, bool isFirst) {
      const Stmt* ss = cs->getSubStmt();
      if (cs->getLHS()) {
        if (isFirst) {
          llvm::outs() << "  of ";
        } else {
          llvm::outs() << "  or ";
        }

        visitCaseValue(cs->getLHS());

        if (ss && !isa<CaseStmt>(ss)) { llvm::outs() << " ->"; }
        llvm::outs() << "\n";
      }
      if (cs->getRHS()) {
        llvm::outs() << "//case stmt rhs:\n";
        visitStmt(cs->getRHS());
      }
      if (ss) {
        if (const CaseStmt* css = dyn_cast<CaseStmt>(ss)) {
          visitCaseStmt(css, false);
        } else {
          visitStmt(ss, StmtContext);
        }
      }
  }

  void collapseNestedArrayInitList(const InitListExpr* ile, std::vector<const clang::Expr*> &inits) {
    for (unsigned i = 0; i < ile->getNumInits(); ++i) {
      const Expr* nie = ile->getInit(i);
      if (const InitListExpr* nested = dyn_cast<InitListExpr>(nie)) {
        if (isa<ConstantArrayType>(nested->getType())) {
          collapseNestedArrayInitList(nested, inits);
          continue;
        }
      }
      // otherwise, if we didn't hit the continue above:
      inits.push_back(nie);
    }
  }

  std::string emitVarName(const ValueDecl* vd) {
    if (auto ecd = dyn_cast<EnumConstantDecl>(vd)) {
      auto pfx = globals.enumPrefixForConstants[ecd->getNameAsString()];
      return "(" + enumConstantAccessor(pfx, ecd) + " !)"; // emitCall
    }

    auto it = duplicateVarDecls.find(vd);
    if (it == duplicateVarDecls.end()) {
      return fosterizedName(vd->getName());
    } else {
      std::string s;
      std::stringstream ss(s); ss << fosterizedName(vd->getName()) << "___" << it->second;
      return ss.str();
    }
  }

  void visitVarDecl(const VarDecl* vd) {
    currentVars.push_back(vd->getName());
    if (vd->hasInit()) {
      if (vmpt.isMutableVar(vd->getName()) && !vmpt.isMutableVar(vd->getInit())) {
        llvm::outs() << emitVarName(vd) << " = PtrRef (prim ref ";
        visitStmt(vd->getInit());
        llvm::outs() << ")"; // /*vd-mutlocal; a=" << isDeclRefOfMutableAlias(vd) << "*/";
      } else {
        llvm::outs() << emitVarName(vd) << " = ";
        visitStmt(vd->getInit());

//        if (optC2FVerbose) {
//          llvm::outs() << " /*mutLocal? " << mutableLocals[vd->getName()]
//                        << "; DRML? " << isDeclRefOfMutableLocal(vd->getInit()) << " */";
//        }

#if 0
        if (auto uno = dyn_cast<UnaryOperator>(vd->getInit())) {
          if (auto dre = dyn_cast<DeclRefExpr>(uno->getSubExpr())) {
            if (isPrimRef(dre->getDecl()) && uno->getOpcode() == UO_AddrOf) {
              //mutableLocalAliases[vd->getName()] = true;

              if (optC2FVerbose) {
                llvm::outs() << " /*mutLocalAlias!*/";
              }

            }
          }
        }
#endif
      }
    } else {
      const Type* ty = vd->getType().getTypePtr();
      uint64_t size = 0;
      const Type* eltTy = nullptr;
      if (tryBindConstantSizedArrayType(ty, eltTy, size)) {
        auto zeroval = zeroValue(eltTy);

        llvm::outs() << emitVarName(vd) << " = ";
        if (size > 0 && size <= 16) {
          llvm::outs() << "(ptrOfArr:[" << tyName(eltTy) << "] (prim mach-array-literal";
          for (uint64_t i = 0; i < size; ++i) {
            llvm::outs() << " " << zeroval;
          }
          llvm::outs() << "))";
        } else {
          llvm::outs() << "(ptrOfArr (newArrayReplicate " << size << " " << zeroval << "))";
        }
      } else if (ty->isScalarType()) {
        llvm::outs() << emitVarName(vd) << " = PtrRef (prim ref " << zeroValue(exprTy(vd)) << ")";
      } else {
        llvm::outs() << emitVarName(vd) << " = (" << zeroValue(exprTy(vd)) << ")";
      }
    }
    currentVars.pop_back();
  }

  void visitStmt(const Stmt* stmt, ContextKind ctx = ExprContext) {
    emitCommentsFromBefore(stmt->getLocStart());

    // for array subscript expression handling
    Indices indices;

    // When visiting a bound substatement, emit its variable binding.
    auto it = StmtMap.find(stmt);
    if (it != StmtMap.end()) {
      auto pair = it->second;
      if (stmt != currStmt) {
        llvm::outs() << "b_" << pair.first << "_" << pair.second;
        if (ctx == BooleanContext) {
          if (auto expr = dyn_cast<Expr>(stmt)) {
            llvm::outs() << " " << emitBooleanCoercion(exprTy(expr)); } }
        return;
      }

      if (stmt == currStmt && !isa<ReturnStmt>(stmt)) {
        llvm::outs() << "b_" << pair.first << "_" << pair.second << " = ";
        ctx = ExprContext;
      }
    } else {
      if (ctx == StmtContext) {
        if (auto e = dyn_cast<Expr>(stmt)) {
          if (!(e->getType().getTypePtr()->isIntegralOrEnumerationType()) ) {
            // Clang doesn't complain about pointer-valued expressions
            // (with side effects) used as statements, but Foster is
            // stricter about what type a statement is allowed to have.
            // To mediate the difference, we sometimes need to add
            // silent bindings.
            llvm::outs() << "_ignored = ";
          }
        }
      }
    }

    if (const ImplicitCastExpr* ice = dyn_cast<ImplicitCastExpr>(stmt)) {
      if (ice->getCastKind() == CK_LValueToRValue
       || ice->getCastKind() == CK_FunctionToPointerDecay
       || ice->getCastKind() == CK_NoOp)
          return visitStmt(ice->getSubExpr(), ctx);
      return handleCastExpr(ice, ctx);
    }

    if (const IfStmt* ifs = dyn_cast<IfStmt>(stmt)) {
      handleIfThenElse(ctx, AnIfStmt, ifs->getCond(), ifs->getThen(), ifs->getElse());
    } else if (const ForStmt* fs = dyn_cast<ForStmt>(stmt)) {
      if (tryHandleEnumRange(fs)) {
        // done
      } else {
        translateGeneralForLoop(fs);
      }
    } else if (const WhileStmt* ws = dyn_cast<WhileStmt>(stmt)) {
      translateWhileLoop(ws, "while", nullptr);
    } else if (const DoStmt* ws = dyn_cast<DoStmt>(stmt)) {
      translateWhileLoop(ws, "do-while", nullptr);
    } else if (const ConditionalOperator* co = dyn_cast<ConditionalOperator>(stmt)) {
      handleIfThenElse(ctx, AnIfExpr, co->getCond(), co->getTrueExpr(), co->getFalseExpr());
    } else if (const BinaryConditionalOperator* bco = dyn_cast<BinaryConditionalOperator>(stmt)) {
      llvm::outs() << "(condV = ";
      visitStmt(bco->getCommon(), ExprContext);
      llvm::outs() << ";\n";
      llvm::outs() << "if condV !=Int32 0 then condV else ";
      visitStmt(bco->getFalseExpr(), ExprContext);
      llvm::outs() << " end)\n";
    } else if (const ParenExpr* pe = dyn_cast<ParenExpr>(stmt)) {
      if (tryHandleAtomicExpr(pe->getSubExpr(), ctx)) {
        // done
      } else {
        llvm::outs() << "(";
        visitStmt(pe->getSubExpr(), ctx);
        llvm::outs() << ")";
      }
    } else if (const NullStmt* dr = dyn_cast<NullStmt>(stmt)) {
      llvm::outs() << "(nullstmt = (); nullstmt)";
    } else if (const CaseStmt* cs = dyn_cast<CaseStmt>(stmt)) {
      visitCaseStmt(cs, true);
    } else if (const DefaultStmt* ds = dyn_cast<DefaultStmt>(stmt)) {
      llvm::outs() << "  of _ ->\n";
      visitStmt(ds->getSubStmt(), StmtContext);
      /*
      if (isa<BreakStmt>(ds->getSubStmt())) {
        llvm::outs() << "; (breakstmt = (); breakstmt)\n";
      }
      */
    } else if (const SwitchStmt* ss = dyn_cast<SwitchStmt>(stmt)) {
      handleSwitch(ss);
    } else if (const GotoStmt* gs = dyn_cast<GotoStmt>(stmt)) {
      llvm::outs() << "mustbecont_" << gs->getLabel()->getNameAsString() << " !\n";
    } else if (isa<BreakStmt>(stmt)) {
      // Outside of switches, breaks will be handled by CFG building.
      // Within switch statements, breaks should correspond to unit values.
      llvm::outs () << " () ";
    } else if (isa<ContinueStmt>(stmt)) {
      // Do nothing; should be implicitly handled by CFG building.
    } else if (const LabelStmt* ls = dyn_cast<LabelStmt>(stmt)) {
      llvm::outs() << "// TODO(c2f): label " << ls->getName() << ";\n";
      llvm::outs() << "(labelstmt = (); retstmt)";
      visitStmt(ls->getSubStmt(), ctx);
    } else if (const ReturnStmt* rs = dyn_cast<ReturnStmt>(stmt)) {
      if (rs->getRetValue()) {
        visitStmt(rs->getRetValue(), ctx);
      } else {
        llvm::outs() << "(retstmt = (); retstmt)";
      }
    } else if (const MemberExpr* me = dyn_cast<MemberExpr>(stmt)) {
      const Expr* base = nullptr;
      if (ctx == BooleanContext) { llvm::outs() << "("; }
      llvm::outs() << "(" + fieldAccessorName(me, base, ctx == AssignmentTarget) + " ";
      // If we have a chained member expr    p->f1->f2    (and we're accessing field f2)
      // and the field f1 is represented with a pointer, we must dereference the
      // pointer to get an object that f2's accessor can accept.
      visitWithDerefIf(base, me->isArrow() &&
        (vmpt.isPointeryVar(base) || 
         globals.fpt.isPointeryField(base->IgnoreParenImpCasts())));
      llvm::outs() << ")";
      if (ctx == BooleanContext) { llvm::outs() << " " << emitBooleanCoercion(exprTy(me)) << ")"; }
    } else if (auto base = extractBaseAndArraySubscripts(stmt, indices)) {
      emitPeek(base, indices);
    } else if (const CompoundAssignOperator* cao = dyn_cast<CompoundAssignOperator>(stmt)) {
      handleCompoundAssignment(cao, ctx);
    } else if (const BinaryOperator* binop = dyn_cast<BinaryOperator>(stmt)) {
      handleBinaryOperator(binop, ctx);
    } else if (const UnaryOperator* unop = dyn_cast<UnaryOperator>(stmt)) {
      if (ctx == BooleanContext) { llvm::outs() << "("; }
      handleUnaryOperator(unop, ctx == BooleanContext ? ExprContext : ctx);
      if (ctx == BooleanContext) { llvm::outs() << " " << emitBooleanCoercion(exprTy(unop)) << " /*L1932*/)"; }
    } else if (const StmtExpr* se = dyn_cast<StmtExpr>(stmt)) {
      visitStmt(se->getSubStmt());
    } else if (const IntegerLiteral* lit = dyn_cast<IntegerLiteral>(stmt)) {
      if (ctx == BooleanContext) {
        llvm::outs() << (lit->getValue().getBoolValue() ? "True" : "False");
      } else {
        bool isSigned = true;
        lit->getValue().print(llvm::outs(), isSigned);
      }
    } else if (const StringLiteral* lit = dyn_cast<StringLiteral>(stmt)) {
      if (ctx == BooleanContext) {
        llvm::outs() << "True";
      } else {
        if (lit->isUTF8() || lit->isAscii()) {
          emitUTF8orAsciiStringLiteral(lit->getString());
        } else {
          llvm::outs() << "// non UTF8 string\n";
          llvm::outs() << "(strLit ";
          lit->outputString(llvm::outs());
          llvm::outs() << ")";
        }
      }
    } else if (const FloatingLiteral* lit = dyn_cast<FloatingLiteral>(stmt)) {
      if (ctx == BooleanContext) {
        llvm::outs() << (lit->getValueAsApproximateDouble() != 0.0 ? "True" : "False");
      } else {
        std::string litstr = FC.getText(*lit);
        //llvm::errs() << "// float lit str: " << litstr << "\n";
        if (!litstr.empty()) {
          char last = litstr[litstr.size() - 1];
          if (last == 'f' || last == 'F') {
            litstr[litstr.size() - 1] = ' ';
          }
        }
        if (!litstr.empty()) llvm::outs() << litstr;
        else {
          llvm::SmallString<128> buf;
          lit->getValue().toString(buf);
          llvm::outs() << buf;
          if (buf.count('.') == 0) {
            llvm::outs() << ".0";
          }
        }
      }

    } else if (const CharacterLiteral* clit = dyn_cast<CharacterLiteral>(stmt)) {
      if (ctx == BooleanContext) {
        llvm::outs() << (clit->getValue() ? "True" : "False");
      } else {
        if (isprint(clit->getValue())) {
          llvm::outs() << "('" << llvm::format("%c", clit->getValue()) << "' as " 
                       << tyName(clit->getType().getTypePtr()) << ")";
        } else {
          llvm::outs() << clit->getValue();
          llvm::outs() << " /*'\\x" << llvm::format("%02x", clit->getValue()) << "'*/ ";
        }
      }
    } else if (const PredefinedExpr* lit = dyn_cast<PredefinedExpr>(stmt)) {
      lit->getFunctionName()->outputString(llvm::outs());
    } else if (const CastExpr* ce = dyn_cast<CastExpr>(stmt)) {
      handleCastExpr(ce, ctx);
    } else if (const DeclRefExpr* dr = dyn_cast<DeclRefExpr>(stmt)) {

      if (ctx == BooleanContext) { llvm::outs() << "("; }

      auto vd = dr->getDecl();

      //if (ctx != AssignmentTarget && isPrimRef(vd) && !isDeclRefOfMutableAlias(vd)) {
      if (ctx != AssignmentTarget && vmpt.isMutableVar(vd->getName())) {
        llvm::outs() << "(ptrGet " << emitVarName(vd) << ")";
        if (optC2FVerbose) { llvm::outs() << "/*3067*/"; }
      } else {
        llvm::outs() << emitVarName(vd);
      }

      if (ctx == BooleanContext) { llvm::outs() << " " << emitBooleanCoercion(exprTy(dr)) << ")"; }

    } else if (const CStyleCastExpr* ce = dyn_cast<CStyleCastExpr>(stmt)) {
      if (tryHandleCallMallocCasted(ce)) {
        // done
      } else {
        llvm::outs() << "/* line 610\n";
        stmt->dump();
        llvm::outs() << "\n*/\n";
        llvm::outs() << FC.getText(*stmt) << "\n";
      }
    } else if (const CallExpr* ce = dyn_cast<CallExpr>(stmt)) {
      if (ctx == BooleanContext) { llvm::outs() << "("; }

      if (tryHandleCallMalloc(ce, nullptr) || tryHandleCallFree(ce)) {
        // done
      } else if (tryHandleCallPrintf(ce) || tryHandleCallMemop(ce)) {
        // done
      } else {
        handleCall(ce);
      }

      if (ctx == BooleanContext) { llvm::outs() << " " << emitBooleanCoercion(exprTy(ce)) << ")"; }
    } else if (const ImplicitValueInitExpr* ivie = dyn_cast<ImplicitValueInitExpr>(stmt)) {
      llvm::outs() << zeroValue(ivie->getType().getTypePtr());
    } else if (const InitListExpr* ile = dyn_cast<InitListExpr>(stmt)) {
      // TOOD CompoundLiteralExpr containing an InitListExpr
      if (ile->hasArrayFiller()) {
        llvm::outs() << "// WARNING: ignoring array filler\n";
      }
      if (ile->isStringLiteralInit()) {
        llvm::outs() << "// WARNING: string literal init...?\n";
      }

      if (auto rt = bindRecordType(ile->getType().getTypePtr())) {
        // We use the name of the expr type rather than the record type
        // because the former works correctly for anonymous typedef'd records.
        llvm::outs() << "(" << tyName(ile->getType().getTypePtr());
        for (unsigned i = 0; i < ile->getNumInits(); ++i) {
          llvm::outs() << " ";
          llvm::outs() << "(mkField ";
          visitStmt(ile->getInit(i));
          llvm::outs() << ")";
        }
        llvm::outs() << ")";
      } else {
        const Type* ty = ile->getType().getTypePtr();

        std::string eltTyName = "";
        {
          uint64_t size = 0; const Type* eltTy = nullptr;
          if (tryBindConstantSizedArrayType(ty, eltTy, size)) {
            eltTyName = tyName(eltTy);
          } else {
            if (ile->getNumInits() > 0) { eltTyName = tyName(exprTy(ile->getInit(0))); }
            else if (ile->hasArrayFiller()) { eltTyName = tyName(exprTy(ile->getArrayFiller())); }
            else { // TODO constant array element type?
            }
          } 
        }
        

        llvm::outs() << "(ptrOfArr:[" << eltTyName << "] (prim mach-array-literal";
        std::vector<const clang::Expr*> inits;
        collapseNestedArrayInitList(ile, inits);
        for (auto e : inits) {
          llvm::outs() << " ";
          visitStmt(e);
        }

        // Explicitly add any array values that Clang left implicit/uninitialized.
        // TODO for large arrays that are incompletely initialized, we should
        // emit code to set individual slots and rely on the runtime's
        // zero-initialization for the rest.
        uint64_t size = 0; const Type* eltTy = nullptr;
        if (tryBindConstantSizedArrayType(ty, eltTy, size)) {
          auto zeroval = zeroValue(eltTy);
          for (unsigned i = inits.size(); i < size; ++i) {
            llvm::outs() << " " << zeroval;
          }
        }

        llvm::outs() << "))";
      }
    } else if (auto cs = dyn_cast<CompoundStmt>(stmt)) {

      size_t numPrintingChildren = cs->size();
      for (const Stmt* c : cs->children()) {
        if (isa<CompoundStmt>(c) || isa<BreakStmt>(c)) {
          // non-printing
          --numPrintingChildren;
        }
      }

      if (numPrintingChildren == 0) {
        llvm::outs() << "(empty = (); empty)\n";
      } else {
        size_t childno = 0;
        for (const Stmt* c : cs->children()) {
          visitStmt(c, StmtContext);

          if (isa<CompoundStmt>(c) || isa<BreakStmt>(c)) {
            // don't print another semicolon
          } else if (childno == numPrintingChildren - 1) {
            // We need to print a semicolon when compound statments
            // are embedded within other compound statments,
            // but not when they appear within switch cases...
            llvm::outs() << ";\n";
          } else {
            llvm::outs() << ";\n";
          }
          ++childno;
        }
      }
    } else if (const DeclStmt* ds = dyn_cast<DeclStmt>(stmt)) {
      const Decl* last = *(ds->decls().end() - 1);
      for (const Decl* d : ds->decls()) {
        if (const VarDecl* vd = dyn_cast<VarDecl>(d)) {
          visitVarDecl(vd);
        } else {
          visitStmt(d->getBody(), StmtContext);
        }
        if (d != last) llvm::outs() << ";\n";
      }
    } else if (const UnaryExprOrTypeTraitExpr* ue = dyn_cast<UnaryExprOrTypeTraitExpr>(stmt)) {
      if (ue->getKind() == UETT_SizeOf) {
        const Type* ty = bindSizeofType(ue);
        llvm::outs() << (Ctx->getTypeSize(ty) / 8) << " /* sizeof " << tyName(ty) << "*/\n";
      } else {
        llvm::outs().flush();
        llvm::errs() << "/* line 716\n";
        stmt->dump();
        llvm::errs() << "\n*/\n";
        llvm::errs().flush();
        llvm::outs() << FC.getText(*stmt) << "\n";
      }
    } else if (!stmt) {
      llvm::outs() << "/*null stmt??*/";
    } else {
      llvm::outs().flush();
      llvm::errs() << "/* line 655\n";
      stmt->dump();
      llvm::errs() << "\n*/\n";
      llvm::errs().flush();
      llvm::outs() << FC.getText(*stmt) << "\n";
    }
  }


  const ReturnStmt* getTailReturnOrNull(const Stmt* s) {
    const Stmt* rv = lastStmtWithin(s);
    return rv ? dyn_cast<ReturnStmt>(rv) : NULL;
  }

  void performFunctionLocalAnalysis(FunctionDecl* d, bool& needsCFG) {
    std::map<const Stmt*, bool> innocuousReturns;
    innocuousReturns[getTailReturnOrNull(d->getBody())] = true;

    if (const IfStmt* ifs = dyn_cast<IfStmt>(lastStmtWithin(d->getBody()))) {
      // It's only innocuous if both branches have a tail return!
      const ReturnStmt* mbThenRet = getTailReturnOrNull(ifs->getThen());
      const ReturnStmt* mbElseRet = getTailReturnOrNull(ifs->getElse());
      if (mbThenRet && mbElseRet) {
        innocuousReturns[mbThenRet] = true;
        innocuousReturns[mbElseRet] = true;
      }
    }

    // TODO tail returns within a last-stmt do-while(0) block are innocuous.

    FnBodyVisitor v(vmpt, innocuousReturns,
                    voidPtrCasts, needsCFG, d->getASTContext());
    v.TraverseDecl(d);
    if (optC2FVerbose) { vmpt.summarize(d->getNameAsString()); }
  }

  void handleFunctionDecl(FunctionDecl* fd) {
    if (Stmt* body = fd->getBody()) {
      bool needsCFG = false;
      bool mainWithArgs = false;
      performFunctionLocalAnalysis(fd, needsCFG);
      std::string name = fosterizedName(fd->getName());

      if (globals.uglyhack.SawGlobalVariables && name == "main") {
        name = "c2f_main";
      }

      // Functions at toplevel can be mutually recursive (with appropriate
      // forward declarations) so we conservatively mark them as such if
      // we're wrapping "toplevel" functions.
      if (globals.uglyhack.SawGlobalVariables) {
        llvm::outs() << "REC ";
      }

      llvm::outs() << name << " = {\n";

      if (fd->getName() == "main") {
        mainWithArgs = fd->getNumParams() > 0;
      } else {
        // Emit function arguments.
        for (unsigned i = 0; i < fd->getNumParams(); ++i) {
          ParmVarDecl* d = fd->getParamDecl(i);
          auto vpcset = voidPtrCasts[d];
          const Type* ty = vpcset.unique() ? vpcset.front() : exprTy(d);
          if (!isVoidPtr(ty)) {
            llvm::outs() << "    " << fosterizedName(d->getDeclName().getAsString())
                          << " : " << tyName(ty) << " =>\n";
          }
        }
      }

      // Assume main's params are named argc and argv, for now.
      if (mainWithArgs) {
        llvm::outs() << "argv = c2f_argv !; argc = ptrSize argv;\n";
      }

      // Rebind parameters if they are observed to be mutable locals.
      for (unsigned i = 0; i < fd->getNumParams(); ++i) {
        ParmVarDecl* d = fd->getParamDecl(i);
        if (vmpt.isMutableVar(d->getName())) {
          currentVars.push_back(d->getName());
          assert(d->getName() == d->getDeclName().getAsString());
          llvm::outs() << fosterizedName(d->getName())
                        << " = PtrRef (prim ref "
                        << fosterizedName(d->getName())
                        << ");\n";
          currentVars.pop_back();  
        }
      }

      if (needsCFG) {
        visitStmtCFG(body);
      } else {
        visitStmt(body);
      }
      llvm::outs() << "};\n";
    }
  }

/*
  bool isPrimRefDecl(const Expr* e) {
    if (auto dre = dyn_cast<DeclRefExpr>(e->IgnoreParenImpCasts())) {
      return isPrimRef(dre->getDecl());
    }
    return false;
  }

  bool isPrimRef(const ValueDecl* d) {
    return mutableLocals[d->getName()] || mutableLocalAliases[d->getName()];
  }
*/

  void handleSingleTopLevelDecl(Decl* decl) {

    if (FunctionDecl* fd = dyn_cast<FunctionDecl>(decl)) {
      handleFunctionDecl(fd);
    } else if (VarDecl* vd = dyn_cast<VarDecl>(decl)) {
      // TODO globals with initializers may still be mutable,
      // but I don't think we detect mutable usage properly yet.
      visitVarDecl(vd);
      llvm::outs() << ";\n";
#if 0
      llvm::outs() << "/* Unhandled global variable declaration:\n"
        << "     	hasDefinition(): " << vd->hasDefinition() << "\n"
        << "     	hasGlobalStorage(): " << vd->hasGlobalStorage() << "\n"
        << "     	hasInit(): " << vd->hasInit() << "\n"
        << "     	isDirectInit(): " << vd->isDirectInit() << "\n"
        << "     	tyName(getType()): " << tyName(vd->getType().getTypePtr()) << "\n"
        << getText(R, *vd) << ";*/\n";
#endif
    } else {

      bool handled = isa<RecordDecl>(decl)
                  || isa<TypedefDecl>(decl)
                  || isa<EnumDecl>(decl);
      if (!handled) {
        llvm::errs() << "unhandled top-level decl\n";
        decl->dump();
      }
    }
  }

  bool HandleTopLevelDecl(DeclGroupRef DR) override {
    for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b) {
      vmpt.clear();
      voidPtrCasts.clear();

      emitCommentsFromBefore((*b)->getLocStart());
      if (shouldProcessTopLevelDecl(*b, FC)) {
        handleSingleTopLevelDecl(*b);
      }
    }
    return true;
  }

  std::string floatToInt(const Expr* srcexpr, const Type* tgt) {
    const Type* src = exprTy(srcexpr);
    const std::string srcTy = tyName(src);
    const std::string tgtTy = tyName(tgt);
    if (srcTy == "Float32" && tgtTy == "Int32") return (tgt->isSignedIntegerType() ? "f32-to-s32-unsafe" : "f32-to-u32-unsafe");
    if (srcTy == "Float64" && tgtTy == "Int64") return (tgt->isSignedIntegerType() ? "f64-to-s64-unsafe" : "f64-to-u64-unsafe");
    return "/* " + srcTy + "-to-" + tgtTy + "*/";
  }

  std::string floatToFloat(const Expr* srcexpr, const Type* tgt) {
    const Type* src = exprTy(srcexpr);
    const std::string srcTy = tyName(src);
    const std::string tgtTy = tyName(tgt);
    if (srcTy == "Float32" && tgtTy == "Float64") return "f32-to-f64";
    return "/* " + srcTy + "-to-" + tgtTy + "*/";
  }

  std::string intToFloat(const Expr* &srcexpr, const Type* tgt) {
    const Type* src = exprTy(srcexpr);
    const Type* und = exprTy(srcexpr->IgnoreCasts());
    std::string undTy = tyName(und);
    std::string srcTy = tyName(src);
    std::string tgtTy = tyName(tgt);
    // If we have nested casts, generating (s8 |> s8-to-s32 |> s32-to-f32-unsafe)
    // is correct but not ideal because it's guaranteed not to trigger ill defined cases
    // in s32-to-f32, so we special-case certain casts here.
    if (undTy == "Int8" && tgtTy == "Float32") {
      srcTy = undTy;
      srcexpr = srcexpr->IgnoreCasts();
    }
    if (srcTy == "Int32" && tgtTy == "Float64") return (src->isSignedIntegerType() ? "s32-to-f64" : "u32-to-f64");
    if (srcTy == "Int64" && tgtTy == "Float64") return (src->isSignedIntegerType() ? "s64-to-f64-unsafe" : "u64-to-f64-unsafe");
    if (srcTy == "Int8"  && tgtTy == "Float32") return (src->isSignedIntegerType() ? "s8-to-f32" : "u8-to-f32");
    if (srcTy == "Int32" && tgtTy == "Float32") return (src->isSignedIntegerType() ? "s32-to-f32-unsafe" : "u32-to-f32-unsafe");
    return "/* " + srcTy + "-to-" + tgtTy + "*/";
  }

  // As the translation unit is parsed, the comments list pointed to by rawcomments
  // will be updated incrementally. To remain agnostic about how & when it is updated,
  // we only assume that it will contain (at least) those comments appearing before ``loc``.
  // We track two hidden state variables, one indicating which was the last comment we printed,
  // and one for the last location we checked.
  // This method prints those comments which occur between lastloc and loc.
  // We could be more aggressive about updating lastsize to avoid repeated inspection of comments.
  void emitCommentsFromBefore(SourceLocation loc) {
    ArrayRef<RawComment*> comments = rawcomments->getComments();
    for (unsigned i = rawcomments_lastsize; i < comments.size(); ++i) {
      if (FC.isFromMainFile(comments[i]->getLocStart())) {
        if (FC.getSourceMgr().isBeforeInTranslationUnit(comments[i]->getLocStart(), loc)) {
          // If we don't have a last location, or if the comment comes
          // after the last location, emit it.
          if (!lastloc.isValid() || FC.getSourceMgr().isBeforeInTranslationUnit(lastloc, comments[i]->getLocStart())) {
            llvm::outs() << FC.getText(*comments[i]) << "\n";
            rawcomments_lastsize = i + 1;
          }
        }
      }
    }
    lastloc = loc;
  }

  void Initialize(ASTContext& ctx) override {
    rawcomments = &(ctx.getRawCommentList());
    rawcomments_lastsize = 0;
    Ctx = &ctx;
    currStmt = nullptr;
  }
/*
  void HandleTranslationUnit(ASTContext& ctx) override {
    ArrayRef<RawComment*> comments = ctx.getRawCommentList().getComments();
    llvm::outs() << "HandleTranslationUnit: # comments = " << comments.size() << "\n";
    for (unsigned i = 0; i < comments.size(); ++i) {
      if (isFromMainFile(comments[i]->getLocStart())) {
        llvm::outs() << getText(R, *comments[i]) << "\n";
      }
    }
  }
  */

private:
  RawCommentList* rawcomments;
  int             rawcomments_lastsize;
  SourceLocation  lastloc;
  VarMutabilityAndPointernessTracker vmpt;
  VoidPtrCasts voidPtrCasts;
  const CompilerInstance& CI;
  const FileClassifier FC;
  ASTContext* Ctx;

  std::vector<std::string> currentVars;

  llvm::DenseMap<const ValueDecl*, int> duplicateVarDecls;

  const Stmt* currStmt; // print this one, even if it's in the map.
  typedef llvm::DenseMap<const Stmt*,std::pair<unsigned,unsigned> > StmtMapTy;
  StmtMapTy StmtMap;

  llvm::DenseMap<const Stmt*, BinaryOperatorKind> tweakedStmts;
};


bool C2F_FormatStringHandler::HandlePrintfSpecifier(const analyze_printf::PrintfSpecifier& fs, const char* startSpecifier, unsigned specifierLen) {
  bool followedByNewline = startSpecifier[specifierLen] == '\n';
  emitStringContentsUpTo(startSpecifier, specifierLen + (followedByNewline ? 1 : 0));

  StringRef text(startSpecifier, specifierLen);
  const Expr* e = ce->getArg(fs.getArgIndex() + 1);

  if (text == "%d") {
    std::string tynm = tyName(e->getType().getTypePtr());
    // TODO use fs.getArgType() to determine non-i32 and ext/trunc usage?
    if (followedByNewline) {
      if (tynm == "Int64") {
        llvm::outs() << "(print_i64 ";
      } else {
        llvm::outs() << "(print_i32 ";
      }
    } else {
      if (tynm == "Int64") {
        llvm::outs() << "(print_i64_bare ";
      } else {
        llvm::outs() << "(print_i32_bare ";
      }
    }    
    cons.visitStmt(e);
    llvm::outs() << ");\n";
  } else if (text == "%s") {
    if (followedByNewline) {
      llvm::outs() << "(printStr ";
    } else {
      llvm::outs() << "(printStrBare ";
    }
    cons.visitStmt(ce->getArg(fs.getArgIndex() + 1));
    llvm::outs() << ")";
  } else {
    std::string spec = fs.getConversionSpecifier().getCharacters();
    if (spec == "d" || spec == "u" || spec == "c" || spec == "x") {
      int8_t flag = 0;
      int32_t width = 0;
      int32_t precision = -1;

      if (fs.hasValidSpacePrefix() && fs.hasSpacePrefix().isSet()) flag = 2;
      else if (fs.hasValidPlusPrefix() && fs.hasPlusPrefix().isSet()) flag = 1;
      else if (fs.hasValidLeadingZeros() && fs.hasLeadingZeros().isSet()) flag = 4;

      if (fs.hasValidLeftJustified() && fs.isLeftJustified().isSet()) flag += 10;

      if (fs.hasValidFieldWidth() &&
          fs.getFieldWidth().getHowSpecified() == clang::analyze_format_string::OptionalAmount::Constant) {
        width = fs.getFieldWidth().getConstantAmount();
      }

      if (fs.hasValidPrecision() &&
          fs.getPrecision().getHowSpecified() == clang::analyze_format_string::OptionalAmount::Constant) {
        precision = fs.getPrecision().getConstantAmount();
      }

      // TODO handle i64 as well.
      std::string tynm = tyName(e->getType().getTypePtr());
      if (tynm == "Int64") {
        llvm::outs() << "(foster_sprintf_i64 ";
      } else {
        llvm::outs() << "(foster_sprintf_i32 ";
      }
      
      cons.visitStmt(ce->getArg(fs.getArgIndex() + 1));
      llvm::outs() << " ('" << spec << "' as Int8) " << int(flag) << " " << width << " " << precision;

      if (followedByNewline) {
        llvm::outs() << " |> print_text);\n";
      } else {
        llvm::outs() << " |> print_text_bare);\n";
      }
    } else if (text == "%f" || text == "%g") {
      std::string tynm = tyName(ce->getArg(1)->getType().getTypePtr());
      std::string printfn;
      if (tynm == "Float32" && followedByNewline) printfn = "print_float_f32";
      if (tynm == "Float64" && followedByNewline) printfn = "print_float_f64";
      if (tynm == "Float32" && !followedByNewline) printfn = "print_f32_bare";
      if (tynm == "Float64" && !followedByNewline) printfn = "print_f64_bare";
      if (printfn.empty()) return false;

      llvm::outs() << "(" << printfn << " ";
      cons.visitStmt(e);
      llvm::outs() << ")";
      return true;

    } else {
      fprintf(stderr, "/* handle printf specifier: %.*s */\n", specifierLen, startSpecifier);
      fprintf(stderr, "/* format specifier: getArgIndex: %d */\n", fs.getArgIndex());
      fprintf(stderr, "/* format specifier: usesPositionalArg: %d */\n", fs.usesPositionalArg());
      fprintf(stderr, "/* format specifier: getPositionalArgIndex: %d */\n", fs.getPositionalArgIndex());
      fprintf(stderr, "/* format specifier: hasStandardLengthModifier: %d */\n", fs.hasStandardLengthModifier());
      //fprintf(stderr, "/* format specifier: hasStandardConversionSpecifier: %d */\n", fs.hasStandardConversionSpecifier());
      fprintf(stderr, "/* format specifier: hasStandardLengthConversionCombination: %d */\n", fs.hasStandardLengthConversionCombination());
      fprintf(stderr, "/* printf specifier: consumesDataArgument: %d */\n", fs.consumesDataArgument());
      fprintf(stderr, "/* printf specifier: hasValidPlusPrefix: %d */\n", fs.hasValidPlusPrefix());
      fprintf(stderr, "/* printf specifier: hasValidSpacePrefix: %d */\n", fs.hasValidSpacePrefix());
      fprintf(stderr, "/* printf specifier: hasValidLeadingZeros: %d */\n", fs.hasValidLeadingZeros());
      fprintf(stderr, "/* printf specifier: hasValidPrecision: %d */\n", fs.hasValidPrecision());
      fprintf(stderr, "/* printf specifier: hasValidFieldWidth: %d */\n", fs.hasValidFieldWidth());
      fprintf(stderr, "/* printf specifier: argType: isValid: %d */\n", fs.getArgType(ctx, false).isValid());
      std::string tyname = fs.getArgType(ctx, false).getRepresentativeTypeName(ctx);
      fprintf(stderr, "/* printf specifier: argType: %s */\n", tyname.c_str());
      fflush(stderr);
      llvm::errs() << "/* printf conversion: " << fs.getConversionSpecifier().getCharacters() << " */\n";
      llvm::errs() << "/* printf precision: "; fs.getPrecision().toString(llvm::errs()); llvm::errs() << " */\n";
      llvm::errs() << "/* printf precision invalid: "; fs.getPrecision().isInvalid(); llvm::errs() << " */\n";
      llvm::errs() << "/* printf field width: "; fs.getFieldWidth().toString(llvm::errs()); llvm::errs() << " */\n";
      llvm::errs() << "/* printf field width not spec: "
        << (fs.getFieldWidth().getHowSpecified() == clang::analyze_format_string::OptionalAmount::NotSpecified) << " */\n";
      llvm::errs() << "/* printf field width valid : " << !fs.getFieldWidth().isInvalid(); llvm::errs() << " */\n";
      llvm::errs() << "/* printf length modifier: " << fs.getLengthModifier().toString() << " */\n";

      if (followedByNewline) {
        llvm::outs() << "print_newline !;\n";
      }
    }
  }
  return true;
}


class C2F_TypeDeclHandler_FA : public ASTFrontendAction {
public:
  C2F_TypeDeclHandler_FA() {}

  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    return llvm::make_unique<C2F_TypeDeclHandler>(CI.getSourceManager());
  }
};

class C2F_GlobalVariableDetector_FA : public ASTFrontendAction {
public:
  C2F_GlobalVariableDetector_FA() {}

  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    return llvm::make_unique<C2F_GlobalVariableDetector>(CI.getSourceManager());
  }
};


// For each source file provided to the tool, a new FrontendAction is created.
class C2F_FrontendAction : public ASTFrontendAction {
public:
  C2F_FrontendAction() {}

  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    return llvm::make_unique<MyASTConsumer>(CI);
  }
};

void initializeIgnoredSymbolNames() {
  globals.ignoredSymbolNames.insert("csmith_sink_");
  globals.ignoredSymbolNames.insert("__undefined");
  globals.ignoredSymbolNames.insert("platform_main_begin");
  globals.ignoredSymbolNames.insert("platform_main_end");
  globals.ignoredSymbolNames.insert("transparent_crc");
  globals.ignoredSymbolNames.insert("transparent_crc_bytes");
  globals.ignoredSymbolNames.insert("crc32_byte");
  globals.ignoredSymbolNames.insert("crc32_8bytes");
  globals.ignoredSymbolNames.insert("crc32_gentab");
  globals.ignoredSymbolNames.insert("safe_rshift_func_int64_t_s_u");
  globals.ignoredSymbolNames.insert("safe_rshift_func_int64_t_u_u");
  globals.ignoredSymbolNames.insert("safe_rshift_func_int64_t_u_s");
  globals.ignoredSymbolNames.insert("safe_rshift_func_int64_t_s_s");
  globals.ignoredSymbolNames.insert("safe_lshift_func_int64_t_s_u");
  globals.ignoredSymbolNames.insert("safe_lshift_func_int64_t_u_u");
  globals.ignoredSymbolNames.insert("safe_lshift_func_int64_t_u_s");
  globals.ignoredSymbolNames.insert("safe_lshift_func_int64_t_s_s");
  globals.ignoredSymbolNames.insert("safe_rshift_func_uint64_t_s_u");
  globals.ignoredSymbolNames.insert("safe_rshift_func_uint64_t_u_u");
  globals.ignoredSymbolNames.insert("safe_rshift_func_uint64_t_u_s");
  globals.ignoredSymbolNames.insert("safe_rshift_func_uint64_t_s_s");
  globals.ignoredSymbolNames.insert("safe_lshift_func_uint64_t_s_u");
  globals.ignoredSymbolNames.insert("safe_lshift_func_uint64_t_u_u");
  globals.ignoredSymbolNames.insert("safe_lshift_func_uint64_t_u_s");
  globals.ignoredSymbolNames.insert("safe_lshift_func_uint64_t_s_s");
  globals.ignoredSymbolNames.insert("safe_div_func_int8_t_s_s");
  globals.ignoredSymbolNames.insert("safe_div_func_int16_t_s_s");
  globals.ignoredSymbolNames.insert("safe_div_func_int32_t_s_s");
  globals.ignoredSymbolNames.insert("safe_div_func_int64_t_s_s");
  globals.ignoredSymbolNames.insert("safe_mod_func_int8_t_s_s");
  globals.ignoredSymbolNames.insert("safe_mod_func_int16_t_s_s");
  globals.ignoredSymbolNames.insert("safe_mod_func_int32_t_s_s");
  globals.ignoredSymbolNames.insert("safe_mod_func_int64_t_s_s");
  globals.ignoredSymbolNames.insert("safe_mul_func_int8_t_s_s");
  globals.ignoredSymbolNames.insert("safe_mul_func_int16_t_s_s");
  globals.ignoredSymbolNames.insert("safe_mul_func_int32_t_s_s");
  globals.ignoredSymbolNames.insert("safe_mul_func_int64_t_s_s");
  globals.ignoredSymbolNames.insert("safe_unary_minus_func_int8_t_s");
  globals.ignoredSymbolNames.insert("safe_add_func_int8_t_s_s");
  globals.ignoredSymbolNames.insert("safe_sub_func_int8_t_s_s");
  globals.ignoredSymbolNames.insert("safe_lshift_func_int8_t_s_s");
  globals.ignoredSymbolNames.insert("safe_lshift_func_int8_t_s_u");
  globals.ignoredSymbolNames.insert("safe_rshift_func_int8_t_s_s");
  globals.ignoredSymbolNames.insert("safe_rshift_func_int8_t_s_u");
  globals.ignoredSymbolNames.insert("safe_unary_minus_func_int16_t_s");
  globals.ignoredSymbolNames.insert("safe_add_func_int16_t_s_s");
  globals.ignoredSymbolNames.insert("safe_sub_func_int16_t_s_s");
  globals.ignoredSymbolNames.insert("safe_lshift_func_int16_t_s_s");
  globals.ignoredSymbolNames.insert("safe_lshift_func_int16_t_s_u");
  globals.ignoredSymbolNames.insert("safe_rshift_func_int16_t_s_s");
  globals.ignoredSymbolNames.insert("safe_rshift_func_int16_t_s_u");
  globals.ignoredSymbolNames.insert("safe_unary_minus_func_int32_t_s");
  globals.ignoredSymbolNames.insert("safe_add_func_int32_t_s_s");
  globals.ignoredSymbolNames.insert("safe_sub_func_int32_t_s_s");
  globals.ignoredSymbolNames.insert("safe_lshift_func_int32_t_s_s");
  globals.ignoredSymbolNames.insert("safe_lshift_func_int32_t_s_u");
  globals.ignoredSymbolNames.insert("safe_rshift_func_int32_t_s_s");
  globals.ignoredSymbolNames.insert("safe_rshift_func_int32_t_s_u");
  globals.ignoredSymbolNames.insert("safe_unary_minus_func_int64_t_s");
  globals.ignoredSymbolNames.insert("safe_add_func_int64_t_s_s");
  globals.ignoredSymbolNames.insert("safe_sub_func_int64_t_s_s");
  globals.ignoredSymbolNames.insert("safe_unary_minus_func_uint8_t_u");
  globals.ignoredSymbolNames.insert("safe_add_func_uint8_t_u_u");
  globals.ignoredSymbolNames.insert("safe_sub_func_uint8_t_u_u");
  globals.ignoredSymbolNames.insert("safe_mul_func_uint8_t_u_u");
  globals.ignoredSymbolNames.insert("safe_mod_func_uint8_t_u_u");
  globals.ignoredSymbolNames.insert("safe_div_func_uint8_t_u_u");
  globals.ignoredSymbolNames.insert("safe_lshift_func_uint8_t_u_s");
  globals.ignoredSymbolNames.insert("safe_lshift_func_uint8_t_u_u");
  globals.ignoredSymbolNames.insert("safe_rshift_func_uint8_t_u_s");
  globals.ignoredSymbolNames.insert("safe_rshift_func_uint8_t_u_u");
  globals.ignoredSymbolNames.insert("safe_unary_minus_func_uint16_t_u");
  globals.ignoredSymbolNames.insert("safe_add_func_uint16_t_u_u");
  globals.ignoredSymbolNames.insert("safe_sub_func_uint16_t_u_u");
  globals.ignoredSymbolNames.insert("safe_mul_func_uint16_t_u_u");
  globals.ignoredSymbolNames.insert("safe_mod_func_uint16_t_u_u");
  globals.ignoredSymbolNames.insert("safe_div_func_uint16_t_u_u");
  globals.ignoredSymbolNames.insert("safe_lshift_func_uint16_t_u_s");
  globals.ignoredSymbolNames.insert("safe_lshift_func_uint16_t_u_u");
  globals.ignoredSymbolNames.insert("safe_rshift_func_uint16_t_u_s");
  globals.ignoredSymbolNames.insert("safe_rshift_func_uint16_t_u_u");
  globals.ignoredSymbolNames.insert("safe_unary_minus_func_uint32_t_u");
  globals.ignoredSymbolNames.insert("safe_add_func_uint32_t_u_u");
  globals.ignoredSymbolNames.insert("safe_sub_func_uint33_t_u_u");
  globals.ignoredSymbolNames.insert("safe_mul_func_uint32_t_u_u");
  globals.ignoredSymbolNames.insert("safe_mod_func_uint32_t_u_u");
  globals.ignoredSymbolNames.insert("safe_div_func_uint32_t_u_u");
  globals.ignoredSymbolNames.insert("safe_lshift_func_uint32_t_u_s");
  globals.ignoredSymbolNames.insert("safe_lshift_func_uint32_t_u_u");
  globals.ignoredSymbolNames.insert("safe_rshift_func_uint32_t_u_s");
  globals.ignoredSymbolNames.insert("safe_rshift_func_uint32_t_u_u");
  globals.ignoredSymbolNames.insert("safe_unary_minus_func_uint64_t_u");
  globals.ignoredSymbolNames.insert("safe_add_func_uint64_t_u_u");
  globals.ignoredSymbolNames.insert("safe_sub_func_uint64_t_u_u");
  globals.ignoredSymbolNames.insert("safe_mul_func_uint64_t_u_u");
  globals.ignoredSymbolNames.insert("safe_mod_func_uint64_t_u_u");
  globals.ignoredSymbolNames.insert("safe_div_func_uint64_t_u_u");
  globals.ignoredSymbolNames.insert("safe_add_func_float_f_f");
  globals.ignoredSymbolNames.insert("safe_sub_func_float_f_f");
  globals.ignoredSymbolNames.insert("safe_mul_func_float_f_f");
  globals.ignoredSymbolNames.insert("safe_div_func_float_f_f");
  globals.ignoredSymbolNames.insert("safe_add_func_double_f_f");
  globals.ignoredSymbolNames.insert("safe_sub_func_double_f_f");
  globals.ignoredSymbolNames.insert("safe_mul_func_double_f_f");
  globals.ignoredSymbolNames.insert("safe_div_func_double_f_f");
  globals.ignoredSymbolNames.insert("safe_convert_func_float_to_int32_t");
}

// You'll probably want to invoke with -fparse-all-comments
int main(int argc, const char **argv) {
  CommonOptionsParser op(argc, argv, CtoFosterCategory);
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());

  initializeIgnoredSymbolNames();

  globals.uglyhack.SawGlobalVariables = false;

  Tool.run(newFrontendActionFactory<C2F_GlobalVariableDetector_FA>().get());

  // Note: to print type decls properly, we need to know what fields are
  // full pointers and which can be optimized to elide pointer overhead.
  // This information is currently produced by the global traversal.

  // Emit datatype definitions and field accessors for the program's data structures.
  // This also computes enum prefixes, which are needed when translating code.
  Tool.run(newFrontendActionFactory<C2F_TypeDeclHandler_FA>().get());

  if (globals.uglyhack.SawGlobalVariables) { llvm::outs() << "main = {\n"; }

  int rv = Tool.run(newFrontendActionFactory<C2F_FrontendAction>().get());

  if (globals.uglyhack.SawGlobalVariables) { llvm::outs() << "\nc2f_main !; };\n"; }

  return rv;
}

// Notes on un-handled C constructs:
//   * Need to think more about how to expose libm functions and macros.
//     Even a trivial-ish macro (HUGE_VAL) raises questions.
//   * Unions...
//   * Embedded anonymous structs are not well-handled yet,
//     on either the creation/representation or accessor sides.
//
//   * Struct fields not yet ideally translated.
//     A field of type T could be translated to any one of:
//       T                         when all structs are literals and the field is never mutated,
//                                 or if all mutations can be coalesced into struct allocation.
//       (Ref T)                   for mutable fields with known initializer expressions,
//                                 or non-pointer types (which can be zero-initialized).
//       (Ref (Maybe T))           for mutable pointer fields with uncertain initialization
//    For a pointer-to-struct S, we have additional choices in translating:
//      * Single-constructor datatype S, with implicit level of indirection, but no nullability
//      * Single-constructor datatype SU of kind Unboxed
//      * Single-plus-null datatype SN
//      * (Ptr S) capturing nullability (no extra level of indirection beyond S)
//      * (Array S/SN/SU/Ptr S)
//    Depending on how S* is translated, the translation of  (S*)malloc(...)
//    may produce one allocation = one level of indirection, or multiple allocations
//    = two levels of indirection.
//    For example, if X is a typedef for a 2-element array of Ts,
//    and we want to translate constant-sized arrays to dynamically allocated arrays,
//    then (T*)malloc(SZ) translates to allocDArray:[Array T] SZ
//    which is not correct (the outer array is 2x as big as it should be,
//    and there is no initialization of the interior elements).
//
//  * Local struct decls are stack-allocated in C, but we allocate (ref None) to be safe,
//    and it's not clear where/when/how to upgrade that allocation or update the ref contents.
//    E.g.::
//       struct S ss; struct S* ps = &ss; S_init(ps);
//    should have a better translation than
//       ss = (ref None); ps = ss; S_init ps;
//
//  * No support yet for Clang's OpaqueValueExpr or BinaryConditionalOperator.

// Other notes:
//   * If the input program defines two types differing only in the case
//     of the first letter (e.g. 'foo' and 'Foo'),
//     we won't properly distinguish the two (both become Foo).
//   * Missing returns from non-void-returning functions will (reasonably!)
//     lead to type errors in the generated Foster code.

