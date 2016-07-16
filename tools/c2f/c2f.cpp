//------------------------------------------------------------------------------
// C-to-Foster translator.
// Mainly focuses on translating syntax as a starting point for human cleanup,
// rather than being an Emscripten-style automated translator of semantics.
//
// Current status: hacky prototype.
//
// Doesn't do any special handling/recognition of function-like macros.
// Doesn't handle switch() yet.
// Doesn't handle early returns/break/continue/goto.
//   (best bet would be Clang CFG + Relooper)
// Doesn't handle pointers or structure allocations very well.
//   (needs to do analysis to differentiate arrays from singleton pointers).
// Could get better translations by doing more careful analysis of which
//   variables in the program are mutable and which aren't.
//
// Based on AST matching sample by Eli Bendersky (eliben@gmail.com).
//------------------------------------------------------------------------------
#include <string>

#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Lex/Lexer.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang;
using namespace clang::ast_matchers;
using namespace clang::driver;
using namespace clang::tooling;

static llvm::cl::OptionCategory CtoFosterCategory("C-to-Foster");

static std::string getRWText(const Rewriter &R, const SourceLocation& locstt, const SourceLocation& locend) {
  return R.getRewrittenText(SourceRange(locstt, locend));
}

static std::string getText(const Rewriter &R, const SourceLocation& locstt, const SourceLocation& locend) {
  const SourceManager &SourceManager = R.getSourceMgr();
  SourceLocation StartSpellingLocation = SourceManager.getSpellingLoc(locstt);
  SourceLocation EndSpellingLocation = SourceManager.getSpellingLoc(locend);
  if (!StartSpellingLocation.isValid() || !EndSpellingLocation.isValid()) {
    return std::string();
  }
  bool Invalid = true;
  const char *Text =
      SourceManager.getCharacterData(StartSpellingLocation, &Invalid);
  if (Invalid) {
    return std::string();
  }
  std::pair<FileID, unsigned> Start =
      SourceManager.getDecomposedLoc(StartSpellingLocation);
  std::pair<FileID, unsigned> End =
      SourceManager.getDecomposedLoc(Lexer::getLocForEndOfToken(
          EndSpellingLocation, 0, SourceManager, LangOptions()));
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
static std::string getText(const Rewriter &R, const T &Node) {
  return getRWText(R, Node.getLocStart(), Node.getLocEnd());
}

std::string s(const char* c) { return std::string(c); }

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

std::string getCompoundTextWithoutBraces(const Rewriter &R, const Stmt* mb_comp) {
  if (llvm::isa<CompoundStmt>(mb_comp)) {
   return getRWText(R, mb_comp->getLocStart().getLocWithOffset(1), mb_comp->getLocEnd().getLocWithOffset(-1));
  } else {
   return getRWText(R, mb_comp->getLocStart(), mb_comp->getLocEnd());
  }
}

std::string tyOpSuffix(const clang::Type* ty) {
  if (ty->isCharType()) return "Int8";
  if (ty->isSpecificBuiltinType(BuiltinType::UShort)) return "Int32";
  if (ty->isSpecificBuiltinType(BuiltinType::Short)) return "Int32";
  if (ty->isSpecificBuiltinType(BuiltinType::UInt)) return "Int32";
  if (ty->isSpecificBuiltinType(BuiltinType::Int)) return "Int32";
  if (ty->isSpecificBuiltinType(BuiltinType::ULong)) return "Int64";
  if (ty->isSpecificBuiltinType(BuiltinType::Long)) return "Int64";
  if (ty->isSpecificBuiltinType(BuiltinType::ULongLong)) return "Int64";
  if (ty->isSpecificBuiltinType(BuiltinType::LongLong)) return "Int64";
  if (ty->isSpecificBuiltinType(BuiltinType::Float)) return "f32";
  if (ty->isSpecificBuiltinType(BuiltinType::Double)) return "f64";

  if (auto pty = dyn_cast<PointerType>(ty)) {
    return "Ptr_" + tyOpSuffix(ty->getPointeeType().getTypePtr());
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

bool isVoidPtr(const Type* inp_ty) {
  const PointerType* ptr_ty = dyn_cast<PointerType>(inp_ty);
  const Type* ty = ptr_ty ? ptr_ty->getPointeeType().getTypePtr() : nullptr;
  return ty && ty->isVoidType();
}

std::string tyName(const clang::Type* ty, std::string defaultName = "C2FUNK") {
  if (ty->isCharType()) return "Int8";
  if (ty->isSpecificBuiltinType(BuiltinType::UShort)) return "Int32";
  if (ty->isSpecificBuiltinType(BuiltinType::Short)) return "Int32";
  if (ty->isSpecificBuiltinType(BuiltinType::UInt)) return "Int32";
  if (ty->isSpecificBuiltinType(BuiltinType::Int)) return "Int32";
  if (ty->isSpecificBuiltinType(BuiltinType::ULong)) return "Int64";
  if (ty->isSpecificBuiltinType(BuiltinType::Long)) return "Int64";
  if (ty->isSpecificBuiltinType(BuiltinType::ULongLong)) return "Int64";
  if (ty->isSpecificBuiltinType(BuiltinType::LongLong)) return "Int64";
  if (ty->isSpecificBuiltinType(BuiltinType::Float)) return "Float32";
  if (ty->isSpecificBuiltinType(BuiltinType::Double)) return "Float64";

  if (ty->isSpecificBuiltinType(BuiltinType::Void)) return "()";

  if (auto dc = dyn_cast<DecayedType>(ty)) {
    std::string fnty = tryParseFnTy(dc->getDecayedType().getTypePtr());
    if (fnty != "") return fnty;
  }
  if (auto dc = dyn_cast<FunctionProtoType>(ty)) {
    return fnTyName(dc);
  }

  if (const TypedefType* tty = dyn_cast<TypedefType>(ty)) {
    return tyName(tty->desugar().getTypePtr(), tty->getDecl()->getNameAsString());
  }
  if (const PointerType* pty = dyn_cast<PointerType>(ty)) {
    // could mean either (Array t) or (Ref t)
    if (isVoidPtr(pty)) return "VOIDPTR";
    if (const RecordType* rty = bindRecordType(pty->getPointeeType().getTypePtr())) {
      return rty->getDecl()->getNameAsString();
    }

    return "(Array " + tyName(pty->getPointeeType().getTypePtr()) + ")";
  }

  if (const ConstantArrayType* cat = dyn_cast<ConstantArrayType>(ty)) {
    if (cat->getSizeModifier() != ArrayType::Normal) {
      llvm::outs() << "// TODO(f2c) handle size modified arrays\n";
    }
    auto sz = cat->getSize();
    return "(Array " + tyName(cat->getElementType().getTypePtr())
                     + " /*size=" + sz.toString(10, false) + "*/ )";
  }

  if (const ElaboratedType* ety = dyn_cast<ElaboratedType>(ty)) {
    if (ety->isSugared()) {
      return tyName(ety->desugar().getTypePtr());
    }
  }

  if (const RecordType* rty = dyn_cast<RecordType>(ty)) { return rty->getDecl()->getNameAsString(); }
  if (const ParenType* rty = dyn_cast<ParenType>(ty)) { return tyName(rty->getInnerType().getTypePtr()); }
  // TODO handle constantarraytype

  llvm::outs().flush();
  ty->dump();
  llvm::errs().flush();
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

std::string mkFosterBinop(const std::string& op, const clang::Type* typ) {
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

  if (op[0] == '<' || op[0] == '>') {
    if (typ->hasSignedIntegerRepresentation())
      return op + "S" + ty;
    if (typ->hasUnsignedIntegerRepresentation())
      return op + "U" + ty;
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

class MutableLocalHandler : public MatchFinder::MatchCallback {
public:
  MutableLocalHandler(std::map<std::string, bool>& locals) : locals(locals) {}

  virtual void run(const MatchFinder::MatchResult &Result) {
    if (auto v = Result.Nodes.getNodeAs<DeclRefExpr>("binopvar")) {
      if (auto bo = Result.Nodes.getNodeAs<BinaryOperator>("binop")) {
        if (bo->isAssignmentOp() || bo->isCompoundAssignmentOp())
          locals[v->getDecl()->getName()] = true;
      }
    }
    if (auto v = Result.Nodes.getNodeAs<DeclRefExpr>("addrtakenvar"))
      locals[v->getDecl()->getName()] = true;
    if (auto v = Result.Nodes.getNodeAs<VarDecl>("vardecl-noinit"))
      locals[v->getName()] = true;
    if (auto v = Result.Nodes.getNodeAs<VarDecl>("vardecl")) {
      if (!v->hasInit())
        locals[v->getName()] = true;
    }
  }

private:
  std::map<std::string, bool>& locals;
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

class FnBodyVisitor : public RecursiveASTVisitor<FnBodyVisitor> {
  public:
  FnBodyVisitor(std::map<std::string, bool>& locals,
                VoidPtrCasts& casts,
                ASTContext& ctx) : locals(locals), casts(casts), ctx(ctx) {}

  bool VisitStmt(Stmt* s) {
    MatchFinder mf;

    MutableLocalHandler mutloc_handler(locals);
    // assignments: x = ...
    mf.addMatcher( binaryOperator(hasLHS(declRefExpr().bind("binopvar"))).bind("binop") , &mutloc_handler);
    // address-of &x
    mf.addMatcher( unaryOperator(hasOperatorName("&"), hasUnaryOperand(declRefExpr().bind("addrtakenvar"))) , &mutloc_handler);
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

    mf.match(*s, ctx);
    return true;
  }

  void handlePotentialVoidPtrCast(const ValueDecl* v, const CStyleCastExpr* cse) {
    if (isVoidPtr(exprTy(v))) {
      casts[v].add(exprTy(cse));
    }
  }

  private:
  std::map<std::string, bool>& locals;
  VoidPtrCasts& casts;
  ASTContext& ctx;
};

class MyASTConsumer : public ASTConsumer {
public:
  MyASTConsumer(Rewriter &R) : lastloc(), R(R) { }

  void handleIfThenElse(const Stmt* cnd, const Stmt* thn, const Stmt* els) {
    llvm::outs() << "if ";
    visitStmt(cnd);
    llvm::outs() << " then ";
    visitStmt(thn);
    if (els) {
      llvm::outs() << " else ";
      visitStmt(els);
    }
    llvm::outs() << " end";
  }

  bool tryHandleConditionalOperator(const Stmt* stmt) {
    if (const ConditionalOperator* co = dyn_cast<ConditionalOperator>(stmt)) {
      handleIfThenElse(co->getCond(), co->getTrueExpr(), co->getFalseExpr());
      return true;
    }
    return false;
  }

  bool isDeclRefOf(const Expr* e, const Decl* d) {
    if (const DeclRefExpr* dre = dyn_cast<DeclRefExpr>(e)) {
      return dre->getDecl() == d;
    }
    return false;
  }

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
      // TODO write an explicit "ended" variable, for control flow
      if (stmt->getCond()) visitStmt(stmt->getCond()); else llvm::outs() << "True";
    llvm::outs() << " } {\n";
      visitStmt(stmt->getBody());
      // If the body wasn't a compound, we'll be missing a semicolon...
      if (extra) { llvm::outs() << "\n"; visitStmt(extra); }
    llvm::outs() << "}";
  }

  void translateGeneralForLoop(const ForStmt* fs) {
    if (fs->getInit()) { visitStmt(fs->getInit()); llvm::outs() << ";\n"; }
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
        llvm::outs() << "(" << incdec << tyName(unop) << " ";
        visitStmt(unop->getSubExpr(), true);
        llvm::outs() << ")";
      }
  }

  // clang::UnaryOperatorKind
  void handleUnaryOperator(const UnaryOperator* unop) {
    if (unop->getOpcode() == UO_LNot) {
      llvm::outs() << "(";
      visitStmt(unop->getSubExpr());
      llvm::outs() << " " << mkFosterBinop("!=", exprTy(unop));
      llvm::outs() << " " << "0" << ")";
    } else if (unop->getOpcode() == UO_Not) {
      llvm::outs() << "(bitnot-" + tyName(unop);
      visitStmt(unop->getSubExpr());
      llvm::outs() << ")";
    } else if (unop->getOpcode() == UO_Minus) {
      llvm::outs() << "(-";
      visitStmt(unop->getSubExpr());
      llvm::outs() << ")";
    } else if (unop->getOpcode() == UO_PreDec || unop->getOpcode() == UO_PostDec) {
      handleIncrDecr("decr", unop);
    } else if (unop->getOpcode() == UO_PreInc || unop->getOpcode() == UO_PostInc) {
      handleIncrDecr("incr", unop);
    } else if (unop->getOpcode() == UO_AddrOf) {
        visitStmt(unop->getSubExpr(), true);
    } else if (unop->getOpcode() == UO_Deref) {
        visitStmt(unop->getSubExpr());
        llvm::outs() << "^";
    } else {
      llvm::outs() << "/* line 424\n";
      llvm::outs().flush();
      unop->dump();
      llvm::errs().flush();
      llvm::outs() << "\n*/\n";
      llvm::outs() << getText(R, *unop) << "\n";
    }
  }

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
    if (ce->getNumArgs() == 0) { llvm::outs() << " !"; }
    llvm::outs() << ")";
  }

  // Emit calls to free() as comments, since we're presumably doing GC.
  bool tryHandleCallFree(const CallExpr* ce) {
    if (!isDeclNamed("free", ce->getCallee()->IgnoreParenImpCasts())) return false;
    if (ce->getNumArgs() != 1) return false;
    llvm::outs() << "// "; handleCall(ce); llvm::outs() << "\n";
    llvm::outs() << "()";
    return true;
  }

  // Recognize calls of the form malloc(sizeof(T) * EXPR);
  // and emit                   (allocDArray:[T] EXPR)
  bool tryHandleCallMalloc(const CallExpr* ce, const Type* result_typ) {
    if (!isDeclNamed("malloc", ce->getCallee()->IgnoreParenImpCasts())) return false;
    if (ce->getNumArgs() != 1) return false;
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
        llvm::outs() << "(allocDArray:[" << tyName(szty) << "] ";
        visitStmt(sztyL ? binop->getRHS() :  binop->getLHS());
        llvm::outs() << ")";
        return true;
      }
    }
    return false;
  }

  /*
    type case Ptr (t:Type)
          of $NullPtr
          of $Ptr t
          ;

    // assuming that t has a zero value
    type case Field (t:Type)
           of $Field (Ref t)
           ;
  */

  std::string zeroValueRecord(const RecordDecl* rd) {
    std::string name = rd->getName();
    if (TypedefNameDecl* tnd = rd->getTypedefNameForAnonDecl()) {
      name = tnd->getName();
    }

    if (name == "") {
      llvm::outs() << "// TODO handle this better...\n";
      llvm::errs() << "anon record\n";
      rd->dump();
      llvm::outs() << getText(R, *rd) << "\n";
      return "";
    }

    std::string rv = "(" + name;
    for (auto d : rd->decls()) {
      if (const FieldDecl* fd = dyn_cast<FieldDecl>(d)) {
        rv = rv + " " + zeroValueField(exprTy(fd));
      }
    }
    return rv + ")";
  }

  std::string zeroValueField(const Type* typ) {
    return "(MutField (ref " + zeroValue(typ) + " ))";
  }

  std::string zeroValue(const Type* typ) {
    if (typ->isFloatingType()) return "0.0";
    if (typ->isIntegerType()) return "0";
    if (typ->isPointerType()) return "NullPtr";
    if (auto tty = dyn_cast<TypedefType>(typ)) {
      return zeroValue(tty->desugar().getTypePtr());
    }
    if (auto rty = dyn_cast<ElaboratedType>(typ)) {
      return zeroValue(rty->getNamedType().getTypePtr());
    }
    if (auto rty = dyn_cast<RecordType>(typ)) {
      return zeroValueRecord(rty->getDecl());
    }
    return "None";
  }

  std::string fieldAccessorName(const MemberExpr* me) {
    DeclarationNameInfo dni = me->getMemberNameInfo();
    return tyName(exprTy(me->getBase())) + "_" + dni.getAsString();
  }

  void handleAssignment(const BinaryOperator* binop) {
    if (const MemberExpr* me = dyn_cast<MemberExpr>(binop->getLHS())) {
      // translate p->f = v;  to  (set_pType_f p v)
      llvm::outs() << "(set_" << fieldAccessorName(me) << " ";
      llvm::outs() << "(";
      visitStmt(me->getBase(), true);
      llvm::outs() << ") (";
      visitStmt(binop->getRHS());
      llvm::outs() << ")";
      llvm::outs() << ")";
    } else {
      llvm::outs() << "(";
      visitStmt(binop->getRHS());
      llvm::outs() << ") >^ ";
      visitStmt(binop->getLHS(), true);
    }
  }

  bool isSignConversion(const CastExpr* ce) {
    const Type* origType = exprTy(ce->getSubExpr());
    const Type* destType = exprTy(ce);
    // Assuming here that both are signed/unsigned integer (well, integral) types.
    return origType->isUnsignedIntegerType() != destType->isUnsignedIntegerType();
  }

  std::string fosterizedName(const std::string& name) {
    if (name == "end" || name == "do" || name == "type" || name == "case"
     || name == "of" || name == "as" || name == "then" || name == "in") {
      return name + "_";
    }
    return name;
  }

  std::string intCastFromTo(const std::string& srcTy, const std::string& dstTy, bool isSigned) {
    if (srcTy == "Int32" && dstTy == "Int8" ) return "trunc_i32_to_i8";
    if (srcTy == "Int64" && dstTy == "Int8" ) return "trunc_i64_to_i8";
    if (srcTy == "Int64" && dstTy == "Int32") return "trunc_i64_to_i32";
    if (srcTy == "Int8"  && dstTy == "Int32" && isSigned) return "sext_i8_to_i32";
    if (srcTy == "Int8"  && dstTy == "Int64" && isSigned) return "sext_i8_to_i64";
    if (srcTy == "Int32" && dstTy == "Int64" && isSigned) return "sext_i32_to_i64";
    if (srcTy == "Int8"  && dstTy == "Int32" && !isSigned) return "zext_i8_to_i32";
    if (srcTy == "Int8"  && dstTy == "Int64" && !isSigned) return "zext_i8_to_i64";
    if (srcTy == "Int32" && dstTy == "Int64" && !isSigned) return "zext_i32_to_i64";
    return "/*unhandled cast from " + srcTy + " to " + dstTy + "*/";
  }

  void handleCastExpr(const CastExpr* ce) {
    switch (ce->getCastKind()) {
    case CK_FloatingCast:
      llvm::outs() << " /*float cast*/ ";
      visitStmt(ce->getSubExpr());
      break;
    case CK_FloatingToIntegral:
      llvm::outs() << " /*float-to-int cast*/ ";
      visitStmt(ce->getSubExpr());
      break;
    case CK_IntegralToFloating:
      llvm::outs() << "(" << intToFloat(ce->getSubExpr(), exprTy(ce)) << " ";
      visitStmt(ce->getSubExpr());
      llvm::outs() << ")";
      break;
    case CK_PointerToBoolean:
      llvm::outs() << " /*pointer-to-bool cast*/ ";
      visitStmt(ce->getSubExpr());
      break;
    case CK_IntegralToBoolean:
      llvm::outs() << " /*integral-to-bool cast*/ ";
      visitStmt(ce->getSubExpr());
      break;
    case CK_IntegralCast: {
      std::string cast = "";
      if (const IntegerLiteral* lit = dyn_cast<IntegerLiteral>(ce->getSubExpr())) {
        // don't print anything, no cast needed
      } else if (isSignConversion(ce)) {
        // don't print anything either
      } else {
        std::string srcTy = tyName(exprTy(ce->getSubExpr())) ;
        std::string dstTy = tyName(exprTy(ce));
        if (srcTy != dstTy) {
          cast = intCastFromTo(srcTy, dstTy, exprTy(ce)->isSignedIntegerType());
        }
      }

      if (cast == "") {
        visitStmt(ce->getSubExpr());
      } else {
        llvm::outs() << "(" << cast << " ";
        visitStmt(ce->getSubExpr());
        llvm::outs() << ")";
      }
      break;
                          }
    default:
      visitStmt(ce->getSubExpr());
    }
  }

  void visitStmt(const Stmt* stmt, bool isAssignmentTarget = false) {
    emitCommentsFromBefore(stmt->getLocStart());

    if (const ImplicitCastExpr* ice = dyn_cast<ImplicitCastExpr>(stmt)) {
      if (ice->getCastKind() == CK_LValueToRValue
       || ice->getCastKind() == CK_FunctionToPointerDecay
       || ice->getCastKind() == CK_NoOp)
          return visitStmt(ice->getSubExpr());
      return handleCastExpr(ice);
    }

    if (const IfStmt* ifs = dyn_cast<IfStmt>(stmt)) {
      handleIfThenElse(ifs->getCond(), ifs->getThen(), ifs->getElse());
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
      handleIfThenElse(co->getCond(), co->getTrueExpr(), co->getFalseExpr());
    } else if (const ParenExpr* pe = dyn_cast<ParenExpr>(stmt)) {
      if (tryHandleConditionalOperator(pe->getSubExpr())) {
        // done
      } else {
        llvm::outs() << "(";
        visitStmt(pe->getSubExpr());
        llvm::outs() << ")";
      }
    } else if (const NullStmt* dr = dyn_cast<NullStmt>(stmt)) {
      llvm::outs() << "()";
    } else if (const GotoStmt* gs = dyn_cast<GotoStmt>(stmt)) {
      llvm::outs() << "// TODO(c2f): goto " << gs->getLabel()->getNameAsString() << "\n";
      llvm::outs() << "()";
    } else if (const BreakStmt* bs = dyn_cast<BreakStmt>(stmt)) {
      llvm::outs() << "// TODO(c2f): break;\n";
      llvm::outs() << "()";
    } else if (const ContinueStmt* cs = dyn_cast<ContinueStmt>(stmt)) {
      llvm::outs() << "// TODO(c2f): continue;\n";
      llvm::outs() << "()";
    } else if (const LabelStmt* ls = dyn_cast<LabelStmt>(stmt)) {
      llvm::outs() << "// TODO(c2f): label " << ls->getName() << ";\n";
      llvm::outs() << "()";
      visitStmt(ls->getSubStmt());
    } else if (const ReturnStmt* rs = dyn_cast<ReturnStmt>(stmt)) {
      llvm::outs() << "// TODO(c2f): return\n";
      if (rs->getRetValue()) {
        visitStmt(rs->getRetValue());
      } else {
        llvm::outs() << "()";
      }
    } else if (const MemberExpr* me = dyn_cast<MemberExpr>(stmt)) {
      llvm::outs() << "(" + fieldAccessorName(me) + " ";
      visitStmt(me->getBase());
      llvm::outs() << ")";
    } else if (const ArraySubscriptExpr* ase = dyn_cast<ArraySubscriptExpr>(stmt)) {
      visitStmt(ase->getBase());
      llvm::outs() << "[";
      visitStmt(ase->getIdx());
      llvm::outs() << "]";
    } else if (const BinaryOperator* binop = dyn_cast<BinaryOperator>(stmt)) {
      std::string op = binop->getOpcodeStr();
      if (op == "=") {
        handleAssignment(binop);
      } else if (op == "&&" || op == "||") {
        std::string tgt = (op == "&&" ? "`andand`" : "`oror`");
        llvm::outs() << "({ ";
        visitStmt(binop->getLHS());
        llvm::outs() << " } " << tgt << " { ";
        visitStmt(binop->getRHS());
        llvm::outs() << " })";
      } else {
        std::string tgt = mkFosterBinop(op, exprTy(binop->getLHS()));
        llvm::outs() << "(";
        visitStmt(binop->getLHS(), binop->isCompoundAssignmentOp());
        llvm::outs() << " " << tgt << " ";
        visitStmt(binop->getRHS());
        llvm::outs() << ")";
      }
    } else if (const UnaryOperator* unop = dyn_cast<UnaryOperator>(stmt)) {
      handleUnaryOperator(unop);
    } else if (const IntegerLiteral* lit = dyn_cast<IntegerLiteral>(stmt)) {
      lit->getValue().print(llvm::outs(), true);
    } else if (const StringLiteral* lit = dyn_cast<StringLiteral>(stmt)) {
      if (lit->isUTF8() || lit->isAscii()) {
        lit->outputString(llvm::outs());
      } else {
        llvm::outs() << "// non UTF8 string\n";
        lit->outputString(llvm::outs());
      }
    } else if (const FloatingLiteral* lit = dyn_cast<FloatingLiteral>(stmt)) {
      std::string litstr = getText(R, *lit);
      if (litstr != "") llvm::outs() << litstr;
      else {
        llvm::SmallString<128> buf;
        lit->getValue().toString(buf);
        llvm::outs() << "/*floatlit...*/" << buf;
      }
    } else if (const PredefinedExpr* lit = dyn_cast<PredefinedExpr>(stmt)) {
      lit->getFunctionName()->outputString(llvm::outs());
    } else if (const CastExpr* ce = dyn_cast<CastExpr>(stmt)) {
      handleCastExpr(ce);
    } else if (const DeclRefExpr* dr = dyn_cast<DeclRefExpr>(stmt)) {
      std::string name = dr->getDecl()->getName();
      if (mutableLocals[name] && !isAssignmentTarget) {
        llvm::outs() << fosterizedName(name) << "^";
      } else {
        llvm::outs() << fosterizedName(name);
      }
    } else if (const CStyleCastExpr* ce = dyn_cast<CStyleCastExpr>(stmt)) {
      if (tryHandleCallMallocCasted(ce)) {
        // done
      } else {
        llvm::outs() << "/* line 610\n";
        stmt->dump();
        llvm::outs() << "\n*/\n";
        llvm::outs() << getText(R, *stmt) << "\n";
      }
    } else if (const CallExpr* ce = dyn_cast<CallExpr>(stmt)) {
      if (tryHandleCallMalloc(ce, nullptr) || tryHandleCallFree(ce)) {
        // done
      } else {
        handleCall(ce);
      }
    } else if (const InitListExpr* ile = dyn_cast<InitListExpr>(stmt)) {
      if (ile->hasArrayFiller()) {
        llvm::outs() << "// WARNING: ignoring array filler\n";
      }
      if (ile->isStringLiteralInit()) {
        llvm::outs() << "// WARNING: string literal init...?\n";
      }
      llvm::outs() << "(prim mach-array-literal";
      for (unsigned i = 0; i < ile->getNumInits(); ++i) {
        llvm::outs() << " ";
        visitStmt(ile->getInit(i));
      }
      llvm::outs() << ")";
    } else if (const CompoundStmt* cs = dyn_cast<CompoundStmt>(stmt)) {
      for (const Stmt* c : cs->children()) {
        visitStmt(c);
        if (const CompoundStmt* x = dyn_cast<CompoundStmt>(c)) {
          // don't print another semicolon
        } else {
          llvm::outs() << ";\n";
        }
      }
    } else if (const DeclStmt* ds = dyn_cast<DeclStmt>(stmt)) {
      const Decl* last = *(ds->decls().end() - 1);
      for (const Decl* d : ds->decls()) {
        if (const VarDecl* vd = dyn_cast<VarDecl>(d)) {
          if (vd->hasInit()) {
            if (mutableLocals[vd->getName()]) {
              llvm::outs() << fosterizedName(vd->getName()) << " = (prim ref ";
              visitStmt(vd->getInit());
              llvm::outs() << ")";
            } else {
              llvm::outs() << fosterizedName(vd->getName()) << " = ";
              visitStmt(vd->getInit());
            }
          } else {
            llvm::outs() << vd->getName() << " = (prim ref " << zeroValue(exprTy(vd)) << ")";
          }
        } else {
          visitStmt(d->getBody());
        }
        if (d != last) llvm::outs() << ";\n";
      }
    } else if (const UnaryExprOrTypeTraitExpr* ue = dyn_cast<UnaryExprOrTypeTraitExpr>(stmt)) {
      if (ue->getKind() == UETT_SizeOf) {
        const Type* ty = bindSizeofType(ue);
        llvm::outs() << "0 // sizeof(" << tyName(ty) << ")\n";
      } else {
        llvm::outs().flush();
        llvm::errs() << "/* line 716\n";
        stmt->dump();
        llvm::errs() << "\n*/\n";
        llvm::errs().flush();
        llvm::outs() << getText(R, *stmt) << "\n";
      }
    } else {
      llvm::outs().flush();
      llvm::errs() << "/* line 655\n";
      stmt->dump();
      llvm::errs() << "\n*/\n";
      llvm::errs().flush();
      llvm::outs() << getText(R, *stmt) << "\n";
    }
  }

  std::string fieldOf(const std::string& fieldTyName) {
    return "(Field " +  fieldTyName + ")";
  }

  void handleRecordDecl(const RecordDecl* rd) {
    std::string name = rd->getName();
    if (TypedefNameDecl* tnd = rd->getTypedefNameForAnonDecl()) {
      name = tnd->getName();
    }

    if (name == "") {
      llvm::outs() << "// TODO handle this better...\n";
      llvm::errs() << "anon record\n";
      rd->dump();
      llvm::outs() << getText(R, *rd) << "\n";
      return;
    }

    llvm::outs() << "type case " << name
      << "\n       of $" << name << "\n";
    for (auto d : rd->decls()) {
      if (const FieldDecl* fd = dyn_cast<FieldDecl>(d)) {
        llvm::outs() << "             " << fieldOf(tyName(exprTy(fd))) << " // " << fd->getName() << "\n";
      }
    }
    llvm::outs() << ";\n\n";
    // TODO emit field accessor functions
  }

  bool isFromMainFile(const SourceLocation loc) {
    return R.getSourceMgr().isWrittenInMainFile(loc);
  }

  bool isFromMainFile(const Decl* d) { return isFromMainFile(d->getLocation()); }

  void performFunctionLocalAnalysis(FunctionDecl* d) {
    FnBodyVisitor v(mutableLocals, voidPtrCasts, d->getASTContext());
    v.TraverseDecl(d);
  }

  bool HandleTopLevelDecl(DeclGroupRef DR) override {
    for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b) {
      mutableLocals.clear();
      voidPtrCasts.clear();

      emitCommentsFromBefore((*b)->getLocStart());
      if (!isFromMainFile(*b)) {
        // skip it
      } else if (RecordDecl* rdo = dyn_cast<RecordDecl>(*b)) {
        if (!rdo->isThisDeclarationADefinition()) continue;
        if (RecordDecl* rd = rdo->getDefinition()) {
          if (rd->isEnum()) {
            llvm::outs() << "// TODO: translate enum definitions\n";
            continue;
          }
          if (!(rd->isClass() || rd->isStruct())) {
            continue;
          }

          handleRecordDecl(rd);
        }
      } else if (FunctionDecl* fd = dyn_cast<FunctionDecl>(*b)) {
        if (Stmt* body = fd->getBody()) {
          performFunctionLocalAnalysis(fd);

          llvm::outs() << fosterizedName(fd->getName()) << " = {\n";
          for (unsigned i = 0; i < fd->getNumParams(); ++i) {
            ParmVarDecl* d = fd->getParamDecl(i);
            auto vpcset = voidPtrCasts[d];
            const Type* ty = vpcset.unique() ? vpcset.front() : exprTy(d);
            if (!isVoidPtr(ty)) {
              llvm::outs() << "    " << fosterizedName(d->getDeclName().getAsString())
                            << " : " << tyName(ty) << " =>\n";
            }
          }
          // TODO rebind parameters if they are mutable locals
          visitStmt(body);
          llvm::outs() << "};\n";
        }
      } else if (TypedefDecl* fd = dyn_cast<TypedefDecl>(*b)) {
        llvm::outs() << "/* " << getText(R, *fd) << ";*/\n";
      } else if (VarDecl* vd = dyn_cast<VarDecl>(*b)) {
        llvm::outs() << "/* Unhandled global variable declaration:\n" << getText(R, *vd) << ";*/\n";
      } else {
        llvm::errs() << "unhandled top-level decl\n";
        (*b)->dump();
      }
    }
    return true;
  }

  std::string intToFloat(const Expr* srcexpr, const Type* tgt) {
    const Type* src = exprTy(srcexpr);
    const std::string srcTy = tyName(src);
    const std::string tgtTy = tyName(tgt);
    if (srcTy == "Int32" && tgtTy == "Float64") return (src->isSignedIntegerType() ? "s32-to-f64" : "u32-to-f64");
    if (srcTy == "Int64" && tgtTy == "Float64") return (src->isSignedIntegerType() ? "s64-to-f64-unsafe" : "u64-to-f64-unsafe");
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
      if (isFromMainFile(comments[i]->getLocStart())) {
        if (R.getSourceMgr().isBeforeInTranslationUnit(comments[i]->getLocStart(), loc)) {
          // If we don't have a last location, or if the comment comes
          // after the last location, emit it.
          if (!lastloc.isValid() || R.getSourceMgr().isBeforeInTranslationUnit(lastloc, comments[i]->getLocStart())) {
            llvm::outs() << getText(R, *comments[i]) << "\n";
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
  std::map<std::string, bool> mutableLocals;
  VoidPtrCasts voidPtrCasts;
  Rewriter R;
};

// For each source file provided to the tool, a new FrontendAction is created.
class C2F_FrontendAction : public ASTFrontendAction {
public:
  C2F_FrontendAction() {}

  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    TheRewriter.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<MyASTConsumer>(TheRewriter);
  }

  void EndSourceFileAction() override {
    //TheRewriter.getEditBuffer(TheRewriter.getSourceMgr().getMainFileID())
    //    .write(llvm::outs());
  }

private:
  Rewriter TheRewriter;
};

// You'll probably want to invoke with -fparse-all-comments
int main(int argc, const char **argv) {
  CommonOptionsParser op(argc, argv, CtoFosterCategory);
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());

  return Tool.run(newFrontendActionFactory<C2F_FrontendAction>().get());
}

// Notes on un-handled C constructs:
//   * Local control flow statements (break, continue, return)
//     not yet implemented.
//   * Struct fields not yet properly translated.
//     A field of type T can be translated to any one of:
//       T                         when all structs are literals and the field is never mutated,
//                                 or if all mutations can be coalesced into struct allocation.
//       (Ref T)                   for mutable fields
//       (Ref (Maybe T))           for mutable fields with uncertain initialization
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
//  * Local struct decls are stack-allocated in C, but we allocate (ref None) to be safe,
//    and it's not clear where/when/how to upgrade that allocation or update the ref contents.
//    E.g.::
//       struct S ss; struct S* ps = &ss; S_init(ps);
//    should have a better translation than
//       ss = (ref None); ps = ss; S_init ps;
