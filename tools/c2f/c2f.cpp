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
//
// Originally based on AST matching sample by Eli Bendersky (eliben@gmail.com).
//------------------------------------------------------------------------------
#include <string>
#include <sstream>

#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Analysis/CFG.h"
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

static llvm::cl::OptionCategory CtoFosterCategory("C-to-Foster");

static std::string getRWText(const Rewriter &R, const SourceLocation& locstt, const SourceLocation& locend) {
  return R.getRewrittenText(SourceRange(locstt, locend));
}

static bool startswith(const std::string& a, const std::string& b) {
  return a.size() >= b.size() && a.substr(0, b.size()) == b;
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

  if (auto pty = dyn_cast<PointerType>(ty)) {
    return "Ptr_" + tyOpSuffix(ty->getPointeeType().getTypePtr());
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

bool isTrivialIntegerLiteralInRange(const Expr* e, int lo, int hi) {
  if (auto lit = dyn_cast<IntegerLiteral>(e)) {
    auto se = lit->getValue().getSExtValue();
    return se >= lo && se <= hi;
  }
  return false;
}

std::string fosterizedTypeName(std::string rv) {
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

  if (ty->isSpecificBuiltinType(BuiltinType::Void)) return "()";

  return fosterizedTypeName(maybeNonUppercaseTyName(ty, defaultName));
}


std::string maybeNonUppercaseTyName(const clang::Type* ty, std::string defaultName) {

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
  if (const PointerType* pty = dyn_cast<PointerType>(ty)) {
    // could mean either (Array t) or (Ref t) or t
    if (isVoidPtr(pty)) return "VOIDPTR";
    if (const RecordType* rty = bindRecordType(pty->getPointeeType().getTypePtr())) {
      auto nm = rty->getDecl()->getNameAsString();
      if (!nm.empty()) return nm;

      return tyName(pty->getPointeeType().getTypePtr());
    }

    return "(Ptr " + tyName(pty->getPointeeType().getTypePtr()) + ")";
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
      auto nm = tyName(ety->desugar().getTypePtr());
      if (!nm.empty()) return nm;
    }
  }

  if (const RecordType* rty = dyn_cast<RecordType>(ty)) { return rty->getDecl()->getNameAsString(); }
  if (const ParenType* rty = dyn_cast<ParenType>(ty)) { return tyName(rty->getInnerType().getTypePtr()); }

  if (const EnumType* ety = dyn_cast<EnumType>(ty)) {
    std::string name = ety->getDecl()->getCanonicalDecl()->getNameAsString();
    if (name.empty()) {
      auto tnd = ety->getDecl()->getTypedefNameForAnonDecl();
      if (tnd) name = tnd->getNameAsString();
    }
    if (name.empty()) name = "/*EnumType unknown*/";
    return name;
  }

  // If we were going to handle fixed-size array types, this is probably where we'd do it.
  if (const DecayedType* dty = dyn_cast<DecayedType>(ty)) { return tyName(dty->getDecayedType().getTypePtr()); }

  // TODO handle constantarraytype

  if (defaultName == "C2FUNK") {
    llvm::outs().flush();
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

  if (op == "%") return infixOp("mod-", ty);
  if (op == "/") return infixOp("div-", ty);

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
        if (bo->isAssignmentOp() || bo->isCompoundAssignmentOp()) {
          locals[v->getDecl()->getName()] = true;
        }
      }
    }
    if (auto v = Result.Nodes.getNodeAs<DeclRefExpr>("unaryopvar")) {
      locals[v->getDecl()->getName()] = true;
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

class FnBodyVisitor : public RecursiveASTVisitor<FnBodyVisitor> {
  public:
  FnBodyVisitor(std::map<std::string, bool>& locals,
                std::map<const Stmt*, bool>& innocuousReturns,
                VoidPtrCasts& casts,
                bool& needsCFG,
                ASTContext& ctx) : locals(locals), innocuousReturns(innocuousReturns),
                        casts(casts), needsCFG(needsCFG), ctx(ctx) {}

  // Note: statements are visited top-down / preorder;
  // we rely on this fact to identify and tag "innocuous" control flow
  // statements from their parents, before they are recursively visited.
  bool VisitStmt(Stmt* s) {
    MatchFinder mf;

    MutableLocalHandler mutloc_handler(locals);
    // assignments: x = ...
    mf.addMatcher( binaryOperator(hasLHS(declRefExpr().bind("binopvar"))).bind("binop") , &mutloc_handler);
    // address-of &x
    mf.addMatcher( unaryOperator(hasOperatorName("&"), hasUnaryOperand(declRefExpr().bind("addrtakenvar"))) , &mutloc_handler);
    // incr/decr unary operators
    mf.addMatcher( unaryOperator(hasOperatorName("++"), hasUnaryOperand(declRefExpr().bind("unaryopvar"))) , &mutloc_handler);
    mf.addMatcher( unaryOperator(hasOperatorName("--"), hasUnaryOperand(declRefExpr().bind("unaryopvar"))) , &mutloc_handler);
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
  std::map<std::string, bool>& locals;
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

class MyASTConsumer : public ASTConsumer {
public:
  MyASTConsumer(Rewriter &R) : lastloc(), R(R) { }

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
    ss << "mustbecont_";

    if (const Stmt* lab = cb.getLabel()) {
      if (const LabelStmt* labstmt = dyn_cast<LabelStmt>(lab)) {
        ss << labstmt->getName();
        return ss.str();
      }
    }
    ss << "block_" << cb.getBlockID();
    return ss.str();
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

  // TODO support ternary conditional operators in CFGs
  void emitJumpTo(CFGBlock::AdjacentBlock* ab, bool hasValue = true) {
    if (CFGBlock* next = ab->getReachableBlock()) {
      if (isExitBlock(next)) {
        if (!hasValue) {
          llvm::outs() << "(jump = (); jump)";
        } else {
          llvm::outs() << "/*exit block, !hasValue*/ ()";
        }
      } else {
        llvm::outs() << getBlockName(*next) << " !;\n";
      }
    } else if (CFGBlock* next = ab->getPossiblyUnreachableBlock()) {
      llvm::outs() << getBlockName(*next) << " !; // unreachable\n";
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

  void visitStmtCFG(const Stmt* stmt) {
    // Make sure that binary operators, like || and &&,
    // don't get split up into separate CFG blocks, since
    // the way Clang does so is a pain to reconstruct into
    // well-scoped CPS-style expressions.
    LogicalAndOrTweaker tweaker(tweakedStmts);
    tweaker.TraverseStmt(const_cast<Stmt*>(stmt));

    CFG::BuildOptions BO;
    std::unique_ptr<CFG> cfg = C2F_buildCFG(nullptr, const_cast<Stmt*>(stmt), Ctx, BO);

    if (0) {
      llvm::outs().flush();
      llvm::errs() << "/*\n";
      LangOptions LO;
      cfg->dump(LO, false);
      llvm::errs() << "\n*/\n";
      llvm::errs().flush();
    }

    if (1) {
      llvm::outs() << "/*\n";
      llvm::outs() << getText(R, *stmt) << "\n";
      llvm::outs() << "*/\n";
    }

    // One not-completely-obvious thing about Clang's CFG construction
    // is that it can lead to duplicated statements, potentially across
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
      if (d->isSingleDecl()) {
        if (const VarDecl* vd = dyn_cast<VarDecl>(d->getSingleDecl())) {
          mutableLocals[vd->getName()] = true;
          // Unfortunately, all variables must be treated as mutable
          // when we are doing CFG-based generation, because the CFG
          // doesn't respect variable scoping rules.
        }
      }
      visitStmt(d, StmtContext);
      llvm::outs() << ";\n";
    }

    for (auto it = cfg->nodes_begin(); it != cfg->nodes_end(); ++it) {
      CFGBlock* cb = *it;
      if (isExitBlock(cb)) continue;

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
                  if (vd->hasInit() && mutableLocals[vd->getName()]) {
                    emitPoke(vd, vd->getInit());
                  } else if (!mutableLocals[vd->getName()]) {
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
          }
        } else {
          llvm::outs() << "// non-stmt cfg element...\n";
        }
      }

      if (cb->succ_size() == 1) {
        emitJumpTo(cb->succ_begin(), stmtHasValue(getBlockTerminatorOrLastStmt(cb)));
      } else if (cb->succ_size() == 2) {
        if (const Stmt* tc = cb->getTerminatorCondition()) {
          // Similar to handleIfThenElse, but with emitJumpTo instead of visitStmt.
          bool hasVal = stmtHasValue(getBlockTerminatorOrLastStmt(cb));
          llvm::outs() << "/* hasVal=" << hasVal << " */ ";
          llvm::outs() << "if ";
          visitStmt(tc, BooleanContext);
          llvm::outs() << " then ";
          emitJumpTo(cb->succ_begin(), hasVal);
          llvm::outs() << " else ";
          emitJumpTo(cb->succ_begin() + 1, hasVal);
          llvm::outs() << "end";
        }
      } else if (const SwitchStmt* ss = dyn_cast<SwitchStmt>(cb->getTerminator())) {
        // SwitchStmt terminator
        llvm::outs() << "/*line 617*/ ";
        llvm::outs() << "case ";
        visitStmt(cb->getTerminatorCondition(), StmtContext);
        llvm::outs() << "\n";

        // Walk through the successor blocks.
        // If it's a fallthrough, associate the case label with the
        // target block.
        // If it's not a fallthrough, associate with our own block.

        CFGBlock::AdjacentBlock* defaultBlock = nullptr;
        std::map<CFGBlock*, std::vector<Stmt*> > labelsFor;

        std::vector<CFGBlock::AdjacentBlock*> adjs;
        for (auto it = cb->succ_rbegin(); it != cb->succ_rend(); ++it) {
          if (!it->getReachableBlock()) {
            llvm::outs() << "(prim kill-entire-process \"CFGBlock had no reachable block!\")\n";
            continue;
          }
          if (isEmptyFallthroughAdjacent(&*it)) {
            labelsFor[it->getReachableBlock()->succ_begin()->getReachableBlock()].push_back(
                      it->getReachableBlock()->getLabel());
          } else {
            adjs.push_back(&*it);
            labelsFor[it->getReachableBlock()].push_back(
                      it->getReachableBlock()->getLabel());
          }
        }

        // TODO does this handle fallthrough into the default block?
        for (auto adj : adjs) {
          const std::vector<Stmt*>& labels = labelsFor[adj->getReachableBlock()];
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
                emitJumpTo(adj);
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
          emitJumpTo(defaultBlock);
        }

        llvm::outs() << "\nend\n";
      }

      llvm::outs() << "};\n";

    }

    llvm::outs() << getBlockName(cfg->getEntry()) << " !;\n";
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

    llvm::outs() << "/*line 691*/ ";
    llvm::outs() << "case ";
    visitStmt(ss->getCond());
    llvm::outs() << "\n";
    // Assuming the body is a CompoundStmt of CaseStmts...
    visitStmt(ss->getBody(), StmtContext);

    if (ss->isAllEnumCasesCovered()) {
      llvm::outs() << "// all enum cases covered\n";
    } else {
      llvm::outs() << "// not all enum cases covered...\n";
    }

    llvm::outs() << "end\n";

  }

  void emitPeek(const Expr* base, const Expr* idx) {
      std::string tynm = tyName(exprTy(base));
      if (startswith(tynm, "(Array")) {
        visitStmt(base);
        llvm::outs() << "[";
        visitStmt(idx);
        llvm::outs() << "]";
      } else {
        llvm::outs() << "(ptrGetIndex ";
        visitStmt(base);
        llvm::outs() << " ";
        visitStmt(idx);
        llvm::outs() << ")";
      }
  }

  template <typename Lam>
  void emitPokeIdx(const ArraySubscriptExpr* ase, Lam& valEmitter, ContextKind ctx) {
      auto base = ase->getBase();
      auto idx  = ase->getIdx();
      std::string tynm = tyName(exprTy(base));
      if (startswith(tynm, "(Ptr")) {
        llvm::outs() << "(ptrSetIndex ";
        visitStmt(base);
        llvm::outs() << " ";
        visitStmt(idx);
        llvm::outs() << " ";
        valEmitter();

        if (ctx == ExprContext) {
          llvm::outs() << "; "; emitPeek(base, idx);
        }
        // TODO BooleanContext
        llvm::outs() << ");";
      } else {
        llvm::outs() << "((";
        valEmitter();
        llvm::outs() << " >^ (";
        visitStmt(base);
        llvm::outs() << "[";
        visitStmt(idx);
        llvm::outs() << "] ) )";

        if (ctx == ExprContext) {
          llvm::outs() << "; "; emitPeek(base, idx);
        } else if (ctx == BooleanContext) {
          llvm::outs() << "; "; emitPeek(base, idx);
          llvm::outs() << " " << mkFosterBinop("!=", exprTy(ase)) << " 0";
        }
        llvm::outs() << ");";
      }
  }

  template <typename Lam>
  void emitPoke_(const Expr* ptr, Lam valEmitter, ContextKind ctx) {
      std::string tynm = tyName(exprTy(ptr));

      if (auto ase = dyn_cast<ArraySubscriptExpr>(ptr)) {
        emitPokeIdx(ase, valEmitter, ctx);
      } else if (startswith(tynm, "(Ptr")) {
        llvm::outs() << "(ptrSet (";
        visitStmt(ptr);
        llvm::outs() << ") (";
        valEmitter();
        llvm::outs() << ")";
        if (ctx == ExprContext) {
          llvm::outs() << "; "; visitStmt(ptr);
        }
        // TODO BooleanContext
        llvm::outs() << ");";
      } else {
        // If we have something like (c = (b = a)),
        // translate it to (a >^ b; b) >^ c
        llvm::outs() << "((";
        valEmitter();
        llvm::outs() << ") >^ (";
        visitStmt(ptr, AssignmentTarget);
        llvm::outs() << ")";
        if (ctx == ExprContext) {
          llvm::outs() << "; "; visitStmt(ptr);
        } else if (ctx == BooleanContext) {
          llvm::outs() << "; "; visitStmt(ptr);
          llvm::outs() << " " << mkFosterBinop("!=", exprTy(ptr)) << " 0";
        }
        llvm::outs() << ");";
      }
  }

  void emitPoke(const Expr* ptr, const Expr* val, ContextKind ctx) {
    emitPoke_(ptr, [=]() { visitStmt(val); }, ctx);
  }

  void emitPoke(const VarDecl* ptr, const Expr* val) {
      llvm::outs() << "((";
      visitStmt(val);
      llvm::outs() << ") >^ " << emitVarName(ptr) << ");";
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
        if (stmt->getCond()->getType()->isPointerType()) {
          llvm::outs() << "isNonNull ";
        }
        llvm::outs() << "( ";
        visitStmt(stmt->getCond());
        llvm::outs() << " )";
      } else llvm::outs() << "True";
    llvm::outs() << " } {\n";
      visitStmt(stmt->getBody());
      // If the body wasn't a compound, we'll be missing a semicolon...
      if (extra) { llvm::outs() << "\n"; visitStmt(extra); }

      llvm::outs() << ";\n()";
    llvm::outs() << "}";
  }

  void translateGeneralForLoop(const ForStmt* fs) {
    if (fs->getInit()) { visitStmt(fs->getInit(), StmtContext); llvm::outs() << ";\n"; }
    translateWhileLoop(fs, "while", fs->getInc());
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

  void handleIncrDecr(const std::string& incdec, const UnaryOperator* unop) {
      if (const ArraySubscriptExpr* ase = dyn_cast<ArraySubscriptExpr>(unop->getSubExpr())) {
        llvm::outs() << "(" << incdec << "Array" << tyName(unop) << " ";
        visitStmt(ase->getBase());
        llvm::outs() << " ";
        visitStmt(ase->getIdx());
        llvm::outs() << ")";
      } else {
        llvm::outs() << "(" << incdec << fosterizedNameChars(tyName(unop)) << " ";
        visitStmt(unop->getSubExpr(), AssignmentTarget);
        llvm::outs() << ")";
      }
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

      std::string tgt = mkFosterBinop(op, exprTy(binop->getLHS()));
      llvm::outs() << "(";
      visitStmt(binop->getLHS(), (binop->isCompoundAssignmentOp() ? AssignmentTarget : ExprContext));
      llvm::outs() << " " << tgt << " ";
      visitStmt(binop->getRHS());
      llvm::outs() << ")";

      if (isBooleanContext && !isComparison) { llvm::outs() << " " << mkFosterBinop("!=", exprTy(binop)) << " 0 /*L907*/)"; }
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
        std::string tgt = mkFosterBinop("-", exprTy(unop->getSubExpr()));
        llvm::outs() << "(0 " << tgt << " ";
        visitStmt(unop->getSubExpr());
        llvm::outs() << ")";
      }
    } else if (unop->getOpcode() == UO_Plus) {
      // Unary plus gets ignored, basically.
      visitStmt(unop->getSubExpr());
    } else if (unop->getOpcode() == UO_PreDec) {
      handleIncrDecr("decr", unop);
    } else if (unop->getOpcode() == UO_PostDec) {
      handleIncrDecr("postdecr", unop);
    } else if (unop->getOpcode() == UO_PostInc) {
      handleIncrDecr("postincr", unop);
    } else if (unop->getOpcode() == UO_PreInc) {
      handleIncrDecr("incr", unop);
    } else if (unop->getOpcode() == UO_AddrOf) {
      visitStmt(unop->getSubExpr(), AssignmentTarget);
    } else if (unop->getOpcode() == UO_Deref) {
      if (isDeclRefOfMutableAlias(unop->getSubExpr())) {
        visitStmt(unop->getSubExpr());
      } else {
        llvm::outs() << "(ptrGet ";
        llvm::outs() << "/* " << tyName(exprTy(unop->getSubExpr())) << " */";
        visitStmt(unop->getSubExpr());
        llvm::outs() << ")";
      }
    } else {
      llvm::outs() << "/* line 424\n";
      llvm::outs().flush();
      unop->dump();
      llvm::errs().flush();
      llvm::outs() << "\n*/\n";
      llvm::outs() << getText(R, *unop) << "\n";
    }
  }

  bool isDeclRefOfMutableAlias(const Expr* e) {
    if (auto dre = dyn_cast<DeclRefExpr>(e->IgnoreParenImpCasts())) {
      return mutableLocalAliases[dre->getDecl()->getName()];
    }
    return false;
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
    if (ce->getNumArgs() == 0) { llvm::outs() << " !"; }
    llvm::outs() << ")";
  }

  bool tryHandleCallPrintf(const CallExpr* ce) {
    if (!isDeclNamed("printf", ce->getCallee()->IgnoreParenImpCasts())) return false;
    if (ce->getNumArgs() == 1) {
      // Assume one-arg printf means literal text.
      llvm::outs() << "(printStr ";
      visitStmt(ce->getArg(0));
      llvm::outs() << ")";
      return true;
    }
    if (ce->getNumArgs() != 2) return false;

    if (auto slit = dyn_cast<StringLiteral>(ce->getArg(0)->IgnoreParenImpCasts())) {
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
      } else if (slit->getString() == "0x%X\n" || slit->getString() == "0x%lX\n") {
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
      visitStmt(count);

      if (variant == "cmp") {
        auto ty = getElementType(exprTy(ce->getArg(0)->IgnoreParenImpCasts()));
        std::string suffix = (ty->hasSignedIntegerRepresentation()) ? "S" : "U";
        llvm::outs() << " " << mkFosterBinop("cmp-" + suffix, ty);
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

  // Recognize calls of the form malloc(sizeof(T) * EXPR);
  // and emit               strLit (allocDArray:[T] EXPR)
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
        llvm::outs() << "(strLit (allocDArray:[" << tyName(szty) << "] ";
        visitStmt(sztyL ? binop->getRHS() :  binop->getLHS());
        llvm::outs() << "))";
        return true;
      }
    }
    return false;
  }

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
    return "None";
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
  std::string fieldAccessorName(const MemberExpr* me, const Expr* & base) {
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
    return tyName(exprTy(base)) + path + "_" + me->getMemberNameInfo().getAsString();
  }

  void handleAssignment(const BinaryOperator* binop, ContextKind ctx) {
    if (const MemberExpr* me = dyn_cast<MemberExpr>(binop->getLHS())) {
      // translate p->f = x;  to  (set_pType_f p x)
      const Expr* base = nullptr;
      llvm::outs() << "(set_" << fieldAccessorName(me, base) << " ";
      llvm::outs() << "(";
      visitStmt(base, ExprContext);
      llvm::outs() << ") (";
      visitStmt(binop->getRHS());
      llvm::outs() << ")";
      llvm::outs() << ")";
    } else {
      // translate v = x;  to  (x) >^ v;
      emitPoke(binop->getLHS(), binop->getRHS(), ctx);
    }
  }

  void handleCompoundAssignment(const BinaryOperator* binop, ContextKind ctx) {
    std::string op = binop->getOpcodeStr();
    if (op.back() == '=') op.pop_back();

    std::string tgt = mkFosterBinop(op, exprTy(binop->getLHS()));

    if (const MemberExpr* me = dyn_cast<MemberExpr>(binop->getLHS())) {
      // translate p->f OP= v;  to  (set_pType_f p ((pType_f p) OP v))
      const Expr* base = nullptr;
      std::string accessor = fieldAccessorName(me, base);
      llvm::outs() << "(set_" << accessor << " ";
      llvm::outs() << "(";
      visitStmt(base, ExprContext);
      llvm::outs() << ") (";

        llvm::outs() << "(" << accessor << " ";
        llvm::outs() << "(";
        visitStmt(base, ExprContext); // ExprContext?
        llvm::outs() << ")";
        llvm::outs() << ")";

        llvm::outs() << " " << tgt << " ";

        visitStmt(binop->getRHS());
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
          if (srcTy != dstTy) {
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

  std::string fosterizedName(const std::string& name) {
    if (name == "to" || name == "do" || name == "type" || name == "case"
     || name == "of" || name == "as" || name == "then" || name == "end"
     || name == "in") {
      return name + "_";
    }
    if (name.empty()) {
      return "__empty__";
    }
    if (isupper(name[0])) {
      return "v_" + name;
    }
    if (name == "strlen") return "ptrStrlen";
    return name;
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
      return exprTy(ce) == exprTy(sce->getSubExpr());
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
      llvm::outs() << "PtrNil";
      break;
    case CK_ToVoid:
      if (isa<IntegerLiteral>(ce->getSubExpr()->IgnoreParens())) {
        llvm::outs() << "(tovoid = (); tovoid)";
      } else {
        visitStmt(ce->getSubExpr(), ctx);
      }
      break;
    case CK_FloatingCast:
      llvm::outs() << " /*float cast*/ ";
      visitStmt(ce->getSubExpr(), ctx);
      break;
    case CK_FloatingToIntegral:
      llvm::outs() << " /*float-to-int cast*/ ";
      visitStmt(ce->getSubExpr(), ctx);
      break;
    case CK_IntegralToFloating:
      llvm::outs() << "(" << intToFloat(ce->getSubExpr(), exprTy(ce)) << " ";
      visitStmt(ce->getSubExpr());
      llvm::outs() << ")";
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

      if (isNestedCastThatCancelsOut(ce)
       || isTrivialIntegerLiteralInRange(ce->getSubExpr(), 0, 127)
       || isa<CharacterLiteral>(ce->getSubExpr())
       || (exprTy(ce)->isUnsignedIntegerType() &&
             isTrivialIntegerLiteralInRange(ce->getSubExpr(), 0, 255))) {
        // don't print anything, no cast needed
      } else {
        std::string srcTy = tyName(exprTy(ce->getSubExpr())) ;
        std::string dstTy = tyName(exprTy(ce));

        if (srcTy != dstTy) {
          cast = intCastFromTo(srcTy, dstTy, exprTy(ce->getSubExpr())->isSignedIntegerType());
        }
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
        if (ctx == BooleanContext) { llvm::outs() << " " << mkFosterBinop("!=", exprTy(ce)) << " 0)"; }
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

  std::string enumPrefix(const EnumDecl* ed) {
    std::string prefix = ed->getNameAsString();
    if (!prefix.empty()) prefix += "_";
    return prefix;
  }

  std::string enumConstantAccessor(const EnumDecl* ed,
                                   const EnumConstantDecl* ecd) {
    std::string prefix = enumPrefix(ed);
    return prefix + ecd->getNameAsString();
  }

  std::string emitVarName(const ValueDecl* vd) {
    if (auto ecd = dyn_cast<EnumConstantDecl>(vd)) {
      const EnumDecl* ed = enumDeclsForConstants[ecd];
      if (ed)
        return "(" + enumConstantAccessor(ed, ecd) + " !)";
      else
        return "(prim kill-entire-process \"ERROR-no-enum-decl-for-" + ecd->getNameAsString() + "\")";
    }

    auto it = duplicateVarDecls.find(vd);
    if (it == duplicateVarDecls.end()) {
      return fosterizedName(vd->getName());
    } else {
      std::string s;
      std::stringstream ss(s); ss << fosterizedName(vd->getName()) << "_" << it->second;
      return ss.str();
    }
  }

  void visitVarDecl(const VarDecl* vd) {
    if (vd->hasInit()) {
      if (mutableLocals[vd->getName()]) {
        llvm::outs() << emitVarName(vd) << " = (prim ref ";
        visitStmt(vd->getInit());
        llvm::outs() << ")";
      } else {
        llvm::outs() << emitVarName(vd) << " = ";
        visitStmt(vd->getInit());

        if (auto uno = dyn_cast<UnaryOperator>(vd->getInit())) {
          if (auto dre = dyn_cast<DeclRefExpr>(uno->getSubExpr())) {
            if (isPrimRef(dre->getDecl())) {
              mutableLocalAliases[vd->getName()] = true;
            }
          }
        }
      }
    } else {
      const Type* ty = vd->getType().getTypePtr();
      if (auto cat = dyn_cast<ConstantArrayType>(ty)) {
        uint64_t sz = cat->getSize().getZExtValue();
        auto zeroval = zeroValue(cat->getElementType().getTypePtr());

        llvm::outs() << emitVarName(vd) << " = ";
        if (sz > 0 && sz <= 16) {
          llvm::outs() << "(strLit:[" << tyName(cat->getElementType().getTypePtr()) << "] (prim mach-array-literal";
          for (uint64_t i = 0; i < sz; ++i) {
            llvm::outs() << " " << zeroval;
          }
          llvm::outs() << "))";
        } else {
          llvm::outs() << "(newArrayReplicate " << sz << " " << zeroval << ")";
        }
      } else {
        llvm::outs() << emitVarName(vd) << " = (prim ref " << zeroValue(exprTy(vd)) << ")";
      }
    }
  }

  const BinaryOperator*
  tryBindAssignmentOp(const Stmt* stmt) {
    if (auto bo = dyn_cast<BinaryOperator>(stmt)) {
      if (bo->isAssignmentOp()) {
        return bo;
      }
    }
    return nullptr;
  }

  void visitStmt(const Stmt* stmt, ContextKind ctx = ExprContext) {
    emitCommentsFromBefore(stmt->getLocStart());

    // When visiting a bound substatement, emit its variable binding.
    auto it = StmtMap.find(stmt);
    if (it != StmtMap.end()) {
      auto pair = it->second;
      if (stmt != currStmt) {
        llvm::outs() << "b_" << pair.first << "_" << pair.second;
        if (ctx == BooleanContext) {
          if (auto expr = dyn_cast<Expr>(stmt)) {
            llvm::outs() << " " << mkFosterBinop("!=", exprTy(expr)) << " 0"; } }
        return;
      }

      if (stmt == currStmt && !isa<ReturnStmt>(stmt)) {
        llvm::outs() << "b_" << pair.first << "_" << pair.second << " = ";
        ctx = ExprContext;
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
      if (isa<BreakStmt>(ds->getSubStmt())) {
        llvm::outs() << "(breakstmt = (); breakstmt)\n";
      }
    } else if (const SwitchStmt* ss = dyn_cast<SwitchStmt>(stmt)) {
      handleSwitch(ss);
    } else if (const GotoStmt* gs = dyn_cast<GotoStmt>(stmt)) {
      llvm::outs() << "mustbecont_" << gs->getLabel()->getNameAsString() << " !\n";
    } else if (isa<BreakStmt>(stmt) || isa<ContinueStmt>(stmt)) {
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
      llvm::outs() << "(" + fieldAccessorName(me, base) + " ";
      visitStmt(base, ExprContext);
      llvm::outs() << ")";
      if (ctx == BooleanContext) { llvm::outs() << " " << mkFosterBinop("!=", exprTy(me)) << " 0 /*L1922*/)"; }
    } else if (const ArraySubscriptExpr* ase = dyn_cast<ArraySubscriptExpr>(stmt)) {
      emitPeek(ase->getBase(), ase->getIdx());
    } else if (const CompoundAssignOperator* cao = dyn_cast<CompoundAssignOperator>(stmt)) {
      handleCompoundAssignment(cao, ctx);
    } else if (const BinaryOperator* binop = dyn_cast<BinaryOperator>(stmt)) {
      handleBinaryOperator(binop, ctx);
    } else if (const UnaryOperator* unop = dyn_cast<UnaryOperator>(stmt)) {
      if (ctx == BooleanContext) { llvm::outs() << "("; }
      handleUnaryOperator(unop, ctx);
      if (ctx == BooleanContext) { llvm::outs() << " " << mkFosterBinop("!=", exprTy(unop)) << " 0 /*L1932*/)"; }
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
          // Clang's outputString uses octal escapes, but we only support
          // Unicode escape sequences in non-byte-strings.
          StringRef data = lit->getString();
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
                  llvm::outs() << llvm::format("\\u{%02x}", c);
                }
                break;
              }
          }
          llvm::outs() << "\\x00";
          llvm::outs() << (useTriple ? "\"\"\"" : "\"");
          llvm::outs() << ")";
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
        std::string litstr = getText(R, *lit);
        if (litstr != "") llvm::outs() << litstr;
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
        llvm::outs() << clit->getValue();
        if (isprint(clit->getValue())) {
          llvm::outs() << " /*'" << llvm::format("%c", clit->getValue()) << "'*/ ";
        } else {
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
      if (isPrimRef(vd) && ctx != AssignmentTarget) {
        llvm::outs() << emitVarName(vd) << "^";
      } else {
        llvm::outs() << emitVarName(vd);
      }

      if (ctx == BooleanContext) { llvm::outs() << " " << mkFosterBinop("!=", exprTy(dr)) << " 0)"; }

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
      if (ctx == BooleanContext) { llvm::outs() << "("; }

      if (tryHandleCallMalloc(ce, nullptr) || tryHandleCallFree(ce)) {
        // done
      } else if (tryHandleCallPrintf(ce) || tryHandleCallMemop(ce)) {
        // done
      } else {
        handleCall(ce);
      }

      if (ctx == BooleanContext) { llvm::outs() << " " << mkFosterBinop("!=", exprTy(ce)) << " 0)"; }
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
        std::string eltTyName = "";
        if (ile->getNumInits() > 0) { eltTyName = tyName(exprTy(ile->getInit(0))); }
        else if (ile->hasArrayFiller()) { eltTyName = tyName(exprTy(ile->getArrayFiller())); }
        else { // TODO constant array element type?
        }

        llvm::outs() << "(strLit:[" << eltTyName << "] (prim mach-array-literal";
        for (unsigned i = 0; i < ile->getNumInits(); ++i) {
          llvm::outs() << " ";
          visitStmt(ile->getInit(i));
        }
        // Explicitly add any array values that Clang left implicit/uninitialized.
        // TODO for large arrays that are incompletely initialized, we should
        // emit code to set individual slots and rely on the runtime's
        // zero-initialization for the rest.
        const Type* ty = ile->getType().getTypePtr();
        if (auto cat = dyn_cast<ConstantArrayType>(ty)) {
          uint64_t sz = cat->getSize().getZExtValue();
          auto zeroval = zeroValue(cat->getElementType().getTypePtr());
          for (unsigned i = ile->getNumInits(); i < sz; ++i) {
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
            llvm::outs() << ";/*clast*/\n";
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
        llvm::outs() << getText(R, *stmt) << "\n";
      }
    } else if (!stmt) {
      llvm::outs() << "/*null stmt??*/";
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
    name = fosterizedTypeName(name);

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
    
    // Emit field getters
    for (auto d : rd->decls()) {
      if (const FieldDecl* fd = dyn_cast<FieldDecl>(d)) {
        std::string fieldName = fosterizedName(fd->getName());
        llvm::outs() << name << "_" << fieldName << " = { sv : " << name << " => case sv of $" << name;
        for (auto d2 : rd->decls()) {
          if (const FieldDecl* fd2 = dyn_cast<FieldDecl>(d2)) {
            if (fd2 == fd) {
              llvm::outs() << " " << fieldName;
            } else {
              llvm::outs() << " _";
            }
          }
        }
        llvm::outs() << " -> getField " << fieldName << " end };\n";
      }
    }

    // Emit field setters
    for (auto d : rd->decls()) {
      if (const FieldDecl* fd = dyn_cast<FieldDecl>(d)) {
        std::string fieldName = fosterizedName(fd->getName());
        llvm::outs() << "set_" << name << "_" << fieldName
          << " = { sv : " << name << " => v : " << tyName(fd->getType().getTypePtr())
          << " => case sv of $" << name;
        for (auto d2 : rd->decls()) {
          if (const FieldDecl* fd2 = dyn_cast<FieldDecl>(d2)) {
            if (fd2 == fd) {
              llvm::outs() << " " << fieldName;
            } else {
              llvm::outs() << " _";
            }
          }
        }
        llvm::outs() << " -> setField " << fieldName << " v end };\n";
      }
    }
  }

  bool isFromMainFile(const SourceLocation loc) {
    return R.getSourceMgr().isWrittenInMainFile(loc);
  }

  bool isFromMainFile(const Decl* d) { return isFromMainFile(d->getLocation()); }

  bool isFromSystemHeader(const Decl* d) {
    return R.getSourceMgr().isInSystemHeader(d->getLocation());
  }

  const ReturnStmt* getTailReturnOrNull(const Stmt* s) {
    const Stmt* rv = lastStmtWithin(s);
    return rv ? dyn_cast<ReturnStmt>(rv) : NULL;
  }

  void performFunctionLocalAnalysis(FunctionDecl* d, bool& needsCFG) {
    std::map<const Stmt*, bool> innocuousReturns;
    innocuousReturns[getTailReturnOrNull(d->getBody())] = true;

    if (const IfStmt* ifs = dyn_cast<IfStmt>(lastStmtWithin(d->getBody()))) {
      innocuousReturns[getTailReturnOrNull(ifs->getThen())] = true;
      innocuousReturns[getTailReturnOrNull(ifs->getElse())] = true;
    }

    FnBodyVisitor v(mutableLocals, innocuousReturns,
                    voidPtrCasts, needsCFG, d->getASTContext());
    v.TraverseDecl(d);
  }

  bool isPrimRef(const ValueDecl* d) {
    return mutableLocals[d->getName()] || mutableLocalAliases[d->getName()];
  }

  void handleSingleTopLevelDecl(Decl* decl) {
    if (RecordDecl* rdo = dyn_cast<RecordDecl>(decl)) {
      if (!rdo->isThisDeclarationADefinition()) return;
      if (RecordDecl* rd = rdo->getDefinition()) {
        if (rd->isEnum()) {
          llvm::outs() << "// TODO: translate enum definitions\n";
          return;
        }
        if (!(rd->isClass() || rd->isStruct())) {
          return;
        }

        handleRecordDecl(rd);
      }
    } else if (FunctionDecl* fd = dyn_cast<FunctionDecl>(decl)) {
      if (Stmt* body = fd->getBody()) {
        bool needsCFG = false;
        performFunctionLocalAnalysis(fd, needsCFG);

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

        // Rebind parameters if they are observed to be mutable locals.
        for (unsigned i = 0; i < fd->getNumParams(); ++i) {
          ParmVarDecl* d = fd->getParamDecl(i);
          if (mutableLocals[d->getName()]) {
            llvm::outs() << fosterizedName(d->getDeclName().getAsString())
                          << " = (prim ref "
                          << fosterizedName(d->getDeclName().getAsString())
                          << ");\n";
          }
        }

        if (needsCFG) {
          visitStmtCFG(body);
        } else {
          visitStmt(body);
        }
        llvm::outs() << "};\n";
      }
    } else if (TypedefDecl* fd = dyn_cast<TypedefDecl>(decl)) {
      llvm::outs() << "/* " << getText(R, *fd) << ";*/\n";
    } else if (VarDecl* vd = dyn_cast<VarDecl>(decl)) {
      llvm::outs() << "/* Unhandled global variable declaration:\n" << getText(R, *vd) << ";*/\n";
    } else if (auto ed = dyn_cast<EnumDecl>(decl)) {
      for (auto e : ed->enumerators()) {
        enumDeclsForConstants[e] = ed;
        llvm::outs() << enumConstantAccessor(ed, e)
                      << " = { " << e->getInitVal().getSExtValue()
                      << " };\n";
      }
    } else {
      llvm::errs() << "unhandled top-level decl\n";
      decl->dump();
    }
  }

  bool HandleTopLevelDecl(DeclGroupRef DR) override {
    for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b) {
      mutableLocals.clear();
      mutableLocalAliases.clear();
      voidPtrCasts.clear();

      emitCommentsFromBefore((*b)->getLocStart());
      if (!isFromMainFile(*b)) {
        if (!isFromSystemHeader(*b)) {
          if (auto td = dyn_cast<TagDecl>(*b)) {
            if (td->isThisDeclarationADefinition() && td->isCompleteDefinition()) {
              handleSingleTopLevelDecl(*b);
            }
          }
        }
        // skip it if incomplete or from system header
      } else {
        handleSingleTopLevelDecl(*b);
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
  std::map<std::string, bool> mutableLocals;
  std::map<std::string, bool> mutableLocalAliases;
  VoidPtrCasts voidPtrCasts;
  Rewriter R;
  ASTContext* Ctx;

  llvm::DenseMap<const ValueDecl*, int> duplicateVarDecls;

  llvm::DenseMap<const EnumConstantDecl*, const EnumDecl*> enumDeclsForConstants;

  const Stmt* currStmt; // print this one, even if it's in the map.
  typedef llvm::DenseMap<const Stmt*,std::pair<unsigned,unsigned> > StmtMapTy;
  StmtMapTy StmtMap;

  llvm::DenseMap<const Stmt*, BinaryOperatorKind> tweakedStmts;
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
//   * Need to think more about how to expose libm functions and macros.
//     Even a trivial-ish macro (HUGE_VAL) raises questions.
//   * Unions...
//   * Embedded anonymous structs are not well-handled yet,
//     on either the creation/representation or accessor sides.
//
//   * Struct fields not yet properly translated.
//     A field of type T can be translated to any one of:
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
// Other notes:
//   * If the input program defines two types differing only in the case
//     of the first letter (e.g. 'foo' and 'Foo'),
//     we won't properly distinguish the two (both become Foo).
