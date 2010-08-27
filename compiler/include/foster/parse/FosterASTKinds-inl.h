#ifndef FOSTER_AST_KINDS_INL_H
#define FOSTER_AST_KINDS_INL_H

struct TypeVariableAST;
struct VariableAST;
struct ExprAST;

namespace foster {

  class Kind {};
  
  class AtomicKind : public Kind {
    enum Code {
      kValueTypeKind = '*',
      kRegionKind    = '%',
      kEffectKind    = '!',
      kClosureKind   = '$'
    };
    Code code;
    AtomicKind(Code code) : code(code) {}
  public:
    static AtomicKind* getValueTypeKind();
    static AtomicKind* getRegionKind();
    static AtomicKind* getEffectKind();
    static AtomicKind* getClosureKind();
  };
  
  class KindFunction {
    Kind* k1;
    Kind* k2;
    KindFunction(Kind* a, Kind* b) : k1(a), k2(b) {}
  public:
    static KindFunction* get(Kind* a, Kind* b);
  };


  class Effect {};
  
  class ReadEffect : public Effect {
    TypeVariableAST* region;  
  };

  class WriteEffect : public Effect {
    TypeVariableAST* region;  
  };

  class ReadHeadEffect : public Effect {
    TypeVariableAST* region;  
  };
  
  
  class ClosureDatum {
    VariableAST* closedOverVar;
  };
  
  
  class Constraint {};
  
  class EAConstraint {
    Constraint* c;
    ExprAST* source;
  };
  
  class TypeEqualityConstraint : public Constraint {
    TypeAST* a;
    TypeAST* b;
  };
  
  class EffectGreaterThanConstraint : public Constraint {
    TypeVariableAST* a;
    Effect* b;
  };
  
} // namespace foster

#endif
