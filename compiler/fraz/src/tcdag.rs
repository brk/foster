use hashconsing::{ HConsed, HashConsign, HConsign } ;

type Type = HConsed<Ty>;
type Sigma = Type;
type Rho = Type;
type Tau = Type;
type Effect = Type;

struct CallConv();
struct ProcOrFunc();
struct FnExtra(CallConv, ProcOrFunc);

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
enum Ty {
    Con(String),
    App(Rho, Vec<Sigma>),
    //Rcd(Vec<String>, Vec<Sigma>),
    Tup(Vec<Sigma>),
    Ref(Sigma),
    Arr(Sigma),
    Fun(Vec<Sigma>, Sigma, Effect, FnExtra),
    All(Vec<(TyVar, Kind)>, Rho),
    Tvr(TyVar),
    //Refined(String, Type, Expr),
    MetaPlaceholder(Mtvq, String),
}