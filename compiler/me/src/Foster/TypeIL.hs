-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.TypeIL where

import Foster.Base
import Foster.Kind
import Foster.TypeAST
import Foster.Context

import Text.PrettyPrint.ANSI.Leijen

type RhoIL = TypeIL
data TypeIL =
           PrimIntIL       IntSizeBits
         | PrimFloat64IL
         | TyConAppIL      DataTypeName [TypeIL]
         | TupleTypeIL     [TypeIL]
         | FnTypeIL        { fnTypeILDomain :: [TypeIL]
                           , fnTypeILRange  :: TypeIL
                           , fnTypeILCallConv :: CallConv
                           , fnTypeILProcOrFunc :: ProcOrFunc }
         | CoroTypeIL      TypeIL  TypeIL
         | ForAllIL        [(TyVar, Kind)] RhoIL
         | TyVarIL           TyVar  Kind
         | ArrayTypeIL     TypeIL
         | PtrTypeIL       TypeIL

type AIVar = TypedId TypeIL
type ILPrim = FosterPrim TypeIL

instance Kinded TypeIL where
  kindOf x = case x of
    PrimIntIL   {}       -> KindAnySizeType
    PrimFloat64IL        -> KindAnySizeType
    TyVarIL   _ kind     -> kind
    TyConAppIL  {}       -> KindPointerSized
    TupleTypeIL {}       -> KindPointerSized
    FnTypeIL    {}       -> KindPointerSized
    CoroTypeIL  {}       -> KindPointerSized
    ForAllIL _ktvs rho   -> kindOf rho
    ArrayTypeIL {}       -> KindPointerSized
    PtrTypeIL   {}       -> KindPointerSized

instance Show TypeIL where
    show x = case x of
        TyConAppIL nam types -> "(TyConAppIL " ++ nam
                                      ++ joinWith " " ("":map show types) ++ ")"
        PrimIntIL size       -> "(PrimIntIL " ++ show size ++ ")"
        PrimFloat64IL        -> "(PrimFloat64IL)"
        TupleTypeIL types    -> "(" ++ joinWith ", " [show t | t <- types] ++ ")"
        FnTypeIL   s t cc cs -> "(" ++ show s ++ " =" ++ briefCC cc ++ "> " ++ show t ++ " @{" ++ show cs ++ "})"
        CoroTypeIL s t       -> "(Coro " ++ show s ++ " " ++ show t ++ ")"
        ForAllIL ktvs rho    -> "(ForAll " ++ show ktvs ++ ". " ++ show rho ++ ")"
        TyVarIL     tv kind  -> show tv ++ ":" ++ show kind
        ArrayTypeIL ty       -> "(Array " ++ show ty ++ ")"
        PtrTypeIL   ty       -> "(Ptr " ++ show ty ++ ")"

-- Since datatypes are recursively defined, we must be careful when lifting
-- them. In particular, ilOf (TyConAppAST ...) calls ctxLookupDatatype,
-- and lifts the data type using ilOf, which in turn gets called on the types
-- of the data constructors, which can include TyConApps putting us in a loop!

ilOf :: Context t -> TypeAST -> Tc TypeIL
ilOf ctx typ = do
  let q = ilOf ctx
  case typ of
     TyConAppAST dtname tys -> do iltys <- mapM q tys
                                  return $ TyConAppIL dtname iltys
     PrimIntAST size     -> do return $ PrimIntIL size
     PrimFloat64AST      -> do return $ PrimFloat64IL
     TupleTypeAST types  -> do tys <- mapM q types
                               return $ TupleTypeIL tys
     FnTypeAST ss t cc cs-> do (y:xs) <- mapM q (t:ss)
                               return $ FnTypeIL xs y cc cs
     CoroTypeAST s t     -> do [x,y] <- mapM q [s,t]
                               return $ CoroTypeIL x y
     RefTypeAST ty       -> do t <- q ty
                               return $ PtrTypeIL   t
     ArrayTypeAST  ty    -> do t <- q ty
                               return $ ArrayTypeIL t
     ForAllAST ktvs rho  -> do t <- (ilOf $ extendTyCtx ctx ktvs) rho
                               return $ ForAllIL ktvs t
     TyVarAST tv@(SkolemTyVar _ _ k) -> return $ TyVarIL tv k
     TyVarAST tv@(BoundTyVar _) ->
        case Prelude.lookup tv (contextTypeBindings ctx) of
          Nothing -> tcFails [text "Unable to find kind of type variable " <> pretty typ]
          Just k  -> return $ TyVarIL tv k
     MetaTyVar m -> do
        mty <- readTcMeta m
        case mty of
          Nothing -> if False -- TODO this is dangerous, can violate type correctness
                      then return $ TupleTypeIL []
                      else tcFails [text $ "Found un-unified unification variable "
                                ++ show (mtvUniq m) ++ "(" ++ mtvDesc m ++ ")!"]
          Just t  -> q t

aiVar ctx (TypedId t i) = do ty <- ilOf ctx t
                             return $ TypedId ty i

-----------------------------------------------------------------------

ilOfPatAtom :: Context t -> PatternAtom TypeAST -> Tc (PatternAtom TypeIL)
ilOfPatAtom ctx atom = case atom of
    P_Wildcard  rng ty           -> do ty' <- ilOf ctx ty
                                       return $ P_Wildcard  rng ty'
    P_Variable  rng tid          -> do tid' <- aiVar ctx tid
                                       return $ P_Variable rng tid'
    P_Bool      rng ty bval      -> do ty' <- ilOf ctx ty
                                       return $ P_Bool rng ty' bval
    P_Int       rng ty ival      -> do ty' <- ilOf ctx ty
                                       return $ P_Int  rng ty' ival

ilOfPat :: Context t -> Pattern TypeAST -> Tc (Pattern TypeIL)
ilOfPat ctx pat = case pat of
    P_Atom      atom -> return . P_Atom =<< (ilOfPatAtom ctx atom)
    P_Ctor      rng ty pats ctor -> do pats' <- mapM (ilOfPat ctx) pats
                                       ty' <- ilOf ctx ty
                                       ctor' <- ilOfCtorInfo ctx ctor
                                       return $ P_Ctor rng ty' pats' ctor'
    P_Tuple     rng ty pats      -> do pats' <- mapM (ilOfPat ctx) pats
                                       ty' <- ilOf ctx ty
                                       return $ P_Tuple rng ty' pats'

ilOfCtorInfo :: Context t -> CtorInfo TypeAST -> Tc (CtorInfo TypeIL)
ilOfCtorInfo ctx (CtorInfo id dc) = do
  dc' <- ilOfDataCtor ctx dc
  return $ CtorInfo id dc'

ilOfDataCtor :: Context t -> DataCtor TypeAST -> Tc (DataCtor TypeIL)
ilOfDataCtor ctx (DataCtor nm tyformals tys) = do
  let extctx = extendTyCtx ctx (map convertTyFormal tyformals)
  tys' <- mapM (ilOf extctx) tys
  return $ DataCtor nm tyformals tys'

-----------------------------------------------------------------------

boolTypeIL = PrimIntIL I1
stringTypeIL = TyConAppIL "Text" []

pointedToType t = case t of
    PtrTypeIL y -> y
    _ -> error $ "TypeIL.hs:pointedToType\n"
              ++ "Expected type to be a pointer, but had " ++ show t

pointedToTypeOfVar v = case v of
    TypedId (PtrTypeIL t) _ -> t
    _ -> error $ "TypeIL.hs:pointedToTypeOfVar\n"
              ++ "Expected variable to be a pointer, but had " ++ show v
-----------------------------------------------------------------------

fnName f = identPrefix (tidIdent $ fnVar f)

-----------------------------------------------------------------------

instance Structured TypeIL where
    textOf e _width =
        case e of
            TyConAppIL nam _types -> text $ "TyConAppIL " ++ nam
            PrimIntIL     size    -> text $ "PrimIntIL " ++ show size
            PrimFloat64IL         -> text $ "PrimFloat64IL"
            TupleTypeIL   {}      -> text $ "TupleTypeIL"
            FnTypeIL      {}      -> text $ "FnTypeIL"
            CoroTypeIL    {}      -> text $ "CoroTypeIL"
            ForAllIL ktvs _rho    -> text $ "ForAllIL " ++ show ktvs
            TyVarIL       {}      -> text $ "TyVarIL "
            ArrayTypeIL   {}      -> text $ "ArrayTypeIL"
            PtrTypeIL     {}      -> text $ "PtrTypeIL"

    childrenOf e =
        case e of
            TyConAppIL _nam types  -> types
            PrimIntIL       {}     -> []
            PrimFloat64IL          -> []
            TupleTypeIL     types  -> types
            FnTypeIL  ss t _cc _cs -> ss++[t]
            CoroTypeIL s t         -> [s,t]
            ForAllIL  _ktvs rho    -> [rho]
            TyVarIL        _tv _   -> []
            ArrayTypeIL     ty     -> [ty]
            PtrTypeIL       ty     -> [ty]

fnReturnType f@(FnTypeIL {}) = fnTypeILRange f
fnReturnType (ForAllIL _ f@(FnTypeIL {})) = fnTypeILRange f
fnReturnType other = error $
    "Unexpected non-function type in fnReturnType: " ++ show other

