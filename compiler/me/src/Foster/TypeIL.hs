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
import Foster.Output(out)

type RhoIL = TypeIL
data TypeIL =
           PrimIntIL       IntSizeBits
         | PrimFloat64IL
         | TyConAppIL      DataTypeName [TypeIL]
         | TupleTypeIL     [TypeIL]
         | FnTypeIL        { fnTypeILDomain :: TypeIL
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

kindOfTypeIL :: TypeIL -> Kind
kindOfTypeIL x = case x of
    PrimIntIL   {}       -> KindAnySizeType
    PrimFloat64IL        -> KindAnySizeType
    TyVarIL   _ kind     -> kind
    TyConAppIL  {}       -> KindPointerSized
    TupleTypeIL {}       -> KindPointerSized
    FnTypeIL    {}       -> KindPointerSized
    CoroTypeIL  {}       -> KindPointerSized
    ForAllIL _ktvs rho   -> kindOfTypeIL rho
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
        TyVarIL     tv _     -> show tv
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
     PrimFloat64         -> do return $ PrimFloat64IL
     TupleTypeAST types  -> do tys <- mapM q types
                               return $ TupleTypeIL tys
     FnTypeAST s t cc cs -> do [x,y] <- mapM q [s,t]
                               return $ FnTypeIL x y cc cs
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
          Nothing -> tcFails [out $ "Unable to find kind of type variable " ++ show typ]
          Just k  -> return $ TyVarIL tv k
     MetaTyVar m -> do
        mty <- readTcMeta m
        case mty of
          Nothing -> tcFails [out $ "Found un-unified unification variable "
                                ++ show (mtvUniq m) ++ "(" ++ mtvDesc m ++ ")!"]
          Just t  -> q t

extendTyCtx ctx ktvs = ctx { contextTypeBindings =
                     ktvs ++ contextTypeBindings ctx }

aiVar ctx (TypedId t i) = do ty <- ilOf ctx t
                             return $ TypedId ty i

-----------------------------------------------------------------------

ilOfPat :: Context t -> Pattern TypeAST -> Tc (Pattern TypeIL)
ilOfPat ctx pat = case pat of
    P_Wildcard  rng ty           -> do ty' <- ilOf ctx ty
                                       return $ P_Wildcard  rng ty'
    P_Variable  rng tid          -> do tid' <- aiVar ctx tid
                                       return $ P_Variable rng tid'
    P_Ctor      rng ty pats ctor -> do pats' <- mapM (ilOfPat ctx) pats
                                       ty' <- ilOf ctx ty
                                       return $ P_Ctor rng ty' pats' ctor
    P_Bool      rng ty bval      -> do ty' <- ilOf ctx ty
                                       return $ P_Bool rng ty' bval
    P_Int       rng ty ival      -> do ty' <- ilOf ctx ty
                                       return $ P_Int  rng ty' ival
    P_Tuple     rng ty pats      -> do pats' <- mapM (ilOfPat ctx) pats
                                       ty' <- ilOf ctx ty
                                       return $ P_Tuple rng ty' pats'

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

data ILDataCtor = ILDataCtor String Int (DataCtor TypeIL) deriving Show

-----------------------------------------------------------------------

instance Structured TypeIL where
    textOf e _width =
        case e of
            TyConAppIL nam _types -> out $ "TyConAppIL " ++ nam
            PrimIntIL     size    -> out $ "PrimIntIL " ++ show size
            PrimFloat64IL         -> out $ "PrimFloat64IL"
            TupleTypeIL   {}      -> out $ "TupleTypeIL"
            FnTypeIL      {}      -> out $ "FnTypeIL"
            CoroTypeIL    {}      -> out $ "CoroTypeIL"
            ForAllIL ktvs _rho    -> out $ "ForAllIL " ++ show ktvs
            TyVarIL       {}      -> out $ "TyVarIL "
            ArrayTypeIL   {}      -> out $ "ArrayTypeIL"
            PtrTypeIL     {}      -> out $ "PtrTypeIL"

    childrenOf e =
        case e of
            TyConAppIL _nam types  -> types
            PrimIntIL       {}     -> []
            PrimFloat64IL          -> []
            TupleTypeIL     types  -> types
            FnTypeIL   s t _cc _cs -> [s,t]
            CoroTypeIL s t         -> [s,t]
            ForAllIL  _ktvs rho    -> [rho]
            TyVarIL        _tv _   -> []
            ArrayTypeIL     ty     -> [ty]
            PtrTypeIL       ty     -> [ty]

fnReturnType f@(FnTypeIL {}) = fnTypeILRange f
fnReturnType (ForAllIL _ f@(FnTypeIL {})) = fnTypeILRange f
fnReturnType other = error $
    "Unexpected non-function type in fnReturnType: " ++ show other

