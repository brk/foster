-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.TypeIL where

import Foster.Base
import Foster.TypeAST
import Foster.Context

type RhoIL = TypeIL
data TypeIL =
           NamedTypeIL     String
         | TupleTypeIL     [TypeIL]
         | FnTypeIL        { fnTypeILDomain :: TypeIL
                           , fnTypeILRange  :: TypeIL
                           , fnTypeILCallConv :: CallConv
                           , fnTypeILProcOrFunc :: ProcOrFunc }
         | CoroTypeIL      TypeIL  TypeIL
         | ForAllIL        [TyVar] RhoIL
         | TyVarIL         TyVar
         | ArrayTypeIL     TypeIL
         | PtrTypeIL       TypeIL

type AIVar = TypedId TypeIL
type ILPrim = FosterPrim TypeIL

instance Show TypeIL where
    show x = case x of
        (NamedTypeIL s)     -> s
        (TupleTypeIL types) -> "(" ++ joinWith ", " [show t | t <- types] ++ ")"
        (FnTypeIL   s t cc cs)-> "(" ++ show s ++ " =" ++ briefCC cc ++ "> " ++ show t ++ " @{" ++ show cs ++ "})"
        (CoroTypeIL s t)   -> "(Coro " ++ show s ++ " " ++ show t ++ ")"
        (ForAllIL tvs rho) -> "(ForAll " ++ show tvs ++ ". " ++ show rho ++ ")"
        (TyVarIL tv)       -> show tv
        (ArrayTypeIL ty)   -> "(Array " ++ show ty ++ ")"
        (PtrTypeIL ty)     -> "(Ptr " ++ show ty ++ ")"

ilOf :: TypeAST -> Tc TypeIL
ilOf typ =
  case typ of
     (NamedTypeAST s)     -> return $ (NamedTypeIL s)
     (TupleTypeAST types) -> do tys <- mapM ilOf types
                                return $ (TupleTypeIL tys)
     (FnTypeAST s t cc cs)-> do [x,y] <- mapM ilOf [s,t]
                                return $ (FnTypeIL x y cc cs)
     (CoroTypeAST s t)    -> do [x,y] <- mapM ilOf [s,t]
                                return $ (CoroTypeIL x y)
     (RefTypeAST ty)      -> do t <- ilOf ty
                                return $ (PtrTypeIL   t)
     (ArrayTypeAST  ty)   -> do t <- ilOf ty
                                return $ (ArrayTypeIL t)
     (ForAllAST tvs rho)  -> do t <- ilOf rho
                                return $ (ForAllIL tvs t)
     (TyVarAST tv)         -> return $ (TyVarIL tv)
     (MetaTyVar (Meta u tyref desc)) -> do
        mty <- readTcRef tyref
        case mty of
          Nothing -> tcFails [out $ "Found un-unified unification variable "
                                  ++ show u ++ "(" ++ desc ++ ")!"]
          Just t  -> ilOf t

-----------------------------------------------------------------------

boolTypeIL = NamedTypeIL "Bool"

-----------------------------------------------------------------------

fnName f = identPrefix (tidIdent $ fnVar f)

data ILDataCtor = ILDataCtor String Int (DataCtor TypeIL) deriving Show
