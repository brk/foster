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

type RhoIL = TypeIL
data TypeIL =
           DataTypeIL     String
         | PrimIntIL      IntSizeBits
         | TupleTypeIL     [TypeIL]
         | FnTypeIL        { fnTypeILDomain :: TypeIL
                           , fnTypeILRange  :: TypeIL
                           , fnTypeILCallConv :: CallConv
                           , fnTypeILProcOrFunc :: ProcOrFunc }
         | CoroTypeIL      TypeIL  TypeIL
         | ForAllIL        [(TyVar, Kind)] RhoIL
         | TyVarIL         TyVar
         | ArrayTypeIL     TypeIL
         | PtrTypeIL       TypeIL

type AIVar = TypedId TypeIL
type ILPrim = FosterPrim TypeIL

instance Show TypeIL where
    show x = case x of
        (DataTypeIL name)   -> name
        (PrimIntIL size)    -> "(PrimIntIL " ++ show size ++ ")"
        (TupleTypeIL types) -> "(" ++ joinWith ", " [show t | t <- types] ++ ")"
        (FnTypeIL   s t cc cs)-> "(" ++ show s ++ " =" ++ briefCC cc ++ "> " ++ show t ++ " @{" ++ show cs ++ "})"
        (CoroTypeIL s t)   -> "(Coro " ++ show s ++ " " ++ show t ++ ")"
        (ForAllIL ktvs rho) -> "(ForAll " ++ show ktvs ++ ". " ++ show rho ++ ")"
        (TyVarIL tv)       -> show tv
        (ArrayTypeIL ty)   -> "(Array " ++ show ty ++ ")"
        (PtrTypeIL ty)     -> "(Ptr " ++ show ty ++ ")"

ilOf :: TypeAST -> Tc TypeIL
ilOf typ =
  case typ of
     (DataTypeAST name)   -> do return $ (DataTypeIL name)
     (PrimIntAST size)    -> do return $ (PrimIntIL size)
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
                                let ktvs = [(tv, KindAnyType) | tv <- tvs]
                                return $ (ForAllIL ktvs t)
     (TyVarAST tv)         -> return $ (TyVarIL tv)
     (MetaTyVar (Meta u tyref desc)) -> do
        mty <- readTcRef tyref
        case mty of
          Nothing -> tcFails [out $ "Found un-unified unification variable "
                                  ++ show u ++ "(" ++ desc ++ ")!"]
          Just t  -> ilOf t

-----------------------------------------------------------------------

boolTypeIL = PrimIntIL I1

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

data AllocMemRegion = MemRegionStack
                    | MemRegionGlobalHeap deriving Show
data ILAllocInfo = ILAllocInfo { ilAllocType   :: TypeIL
                               , ilAllocRegion :: AllocMemRegion
                               , ilAllocArraySize :: (Maybe AIVar)
                               , ilAllocUnboxed :: Bool
                               } deriving Show
