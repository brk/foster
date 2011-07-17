-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.AnnExprIL where

import Data.Set(Set)
import Data.Set as Set(member)
import Data.Map as Map(lookup)

import Foster.Base
import Foster.Context
import Foster.AnnExpr
import Foster.TypeIL
import Foster.TypeAST(gFosterPrimOpsTable, TypeAST(TupleTypeAST))

{-
  AnnExprIL defines a copy of AnnExpr, annotated
  with TypeIL instead of TypeAST. This lets us
  structurally enforce the restriction that unification
  variables must be eliminated for type checking
  to succeed.
-}

data AIExpr=
        -- Literals
          AIBool       Bool
        | AIInt        TypeIL LiteralInt
        | AITuple      [AIExpr]
        | E_AIFn       AIFn
        -- Control flow
        | AIIf         TypeIL AIExpr AIExpr AIExpr
        | AIUntil      TypeIL AIExpr AIExpr
        -- Creation of bindings
        | AICase       TypeIL AIExpr [(Pattern, AIExpr)]
        | AILetVar     Ident AIExpr AIExpr
        | AILetFuns    [Ident] [AIFn] AIExpr
        -- Use of bindings
        | E_AIVar      VarNamespace (TypedId TypeIL)
        | E_AIPrim     ILPrim
        | AICall       TypeIL AIExpr [AIExpr]
        -- Mutable ref cells
        | AIAlloc      AIExpr
        | AIDeref      TypeIL AIExpr
        | AIStore      TypeIL AIExpr AIExpr
        -- Array operations
        | AIAllocArray TypeIL AIExpr
        | AISubscript  TypeIL AIExpr AIExpr
        -- Terms indexed by types
        | E_AITyApp { aiTyAppOverallType :: TypeIL
                    , aiTyAppExpr        :: AIExpr
                    , aiTyAppArgTypes    :: TypeIL }
        deriving (Show)

data AIFn = AiFn { aiFnType  :: TypeIL
                 , aiFnIdent :: Ident
                 , aiFnVars  :: [TypedId TypeIL]
                 , aiFnBody  :: AIExpr
                 , aiFnRange :: ESourceRange
                 } deriving (Show)

aiFnName f = identPrefix (aiFnIdent f)

type KnownProcNames = Set String

ail :: Context TypeIL -> KnownProcNames -> AnnExpr -> Tc AIExpr
ail ctx knownProcNames ae =
    let q = ail ctx knownProcNames in
    case ae of
        AnnBool _rng b             -> return $ AIBool         b
        AnnCompiles _rng (CompilesResult ooe) -> do
                oox <- tcIntrospect (tcInject ooe q)
                return $ AIBool (isOK oox)
        AnnIf rng  t  a b c        -> do ti <- ilOf t
                                         [x,y,z] <- mapM q [a,b,c]
                                         return $ AIIf    ti x y z
        AnnUntil rng t  a b        -> do ti <- ilOf t
                                         [x,y]   <- mapM q [a,b]
                                         return $ AIUntil ti x y
        AnnInt _rng t int          -> do ti <- ilOf t
                                         return $ AIInt ti int
        AnnLetVar _rng id  a b     -> do [x,y]   <- mapM q [a,b]
                                         return $ AILetVar id x y
        AnnLetFuns _rng ids fns e  -> do fnsi <- mapM (aiFnOf ctx knownProcNames) fns
                                         ei <- q e
                                         return $ AILetFuns ids fnsi ei
        AnnAlloc _rng   a          -> do [x] <- mapM q [a]
                                         return $ AIAlloc x
        AnnDeref _rng t a          -> do ti <- ilOf t
                                         [x] <- mapM q [a]
                                         return $ AIDeref     ti x
        AnnStore _rng t a b        -> do ti <- ilOf t
                                         [x,y]   <- mapM q [a,b]
                                         return $ AIStore     ti x y
        AnnSubscript _rng t a b    -> do ti <- ilOf t
                                         [x,y]   <- mapM q [a,b]
                                         return $ AISubscript ti x y
        AnnTuple tup               -> do aies <- mapM q (childrenOf ae)
                                         return $ AITuple aies
        AnnCase _rng t e bs        -> do ti <- ilOf t
                                         ei <- q e
                                         bsi <- mapM (\(p,e) -> do a <- q e
                                                                   return (p, a)) bs
                                         return $ AICase ti ei bsi
        AnnPrimitive _rng v -> tcFails [out $ "Primitives must be called directly!"
                                          ++ "\n\tFound non-call use of " ++ show v]
        AnnCall r t b (E_AnnTuple _rng args) -> do
            ti <- ilOf t
            argsi <- mapM q args
            case b of
                E_AnnVar _rng _var -> do
                   bi <- q b
                   return $ AICall ti bi argsi

                AnnPrimitive _rng (TypedId pty id) -> do
                   pti <- ilOf pty
                   return $ AICall ti (E_AIPrim $ ilPrimFor pti id) argsi

                E_AnnFn _ -> do
                   bi <- q b
                   return $ AICall ti bi argsi

                E_AnnTyApp _ ot (AnnPrimitive _rng (TypedId _ (GlobalSymbol "allocDArray"))) argty -> do
                    let [arraySize] = argsi
                    aty <- ilOf argty
                    return $ AIAllocArray aty arraySize

                E_AnnTyApp _ ot (AnnPrimitive _rng (TypedId vty id)) appty ->
                   let primName = identPrefix id in
                   case (coroPrimFor primName, appty) of
                     (Just coroPrim, TupleTypeAST [argty, retty]) -> do
                       [aty, rty] <- mapM ilOf [argty, retty]
                       return $ AICall ti (E_AIPrim $ ILCoroPrim coroPrim aty rty) argsi
                     otherwise -> do
                       -- v[types](args) ~~>> let <fresh> = v[types] in <fresh>(args)
                       [vti, oti, appti] <- mapM ilOf [vty, ot, appty]
                       let primVar = TypedId vti id
                       let call = AICall ti (E_AIPrim $ ILNamedPrim primVar) argsi
                       let primName = identPrefix id
                       x <- tcFresh $ "appty_" ++ primName
                       return $ AILetVar x (E_AITyApp oti (E_AIVar VarLocal primVar) appti) call

                -- TODO write test cases for the obvious missing combinations...
                _ -> tcFails [out $ "Unknown base of call: " ++ show b]

        E_AnnVar _rng (TypedId t id)-> do
                ti <- ilOf t
                if isProcType ti || Set.member (identPrefix id) knownProcNames
                  then return $ E_AIVar VarProc  (TypedId ti id)
                  else return $ E_AIVar VarLocal (TypedId ti id)

        E_AnnFn annFn              -> do aif <- aiFnOf ctx knownProcNames annFn
                                         return $ E_AIFn aif
        E_AnnTyApp _rng t e argty  -> do ti <- ilOf t
                                         at <- ilOf argty
                                         ae <- q e
                                         return $ E_AITyApp ti ae at

coroPrimFor "coro_create" = Just $ CoroCreate
coroPrimFor "coro_invoke" = Just $ CoroInvoke
coroPrimFor "coro_yield"  = Just $ CoroYield
coroPrimFor _ = Nothing

isProcType (FnTypeIL _ _ _ FT_Proc) = True
isProcType _ = False

ilPrimFor ti id =
  case Map.lookup (identPrefix id) gFosterPrimOpsTable of
        Just (ty, op) -> op
        Nothing       -> ILNamedPrim (TypedId ti id)

aiFnOf :: Context TypeIL -> KnownProcNames -> AnnFn -> Tc AIFn
aiFnOf ctx procNames f = do
 ft <- ilOf (annFnType f)
 fnVars <- mapM (\(TypedId t i) -> do ty <- ilOf t
                                      return $ TypedId ty i) (annFnVars f)
 body <- ail ctx procNames (annFnBody f)
 return $ AiFn { aiFnType  = ft
               , aiFnIdent = annFnIdent f
               , aiFnVars  = fnVars
               , aiFnBody  = body
               , aiFnRange = (annFnRange f)
               }

instance AExpr AIExpr where
    freeIdents e = case e of
        E_AIVar _ v  -> [tidIdent v]
        AILetVar id a b     -> freeIdents a ++ (freeIdents b `butnot` [id])
        AICase _t e patbnds -> freeIdents e ++ (concatMap patBindingFreeIds patbnds)
        -- Note that all free idents of the bound expr are free in letvar,
        -- but letfuns removes the bound name from that set!
        AILetFuns ids fns e ->
                           concatMap boundvars (zip ids fns) ++ (freeIdents e `butnot` ids) where
                                     boundvars (id, fn) = freeIdents (E_AIFn fn) `butnot` [id]
        E_AIFn f       -> let bodyvars =  freeIdents (aiFnBody f) in
                          let boundvars = map tidIdent (aiFnVars f) in
                          bodyvars `butnot` boundvars
        _               -> concatMap freeIdents (childrenOf e)

instance Expr AIExpr where
    freeVars e = map identPrefix (freeIdents e)

instance Structured AIExpr where
    textOf e width = error "textOf AIExpr not yet implemented"
    childrenOf e =
        case e of
            E_AIPrim p            -> []
            AIBool         b      -> []
            AICall    t b args    -> b:args
            AIIf      t  a b c    -> [a, b, c]
            AIUntil   t  a b      -> [a, b]
            AIInt t _             -> []
            AILetVar _ a b        -> [a, b]
            AILetFuns ids fns e   -> (map E_AIFn fns) ++ [e]
            AIAllocArray t a      -> [a]
            AIAlloc        a      -> [a]
            AIDeref      t a      -> [a]
            AIStore      t a b    -> [a, b]
            AISubscript t a b     -> [a, b]
            AITuple     es        -> es
            AICase t e bs         -> e:(map snd bs)
            E_AIVar _ns  v        -> []
            E_AIFn f              -> [aiFnBody f]
            E_AITyApp t a argty   -> [a]

