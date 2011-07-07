-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.AnnExprIL where

import Foster.Base
import Foster.Context
import Foster.ExprAST
import Foster.TypeIL

{-
  AnnExprIL defines a copy of AnnExpr, annotated
  with TypeIL instead of TypeAST. This lets us
  structurally enforce the restriction that unification
  variables must be eliminated for type checking
  to succeed.
-}

type AIVar = TypedId TypeIL
data AIFn = AiFn { aiFnType  :: TypeIL
                 , aiFnIdent :: Ident
                 , aiFnVars  :: [TypedId TypeIL]
                 , aiFnBody  :: AIExpr
                 , aiFnRange :: ESourceRange
                 } deriving (Show)

aiFnName f = identPrefix (aiFnIdent f)

data AIExpr=
          AIBool       Bool
        | AIInt        TypeIL LiteralInt

        -- No need for an explicit type, so long as subexprs are typed.
        | AITuple      [AIExpr]

        | E_AIFn       AIFn

        -- Add an overall type for the application
        | AICall       ESourceRange TypeIL AIExpr [AIExpr]

        -- Add an overall type for the if branch
        | AIIf         TypeIL AIExpr AIExpr AIExpr
        | AIUntil      TypeIL AIExpr AIExpr

        | AILetVar     Ident AIExpr AIExpr

        -- We have separate syntax for a SCC of recursive functions
        -- because they are compiled differently from non-recursive closures.
        | AILetFuns    [Ident] [AIFn] AIExpr

        | AIAlloc      AIExpr
        | AIDeref      TypeIL AIExpr
        | AIStore      TypeIL AIExpr AIExpr

        -- Subscripts get an overall type
        | AISubscript  TypeIL AIExpr AIExpr

        --Vars go from a Maybe TypeIL to a required TypeIL
        | E_AIVar       (TypedId TypeIL)

        | AIPrimitive   (TypedId TypeIL)

        | E_AITyApp { aiTyAppOverallType :: TypeIL
                    , aiTyAppExpr        :: AIExpr
                    , aiTyAppArgTypes    :: TypeIL }

        | AICase    TypeIL AIExpr [(Pattern, AIExpr)]
        -- This one's a bit odd, in that we can't include an AIExpr
        -- because the subterm doesn't need to be well-typed...
        | AICompiles   CompilesStatus String
        deriving (Show)

ail :: Context TypeIL -> AnnExpr -> Tc AIExpr
ail ctx ae =
    let q = ail ctx in
    case ae of
        AnnBool      b             -> return $ AIBool         b
        AnnCall  r t b args        -> do ti <- ilOf t
                                         (bi:argsi) <- mapM q (b:args)
                                         return $ AICall  r ti bi argsi
        AnnCompiles c msg          -> return $ AICompiles c msg
        AnnIf      t  a b c        -> do ti <- ilOf t
                                         [x,y,z] <- mapM q [a,b,c]
                                         return $ AIIf    ti x y z
        AnnUntil   t  a b          -> do ti <- ilOf t
                                         [x,y]   <- mapM q [a,b]
                                         return $ AIUntil ti x y
        AnnInt     t int           -> do ti <- ilOf t
                                         return $ AIInt ti int
        AnnLetVar id  a b          -> do [x,y]   <- mapM q [a,b]
                                         return $ AILetVar id x y
        AnnLetFuns ids fns e       -> do fnsi <- mapM (aiFnOf ctx) fns
                                         ei <- q e
                                         return $ AILetFuns ids fnsi ei
        AnnAlloc        a          -> do [x] <- mapM q [a]
                                         return $ AIAlloc x
        AnnDeref      t a          -> do ti <- ilOf t
                                         [x] <- mapM q [a]
                                         return $ AIDeref     ti x
        AnnStore      t a b        -> do ti <- ilOf t
                                         [x,y]   <- mapM q [a,b]
                                         return $ AIStore     ti x y
        AnnSubscript  t a b        -> do ti <- ilOf t
                                         [x,y]   <- mapM q [a,b]
                                         return $ AISubscript ti x y
        AnnTuple es                -> do aies <- mapM (ail ctx) es
                                         return $ AITuple aies
        AnnCase t e bs             -> do ti <- ilOf t
                                         ei <- q e
                                         bsi <- mapM (\(p,e) -> do a <- q e
                                                                   return (p, a)) bs
                                         return $ AICase ti ei bsi
        AnnPrimitive (TypedId t i) -> do ti <- ilOf t
                                         return $ AIPrimitive (TypedId ti i)
        E_AnnVar (TypedId t v)     -> do ti <- ilOf t
                                         return $ E_AIVar (TypedId ti v)
        E_AnnFn annFn              -> do aif <- aiFnOf ctx annFn
                                         return $ E_AIFn aif
        E_AnnTyApp t e argty       -> do ti <- ilOf t
                                         at <- ilOf argty
                                         ae <- q e
                                         return $ E_AITyApp ti ae at

aiFnOf :: Context TypeIL -> AnnFn -> Tc AIFn
aiFnOf ctx f = do
 ft <- ilOf (annFnType f)
 fnVars <- mapM (\(TypedId t i) -> do ty <- ilOf t
                                      return $ TypedId ty i) (annFnVars f)
 body <- ail ctx (annFnBody f)
 return $ AiFn { aiFnType  = ft
               , aiFnIdent = annFnIdent f
               , aiFnVars  = fnVars
               , aiFnBody  = body
               , aiFnRange = (annFnRange f)
               }

instance AExpr AIExpr where
    freeIdents e = case e of
        E_AIVar v     -> [tidIdent v]
        AIPrimitive v -> []
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
    textOf e width = error "textOf AIExpr not yet defined"
    childrenOf e =
        case e of
            AIBool         b      -> []
            AICall  r t b args    -> b:args
            AICompiles c msg      -> []
            AIIf      t  a b c    -> [a, b, c]
            AIUntil   t  a b      -> [a, b]
            AIInt t _             -> []
            AILetVar _ a b        -> [a, b]
            AILetFuns ids fns e   -> (map E_AIFn fns) ++ [e]
            AIAlloc        a      -> [a]
            AIDeref      t a      -> [a]
            AIStore      t a b    -> [a, b]
            AISubscript t a b     -> [a, b]
            AITuple     es        -> es
            AICase t e bs         -> e:(map snd bs)
            AIPrimitive  v        -> []
            E_AIVar      v        -> []
            E_AIFn f              -> [aiFnBody f]
            E_AITyApp t a argty   -> [a]

