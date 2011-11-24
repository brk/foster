-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------
module Foster.Typecheck(tcSigma) where

import List(length, zip)
import Control.Monad(liftM, forM_, forM, liftM, liftM2)

import qualified Data.Text as T(Text, pack, unpack)
import qualified Data.Map as Map(lookup)
import qualified Data.Set as Set(toList, fromList)

import Foster.Base
import Foster.TypeAST
import Foster.ExprAST
import Foster.AnnExpr
import Foster.Infer
import Foster.Context
import Foster.TypecheckInt(sanityCheck, typecheckInt)
import Foster.Output(out, outToString, OutputOr(Errors), outCS, runOutput)
import System.Console.ANSI

type ExprT = ExprAST TypeAST

data TCWanted = TCSigma | TCRho deriving Show

-----------------------------------------------------------------------

tcSigma = typecheck TCSigma
tcRho   = typecheck TCRho

typecheck :: TCWanted -> Context Sigma -> ExprAST TypeAST -> Maybe TypeAST -> Tc (AnnExpr Rho)
typecheck want ctx expr maybeExpTy = do
  tcLift $ runOutput $ outCS Green ("typecheck " ++ show want ++ ": ") ++ textOf expr 0 ++ out (" <=? " ++ show maybeExpTy)
  tcLift $ putStrLn ""
  tcWithScope expr $ do
    annexpr <- case expr of
      E_VarAST rng v            -> typecheckVar   want ctx rng (evarName v)
      E_IntAST  rng txt         -> typecheckInt            rng txt        maybeExpTy
      E_BoolAST rng b           -> typecheckBool           rng b          maybeExpTy
      E_CallAST rng base argtup -> typecheckCall       ctx rng base (E_TupleAST argtup) maybeExpTy
      E_TupleAST (TupleAST rng exps)
                                -> typecheckTuple want ctx rng exps       maybeExpTy
      E_IfAST   rng a b c       -> typecheckIf         ctx rng a b c      maybeExpTy
      E_FnAST f                 -> typecheckFn         ctx     f          maybeExpTy
      E_LetRec rng bindings e   -> typecheckLetRec     ctx rng bindings e maybeExpTy
      E_LetAST rng binding  e   -> typecheckLet        ctx rng binding  e maybeExpTy
      E_TyApp  rng e t          -> typecheckTyApp      ctx rng e t        maybeExpTy
      E_Case   rng a branches   -> typecheckCase       ctx rng a branches maybeExpTy
      E_AllocAST rng a          -> typecheckAlloc      ctx rng a          maybeExpTy
      E_StoreAST rng e1 e2      -> typecheckStore      ctx rng e1 e2
      E_DerefAST rng a -> do
        ea <- typecheck want ctx a Nothing -- TODO: match maybeExpTy?
        case typeAST ea of
          RefTypeAST t -> return (AnnDeref rng t ea)
          other        -> tcFails [out $ "Expected deref-ed expr "
                                   ++ "to have ref type, had " ++ show other ++ show rng]
      E_SeqAST rng a b -> do ea <- typecheck want ctx a Nothing --(Just TypeUnitAST)
                             id <- tcFresh ".seq"
                             eb <- typecheck want ctx b maybeExpTy
                             return (AnnLetVar rng id ea eb)
      E_UntilAST rng cond body -> do
              acond <- typecheck want ctx cond (Just fosBoolType)
              abody <- typecheck want ctx body Nothing
              acond' <- subsumedBy acond fosBoolType
                    (Just "E_Until: type of until conditional wasn't boolean")
              return $ AnnUntil rng (TupleTypeAST []) acond' abody

      -- a[b]
      E_ArrayRead rng a b -> do
              ta <- typecheck want ctx a Nothing
              tb <- typecheck want ctx b Nothing
              typecheckArrayRead rng ta (typeAST ta) tb maybeExpTy

      -- a >^ b[c]
      E_ArrayPoke rng a b c -> do
              ta <- typecheck want ctx a Nothing
              tb <- typecheck want ctx b (Just $ ArrayTypeAST (typeAST ta))
              tc <- typecheck want ctx c Nothing
              typecheckArrayPoke rng ta tb (typeAST tb) tc maybeExpTy

      E_CompilesAST rng Nothing ->
              return $ AnnCompiles rng (CompilesResult $
                                                 Errors [out $ "parse error"])
      E_CompilesAST rng (Just e) -> do
              outputOrE <- tcIntrospect (typecheck want ctx e Nothing)
              return $ AnnCompiles rng (CompilesResult outputOrE)

    return annexpr
    {-
    -- If the context provided an expected type,
    -- make sure it unifies with the actual type we computed!
    case maybeExpTy of
        Nothing -> return annexpr
        Just expTy -> do tcLift $ putStrLn ""
                         tcLift $ runOutput $ showStructure annexpr
                         tcLift $ putStrLn ""
                         tcLift $ putStrLn $ show want ++ " Checking return type " ++ show expTy ++" with subsumedBy..."
                         subsumedBy annexpr expTy
                           (Just $ outToString (textOf expr 0)
                               ++ "\n\t\thas_type: " ++ (show $ typeAST annexpr)
                               ++ "\n\t\texpected: " ++ (show $ expTy)
                               ++ show (rangeOf expr))
   -}
-----------------------------------------------------------------------

typecheckBool rng b maybeExpTy = do
-- {{{
    let ab = AnnBool rng b
    case maybeExpTy of
         Nothing                    -> return ab
         Just  (PrimIntAST I1)      -> return ab
         Just  m@MetaTyVar {}       -> subsumedBy ab m (Just $ "bool literal")
         Just  t -> tcFails [out $ "Unable to check Bool constant in context"
                                ++ " expecting non-Bool type " ++ show t
                                ++ showSourceRange rng]
-- }}}

--  G |- e1 ::: tau
--  G |- e2 ::: Ref tau
--  --------------------
--  G |- e1 >^ e2 ::: ()
typecheckStore ctx rng e1 e2 = do
-- {{{
    u_slot <- newTcUnificationVarTau $ "slot_type"
    u_expr <- newTcUnificationVarTau $ "expr_type"
    a2 <- tcRho ctx e2 (Just $ RefTypeAST u_slot)
    a1 <- tcRho ctx e1 (Just $            u_expr)
    unify           u_slot                    u_expr    (Just "Store expression")
    unify        (typeAST a2) (RefTypeAST (typeAST a1)) (Just "Store expression")
    return (AnnStore rng a1 a2)
-- }}}

typecheckAlloc ctx rng a maybeExpTy = do
    let expTy = case maybeExpTy of Just (RefTypeAST t) -> Just t
                                   Just _              -> Nothing
                                   Nothing             -> Nothing
    ea <- tcRho ctx a expTy
    return (AnnAlloc rng ea)
-----------------------------------------------------------------------

-- Resolve the given name as either a variable or a primitive reference.
typecheckVar TCSigma ctx rng name =
  case termVarLookup name (contextBindings ctx) of
    Just (TypedId sigma id) -> do
         return $ E_AnnVar rng (TypedId sigma id)
    Nothing   ->
      case Map.lookup name (primitiveBindings ctx) of
        Just avar -> return $ AnnPrimitive rng avar
        Nothing   -> do msg <- getStructureContextMessage
                        tcFails [out $ "Unknown variable " ++ T.unpack name
                                 ++ showSourceRange rng
                                 ++ "ctx: "++ show (contextBindings ctx)
                                 ++ "\nhist: " , msg]

typecheckVar TCRho ctx rng name = do typecheckVar TCSigma ctx rng name >>= inst

-----------------------------------------------------------------------

--  G         |- e1 ::: t1
--  G{x:::t1} |- e2 ::: t2
--  ----------------------------
--  G |- let x = e1 in e2 ::: t2
typecheckLet ctx0 rng (TermBinding v e1) e2 mt = do
-- {{{
    sanityCheck (notRecursive boundName e1) errMsg
    id     <- tcFreshT boundName
    a1     <- tcRho ctx0 e1 maybeVarType
    let v   = TypedId (typeAST a1) id
    let ctx = prependContextBindings ctx0 [bindingForVar v]
    a2     <- tcRho ctx  e2 mt
    return (AnnLetVar rng id a1 a2)
  where
    boundName    = evarName v
    maybeVarType = evarMaybeType v
    notRecursive boundName expr =
            not (boundName `elem` freeVars expr && isFnAST expr)
                  where   isFnAST (E_FnAST _) = True
                          isFnAST _           = False
    errMsg = "Recursive bindings should use 'rec', not 'let':"
           ++ highlightFirstLine rng
-- }}}

-----------------------------------------------------------------------

{-
  rec a = body_a;
      b = body_b;
      ...;
   in e end
-}
-- {{{
typecheckLetRec :: Context Sigma -> SourceRange -> [TermBinding TypeAST]
                -> ExprT -> Maybe TypeAST -> Tc (AnnExpr Rho)
typecheckLetRec ctx0 rng bindings e mt = do
    verifyNonOverlappingVariableNames rng "rec" (map termBindingName bindings)
    -- Generate unification variables for the overall type of
    -- each binding.
    unificationVars <- sequence [newTcUnificationVarTau $ T.unpack $
                                  "letrec_" `prependedTo` (evarName v)
                                | (TermBinding v _) <- bindings]
    ids <- sequence [tcFreshT (evarName v) | (TermBinding v _) <- bindings]
    -- Create an extended context for typechecking the bindings
    let ctxBindings = map (uncurry varbind) (zip ids unificationVars)
    let ctx = prependContextBindings ctx0 ctxBindings

    -- Typecheck each binding
    tcbodies <- forM (zip unificationVars bindings) $
       (\(u, TermBinding v b) -> do
           b' <- tcRho ctx b (evarMaybeType v) -- or (Just $ MetaTyVar u)?
           unify u (typeAST b')
                       (Just $ "recursive binding " ++ T.unpack (evarName v))
           return b'
       )

    -- Typecheck the body as well
    e' <- tcRho ctx e mt

    let fns = [f | (E_AnnFn f) <- tcbodies]
    return $ AnnLetFuns rng ids fns e'
-- }}}

varbind id ty = TermVarBinding (identPrefix id) (TypedId ty id)

typecheckCase :: Context Sigma -> SourceRange -> ExprT
              -> [(EPattern TypeAST, ExprT)] -> Maybe TypeAST -> Tc (AnnExpr Rho)
-- {{{
typecheckCase ctx rng scrutinee branches maybeExpTy = do
  -- (A) The expected type applies to the branches,
  -- not to the scrutinee.
  -- (B) Each pattern must check against the scrutinee type.
  -- (C) Each branch must check against the expected type,
  --  as well as successfully unify against the overall type.

  ascrutinee <- tcRho ctx scrutinee Nothing
  u <- newTcUnificationVarTau "case"
  let checkBranch (pat, body) = do
      p <- checkPattern pat
      bindings <- extractPatternBindings ctx p (typeAST ascrutinee)
      verifyNonOverlappingVariableNames rng "case"
                                        [v | (TermVarBinding v _) <- bindings]
      abody <- tcRho (prependContextBindings ctx bindings) body maybeExpTy
      unify u (typeAST abody)
                   (Just $ "Failed to unify all branches of case " ++ show rng)
      return (p, abody)
  abranches <- forM branches checkBranch
  return $ AnnCase rng u ascrutinee abranches
 where
    checkPattern :: EPattern TypeAST -> Tc Pattern
    -- Make sure that each pattern has the proper arity.
    checkPattern p = case p of
      EP_Wildcard r   -> do return $ P_Wildcard r
      EP_Bool r b     -> do return $ P_Bool r b
      EP_Variable r v -> do checkSuspiciousPatternVariable r v
                            id <- tcFreshT (evarName v)
                            return $ P_Variable r id
      EP_Int r str    -> do annint <- typecheckInt r str Nothing
                            return $ P_Int  r (aintLitInt annint)
      EP_Ctor r eps s -> do (CtorInfo cid _) <- getCtorInfoForCtor ctx s
                            sanityCheck (ctorArity cid == List.length eps) $
                              "Incorrect pattern arity: expected " ++
                              (show $ ctorArity cid) ++ " pattern(s), but got "
                              ++ (show $ List.length eps) ++ show r
                            ps <- mapM checkPattern eps
                            return $ P_Ctor r ps cid
      EP_Tuple r eps  -> do ps <- mapM checkPattern eps
                            return $ P_Tuple r ps
    -----------------------------------------------------------------------

    getCtorInfoForCtor :: Context Sigma -> T.Text -> Tc (CtorInfo Sigma)
    getCtorInfoForCtor ctx ctorName = do
      let ctorInfos = contextCtorInfo ctx
      case Map.lookup ctorName ctorInfos of
        Just [info] -> return info
        elsewise -> tcFails [out $ "Typecheck.getCtorInfoForCtor: Too many or"
                                    ++ " too few definitions for $" ++ T.unpack ctorName
                                    ++ "\n\t" ++ show elsewise]

    -----------------------------------------------------------------------

    -- Recursively match a pattern against a type and extract the (typed)
    -- binders introduced by the pattern.
    extractPatternBindings :: Context Sigma -> Pattern -> TypeAST
                           -> Tc [ContextBinding Sigma]
    extractPatternBindings _ctx (P_Wildcard _   ) _  = return []
    extractPatternBindings _ctx (P_Variable _ id) ty = return [varbind id ty]

    -- TODO shouldn't ignore the _ty here -- bug when ctors from different types listed.
    extractPatternBindings ctx (P_Ctor _ pats (CtorId _ ctorName _ _)) _ty = do
      CtorInfo _ (DataCtor _ _ types) <- getCtorInfoForCtor ctx (T.pack ctorName)
      bindings <- sequence [extractPatternBindings ctx p t | (p, t) <- zip pats types]
      return $ concat bindings

    extractPatternBindings ctx (P_Bool r v) ty = do
      _ae <- tcRho ctx (E_BoolAST r v) (Just ty)
      -- literals don't bind anything, but we still need to check
      -- that we do not try matching e.g. a bool against an int.
      return []

    extractPatternBindings _ctx (P_Int r litint) ty = do
      _ae <- tcRho ctx (E_IntAST r (litIntText litint)) (Just ty)
      -- literals don't bind anything, but we still need to check
      -- that we do not try matching e.g. a bool against an int.
      return []

    extractPatternBindings ctx (P_Tuple _rng [p]) ty = extractPatternBindings ctx p ty
    extractPatternBindings ctx (P_Tuple  rng ps)  ty =
       case ty of
         TupleTypeAST ts ->
            (if List.length ps == List.length ts
              then do bindings <- sequence [extractPatternBindings ctx p t | (p, t) <- zip ps ts]
                      return $ concat bindings
              else tcFails [out $ "Cannot match pattern against tuple type"
                                  ++ " of different length."])
         _else  -> tcFails [out $ "Cannot check tuple pattern"
                                  ++ " against non-tuple type " ++ show ty
                                  ++ showSourceRange rng]

    checkSuspiciousPatternVariable rng var =
      if T.unpack (evarName var) `elem` ["true", "false"]
       then tcFails [out $ "Error: this matches a variable, not a boolean constant!"
                      ++ highlightFirstLine rng]
       else return ()
-- }}}

-----------------------------------------------------------------------

typecheckIf ctx rng a b c maybeExpTy = do
    ea <- tcRho ctx a (Just fosBoolType)
    eb <- tcRho ctx b maybeExpTy
    ec <- tcRho ctx c maybeExpTy
    ea' <- subsumedBy ea fosBoolType  (Just "IfAST: type of conditional wasn't boolean")
    eb' <- subsumedBy eb (typeAST ec) (Just "IfAST: types of branches didn't match")
    ec' <- subsumedBy ec (typeAST eb) (Just "IfAST: types of branches didn't match")
    return (AnnIf rng (typeAST eb') ea' eb' ec')

-----------------------------------------------------------------------

listize (TupleTypeAST tys) = tys
listize ty                 = [ty]

tyvarsOf ktyvars = map (\(tv,_k) -> tv) ktyvars

-- G |- e ::: forall a1::k1..an::kn, rho
-- G |- t_n <::: k_n                          (checked later)
-- ------------------------------------------
-- G |- e :[ t1..tn ]  ::: rho{t1..tn/a1..an}

typecheckTyApp ctx rng e mb_t1tn _maybeExpTyTODO = do
-- {{{
    aeSigma <- tcSigma ctx e Nothing
    case (mb_t1tn, typeAST aeSigma) of
      (Nothing  , _           ) -> return aeSigma
      (Just t1tn, ForAllAST {}) -> do instWith rng aeSigma (listize t1tn)
      (_        , MetaTyVar _ ) -> do
        tcFails [out $ "Cannot instantiate unknown type of term:"
                ,out $ highlightFirstLine $ rangeOf aeSigma
                ,out $ "Try adding an explicit type annotation."
                ]
      (_        , othertype   ) -> do
        tcFails [out $ "Cannot apply type args to expression of"
                   ++ " non-ForAll type: " ++ show othertype]
-- }}}

-----------------------------------------------------------------------

-- G |- e1 ::: Array t
-- ---------------------  e2 ::: t2 where t2 is a word-like type
-- G |- e1 [ e2 ]  ::: t
typecheckArrayRead :: SourceRange -> AnnExpr Sigma -> TypeAST -> AnnExpr Sigma -> Maybe TypeAST -> Tc (AnnExpr Rho)
-- {{{
typecheckArrayRead rng _base (TupleTypeAST _) (AnnInt {}) _maybeExpTy =
    tcFails [out $ "ArrayReading tuples is not allowed;"
                ++ " use pattern matching instead!" ++ highlightFirstLine rng]

typecheckArrayRead rng base (ArrayTypeAST t) i@(AnnInt {}) (Just expTy) = do
    unify t expTy (Just "arrayread[int] expected type")
    -- TODO make sure i is not negative or too big
    return (AnnArrayRead rng t base i)

typecheckArrayRead rng base (ArrayTypeAST t) i@(AnnInt {}) Nothing = do
    -- TODO make sure i is not negative or too big
    return (AnnArrayRead rng t base i)

-- base[aiexpr]
typecheckArrayRead rng base (ArrayTypeAST t) aiexpr maybeExpTy = do
    -- TODO check aiexpr type is compatible with Word
    unify t (typeAST aiexpr) (Just "arrayread type")
    case maybeExpTy of
      Nothing -> return ()
      Just expTy -> unify t expTy (Just "arrayread expected type")

    return (AnnArrayRead rng t base aiexpr)

typecheckArrayRead rng _base baseType _index maybeExpTy =
    tcFails [out $ "Unable to arrayread expression of type " ++ show baseType
                ++ " (context expected type " ++ show maybeExpTy ++ ")"
                ++ highlightFirstLine rng]
-- }}}

-----------------------------------------------------------------------

-- G |-  c   ::: t
-- G |- b[e] ::: Array t
-- ---------------------
-- G |- c >^ b[e] ::: ()
typecheckArrayPoke rng c base (ArrayTypeAST t) aiexpr maybeExpTy = do
-- {{{
    -- TODO check aiexpr type is compatible with Word
    unify t (typeAST aiexpr) (Just "arraypoke type")
    case maybeExpTy of
      Nothing -> return ()
      Just expTy -> unify t expTy (Just "arraypoke expected type")

    return (AnnArrayPoke rng t c base aiexpr)

typecheckArrayPoke rng _ _base baseType _index maybeExpTy =
    tcFails [out $ "Unable to arraypoke expression of type " ++ show baseType
                ++ " (context expected type " ++ show maybeExpTy ++ ")"
                ++ highlightFirstLine rng]
-- }}}

-----------------------------------------------------------------------

isRho (ForAllAST _ _) = False
isRho _               = True

tuplizeNE []   = error "Preconditition for tuplizeNE violated!"
tuplizeNE [ty] = ty
tuplizeNE tys  = TupleTypeAST tys

inst :: AnnExpr Sigma -> Tc (AnnExpr Rho)
inst base = do
  -- TODO shallow zonk here
  case typeAST base of
     ForAllAST ktvs _rho -> do
       taus <- genTauUnificationVarsLike ktvs (\n -> "type parameter " ++ vname base n)
       instWith (rangeOf base) base taus
     _rho -> return base

instWith :: SourceRange -> AnnExpr Sigma -> [Tau] -> Tc (AnnExpr Rho)
instWith _          aexpSigma [] = do
        sanityCheck (isRho $ typeAST aexpSigma)
                     "Tried to instantiate a sigma with no types!"
        return aexpSigma
instWith rng aexpSigma taus = do
    -- TODO shallow zonk here
    case typeAST aexpSigma of
        ForAllAST ktvs rho -> do
            sanityCheck (List.length taus == List.length ktvs)
                        ("Arity mismatch in instWith: can't instantiate"
                        ++ show (List.length ktvs) ++ " type variables with "
                        ++ show (List.length taus) ++ " types!")
            let tyvarsAndTys = List.zip (tyvarsOf ktvs) taus
            return $ E_AnnTyApp rng (parSubstTy tyvarsAndTys rho)
                                    aexpSigma (tuplizeNE taus)
        _ -> tcFails [out $ "Precondition violated: instWith expected ForAll type!"]

vname (E_AnnVar _rng av) n = show n ++ " for " ++ T.unpack (identPrefix $ tidIdent av)
vname _                  n = show n

genTauUnificationVarsLike :: [a] -> (Int -> String) -> Tc [TypeAST]
genTauUnificationVarsLike spine namegen = do
  sequence [newTcUnificationVarTau (namegen n) | (_, n) <- zip spine [1..]]

-----------------------------------------------------------------------

showtypes :: [AnnExpr Sigma] -> TypeAST -> String
showtypes args expectedTypes = concatMap showtypes' (zip3 [1..] args expTypes)
  where showtypes' (_n, expr, expty) =
            if show (typeAST expr) == show expty
              then ""
              else
                ("\n\tArg has type " ++ show (typeAST expr)
                        ++ ", expected " ++ show expty ++ ":\n"
                        ++ show (rangeOf expr)
                        ++ concatMap (\(n, a) -> "\narg " ++ show n ++ "\n"
                        ++ outToString (showStructure a)) (zip [0..] args)  ++ "\n")
        expTypes = (case expectedTypes of
                        (TupleTypeAST x) -> x
                        x -> [x]) ++ repeat (TyConAppAST "<unknown>" []) -- hack :(

-- For example,   foo (1, 2)   would produce:
-- eargs   = [1, 2]
-- argtype = (i32, i32)
-- eb       = foo
-- basetype = (?a -> ?b) ((for top level functions))
typecheckCallRho :: AnnTuple Rho -> AnnExpr Rho -> Rho -> SourceRange -> Tc (AnnExpr Rho)
typecheckCallRho argtup eb basetype range =
    case basetype of
         FnTypeAST formaltype restype _cc _cs -> do
           -- Note use of implicit laziness to avoid unnecessary work.
           let errmsg = ("CallAST mismatch between formal & arg types\n"
                          ++ showtypes (annTupleExprs argtup) formaltype)

           (AnnTuple argtup') <- subsumedBy (AnnTuple argtup) formaltype (Just $ errmsg)
           return (AnnCall range restype eb argtup')

         _otherwise -> do
            ebStruct <- tcShowStructure eb
            tcFails $ (out $ "Called value was not a function: "):ebStruct:
                                       [out $ " :: " ++ (show $ typeAST eb)]

-- Typecheck the function first, then the args.
-- Example the interior call to foo in
--           foo = { forall a, x : List a => if isnil x then 0 else 1 + foo nil }
-- results in a call to typecheckCall with expected type Int32,
--   base = foo :: ?foo
-- so the MetaTyVar case is taken, and we proceed to typecheckCallWithBaseFnType
-- using a bare function type...
--
typecheckCall :: Context Sigma -> SourceRange
              -> ExprAST TypeAST -> ExprAST TypeAST
              -> Maybe TypeAST -> Tc (AnnExpr Rho)
typecheckCall ctx rng base args maybeExpTy = do
   tcLift $ runOutput $ (outCS Green "typecheckCallSigma ") ++ out (highlightFirstLine rng)
   tcLift $ putStrLn ""
   -- Act in checking mode, since we don't yet know if we're looking
   -- at a plain function or a forall-quantified type.
   eb <- tcSigma ctx base Nothing
   case typeAST eb of
      fnty@FnTypeAST {} -> do
            AnnTuple eargs <- tcSigma ctx args (Just $ fnTypeDomain fnty)
            typecheckCallRho eargs eb fnty rng

      (ForAllAST ktyvars rho) -> do
         -- eb ::[[??]] ea
         let (FnTypeAST argType retType _ _) = rho
         -- Example:            argtype =   ('a -> 'b)
         -- base has type ForAll ['a 'b]   (('a -> 'b) -> (Coro 'a 'b))
         -- The forall-bound vars won't unify with concrete types in the term arg,
         -- so we replace the forall-bound vars with unification variables
         -- when computing the type of the term argument.

         -- That is, instead of checking the args against ('a -> 'b),
         -- we must use unification variables instead:    (?a -> ?b)
         -- and then extract the types from unification
         -- to use as type arguments.

         -- Generate unification vars                 (?a, ?b)
         -- corresponding to the bound type variables ('a, 'b).
         unificationVars <- genTauUnificationVarsLike ktyvars
                                (\n -> "type parameter " ++ vname eb n)

         let tyvarsAndMetavars = List.zip (tyvarsOf ktyvars) unificationVars

         -- Convert ('a -> 'b) to (?a -> ?b).
         let unifiableArgType = parSubstTy tyvarsAndMetavars argType
         let unifiableRetType = parSubstTy tyvarsAndMetavars retType

         -- Type check the args, unifying them with the expected arg type.
         ea@(AnnTuple eargs) <- tcSigma ctx args (Just $ unifiableArgType)

         -- TODO should this be equateTypes instead of tcUnifyTypes?
         --tcLift $ putStrLn ("unifying: " ++ show unifiableArgType)
         --tcLift $ putStrLn ("   w ith: " ++ show (typeAST ea))
         --tcLift $ putStrLn ("     and: " ++ show unifiableRetType)
         --tcLift $ putStrLn ("   w ith: " ++ show maybeExpTy)
         --tcLift $ putStrLn ""

         unificationResults <- unifyFun unifiableArgType unifiableRetType
                                        (typeAST ea)     maybeExpTy
         case unificationResults of
           Nothing -> tcFails [out $ "Failed to determine type arguments to apply!" ++ show rng]
           Just tysub -> do
             -- Suppose the argument to the call has typeAST ea = (t1 -> t2):
             -- ((?a -> ?b) -> (Coro ?a ?b))
             let unifiableRhoType = parSubstTy tyvarsAndMetavars rho
              -- ((t1 -> t2) -> (Coro t1 t2))
             let substitutedFnType = tySubst tysub unifiableRhoType
             -- eb[tyProjTypes]::substitutedFnType

             --tcLift $ putStrLn ("typeAST eb: " ++ show (typeAST eb))
             --tcLift $ putStrLn ("substitutedFnType: " ++ show substitutedFnType)
             --tcLift $ putStrLn ("_maybeExpTy: " ++ show maybeExpTy)
             --tcLift $ putStrLn ("tysub: " ++ show tysub)

             tyProjTypes <- extractSubstTypes
                               (map (\(MetaTyVar m) -> m) unificationVars) tysub
             --tcLift $ putStrLn ("tcTyProjTypes: " ++ show tyProjTypes)
             let annTyApp = E_AnnTyApp rng substitutedFnType eb (minimalTupleAST tyProjTypes)
             --tcLift $ putStrLn ("annTyApp: " ++ show annTyApp)
             typecheckCallRho eargs annTyApp (typeAST annTyApp) rng

      MetaTyVar m -> do
            tcLift $ putStrLn ("*** typecheckCall ctx rng base args _maybeExpTy: " ++ show maybeExpTy)
            AnnTuple eargs <- tcSigma ctx args Nothing

            rt <- newTcUnificationVarTau   $ "arg type for " ++ mtvDesc m
            ft <- newTcUnificationVarSigma $ "ret type for " ++ mtvDesc m
            -- TODO this should sometimes be proc, not func...
            let fnty = mkFuncTy ft rt

            unify (MetaTyVar m) fnty Nothing
            typecheckCallRho eargs eb fnty rng

      _ -> tcFails [out $ "Called expression had unexpected type: "
                          ++ show (typeAST eb) ++ highlightFirstLine rng]

unifyFun expArg _actRet actArg Nothing       = tcUnifyTypes expArg actArg
unifyFun expArg  actRet actArg (Just expRet) = tcUnifyTypes (TupleTypeAST [expArg, actRet])
                                                            (TupleTypeAST [actArg, expRet])

mkFuncTy a r = FnTypeAST a r FastCC FT_Func
-----------------------------------------------------------------------

-- Functions default to the fast calling convention. {{{
typecheckFn ctx f Nothing =
                typecheckFn' ctx f FastCC Nothing  Nothing

typecheckFn ctx f (Just (FnTypeAST s t cc _cs)) =
                typecheckFn' ctx f     cc (Just s) (Just t)

typecheckFn ctx f (Just m@MetaTyVar {}) = do
                tcf <- typecheckFn ctx f Nothing
                subsumedBy tcf m (Just "function literal")

typecheckFn _ctx f (Just t) = tcFails [out $
                "Context of function literal expects non-function type: "
                                ++ show t ++ highlightFirstLine (fnAstRange f)]

typecheckFn' :: Context Sigma -> FnAST TypeAST -> CallConv
             -> Maybe TypeAST -> Maybe TypeAST -> Tc (AnnExpr Rho)
typecheckFn' ctx f cc expArgType expBodyType = do
    let fnProtoName = T.unpack (fnAstName f)
    uniquelyNamedFormals <- getUniquelyNamedFormals (fnAstRange f)
                                                    (fnFormals f) fnProtoName
    equateArgTypes uniquelyNamedFormals expArgType

    -- Typecheck the body of the function in a suitably extended context.
    extCtx <- extendContext ctx uniquelyNamedFormals expArgType
    annbody <- tcSigma extCtx (fnAstBody f) expBodyType

    -- Make sure the body agrees with the return type annotation (if any).
    case fnRetType f of
       Nothing -> return ()
       Just t  -> unify t (typeAST annbody)
                    (Just $ "return type/body type mismatch in " ++ fnProtoName)

    -- Note we collect free vars in the old context, since we can't possibly
    -- capture the function's arguments from the environment!
    freeVars <- computeFreeFnVars uniquelyNamedFormals annbody f ctx

    let fnty = let argtypes = TupleTypeAST (map tidType uniquelyNamedFormals) in
               fnTypeTemplate f argtypes (typeAST annbody) cc

    -- If we're type checking a top-level function binding, update its type.
    case termVarLookup (T.pack fnProtoName) (contextBindings ctx) of
      Nothing -> return ()
      Just av -> unify fnty (tidType av)
                   (Just $ "overall type of function " ++ fnProtoName)

    return $ E_AnnFn $ Fn (TypedId fnty (GlobalSymbol $ fnAstName f))
                          uniquelyNamedFormals annbody freeVars
                          (fnAstRange f)
  where
    extendContext :: Context Sigma -> [AnnVar] -> Maybe TypeAST -> Tc (Context Sigma)
    extendContext ctx [] Nothing = return ctx
    extendContext ctx protoFormals maybeExpFormalTys = do
        equateArgTypes protoFormals maybeExpFormalTys
        return $ prependContextBindings ctx (map bindingForVar protoFormals)

    -- Generalization of fnTypeTemplate in Main.hs
    fnTypeTemplate f argtypes retty cc =
      -- Compute "base" function type, ignoring any type parameters.
      let procOrFunc = if fnWasToplevel f then FT_Proc else FT_Func in
      let fnty = FnTypeAST argtypes retty cc procOrFunc in
      case fnTyFormals f of
              []        -> fnty
              tyformals -> ForAllAST (map convertTyFormal tyformals) fnty

    computeFreeFnVars uniquelyNamedFormals annbody f ctx = do
        let identsFree = bodyvars `butnot` (boundvars ++ globalvars)
                         where
                         bodyvars   = freeIdents annbody
                         boundvars  = map tidIdent uniquelyNamedFormals
                         globalvars = concatMap tmBindingId (globalBindings ctx)
                         tmBindingId (TermVarBinding _ tid) = [tidIdent tid]
        freeAnns <- let rng = fnAstRange f in
                    mapM (\id -> typecheckVar TCSigma ctx rng (identPrefix id))
                         identsFree
        return $ [tid | E_AnnVar _ tid <- freeAnns]

    -- | Verify that the given formals have distinct names,
    -- | and return unique'd versions of each.
    getUniquelyNamedFormals rng rawFormals fnProtoName = do
        verifyNonOverlappingVariableNames rng fnProtoName
                          (map (identPrefix.tidIdent) rawFormals)
        mapM uniquelyName rawFormals
-- }}}

-----------------------------------------------------------------------

typecheckTuple :: TCWanted -> Context Sigma -> SourceRange -> [ExprT] -> Maybe TypeAST -> Tc (AnnExpr Rho)
-- {{{
typecheckTuple want ctx rng exprs maybeExpectedType =
  case maybeExpectedType of
     Nothing                -> tcTuple ctx rng exprs [Nothing | _ <- exprs]
     Just (TupleTypeAST ts) -> tcTuple ctx rng exprs [Just t  | t <- ts]
     Just m@MetaTyVar {}    -> do
        tctup <-               tcTuple ctx rng exprs [Nothing | _ <- exprs]
        unify m (typeAST tctup) (Just $ highlightFirstLine rng)
        return tctup
     Just ty -> tcFails [out $ "typecheck: tuple (" ++ show exprs ++ ") "
                            ++ "cannot check against non-tuple type " ++ show ty]
  where
    tcTuple ctx rng es ts = do
        exprs <- typecheckExprsTogether ctx es ts
        return $ AnnTuple (E_AnnTuple rng exprs)

    -- Typechecks each expression in the same context
    typecheckExprsTogether ctx exprs expectedTypes = do
        sanityCheck (length exprs == length expectedTypes)
            ("typecheckExprsTogether: had different number of values ("
               ++ (show $ length exprs)
               ++ ") and expected types (" ++ (show $ length expectedTypes)
               ++ ")\nThis might be caused by a missing semicolon!\n"
               ++ show exprs ++ " versus \n" ++ show expectedTypes)
        mapM (\(e,mt) -> typecheck want ctx e mt) (List.zip exprs expectedTypes)
-- }}}

-----------------------------------------------------------------------

uniquelyName :: TypedId t -> Tc (TypedId t)
uniquelyName (TypedId ty id) = do
    uniq <- newTcUniq
    newid <- rename id uniq
    return (TypedId ty newid)
  where
    rename :: Ident -> Uniq -> Tc Ident
    rename (Ident p _) u = return (Ident p u)
    rename (GlobalSymbol name) _u =
            tcFails [out $ "Cannot rename global symbol " ++ show name]

verifyNonOverlappingVariableNames :: SourceRange -> String -> [T.Text] -> Tc ()
verifyNonOverlappingVariableNames rng name varNames = do
    case detectDuplicates varNames of
        []   -> return ()
        dups -> tcFails [out $ "Error when checking " ++ name ++ ": "
                              ++ "had duplicated bindings: " ++ show dups
                              ++ highlightFirstLine rng]

-----------------------------------------------------------------------

zonkType :: TypeAST -> Tc TypeAST
zonkType x = do
    case x of
        MetaTyVar m -> do mty <- readTcMeta m
                          case mty of
                            Nothing -> return x
                            Just ty -> do ty' <- zonkType ty
                                          writeTcMeta m ty'
                                          return ty'
        PrimIntAST {}         -> return x
        TyVarAST   {}         -> return x
        TyConAppAST nm types  -> liftM (TyConAppAST nm) (mapM zonkType types)
        TupleTypeAST types    -> liftM (TupleTypeAST  ) (mapM zonkType types)
        ForAllAST  tvs rho    -> liftM (ForAllAST tvs ) (zonkType rho)
        RefTypeAST    ty      -> liftM (RefTypeAST    ) (zonkType ty)
        ArrayTypeAST  ty      -> liftM (ArrayTypeAST  ) (zonkType ty)
        CoroTypeAST s r       -> liftM2 (CoroTypeAST  ) (zonkType s) (zonkType r)
        FnTypeAST s r cc cs   -> do s' <- zonkType s ; r' <- zonkType r
                                    return $ FnTypeAST s' r' cc cs

skolemize (ForAllAST ktvs rho) = do
                             skolems <- mapM newTcSkolem ktvs
                             let tyvarsAndTys = List.zip (tyvarsOf ktvs)
                                                         (map TyVarAST skolems)
                             return (skolems, parSubstTy tyvarsAndTys rho)
skolemize rho = return ([], rho)

getFreeTyVars :: TypeAST -> Tc [TyVar]
getFreeTyVars x = do z <- zonkType x
                     return $ Set.toList (Set.fromList $ go [] z)
                 where
  go :: [TyVar] -> Sigma -> [TyVar]
  go bound x =
    case x of
        PrimIntAST _          -> []
        TyConAppAST _nm types -> concatMap (go bound) types
        TupleTypeAST types    -> concatMap (go bound) types
        FnTypeAST s r _ _     -> concatMap (go bound) [s,r]
        CoroTypeAST s r       -> concatMap (go bound) [s,r]
        ForAllAST  tvs rho    -> go (tyvarsOf tvs ++ bound) rho
        TyVarAST   tv         -> if tv `elem` bound then [] else [tv]
        MetaTyVar     {}      -> []
        RefTypeAST    ty      -> (go bound) ty
        ArrayTypeAST  ty      -> (go bound) ty

subsumedBy :: AnnExpr Sigma -> Sigma -> Maybe String -> Tc (AnnExpr Rho)
subsumedBy (AnnTuple (E_AnnTuple rng exprs)) (TupleTypeAST tys) msg = do
        exprs' <- mapM (\(e,t) -> subsumedBy e t msg) (zip exprs tys)
        return (AnnTuple (E_AnnTuple rng exprs'))
subsumedBy annexpr st2 msg = do
    t1' <- zonkType (typeAST annexpr)
    tcLift $ runOutput $ outCS Green $ "subsumedBy " ++ show t1' ++ " <=? " ++ show st2
    tcLift $ putStrLn ""
    case (typeAST annexpr, st2) of
        (s1, s2@ForAllAST {}) -> do -- Odersky-Laufer's SKOL rule.
             (skols, r2) <- skolemize s2
             e' <- subsumedBy annexpr r2 msg
             ftvs <- getFreeTyVars s1
             let bad_tvs = filter (`elem` ftvs) skols
             sanityCheck (null bad_tvs) "Type not polymorphic enough!"
             return e'
        (ForAllAST {}, rho2) -> do
                --tcLift $ runOutput $ outCS Red $ "subsumedBy: inst " ++ show annexpr ++ " to rho " ++ show rho2
                --tcLift $ putStrLn ""
                annrho <- inst annexpr
                subsumedBy annrho rho2 msg

        --(rho1@FnTypeAST {}, rho2) -> do (a2, r2) <- unifyFun rho2 ; subsumedByFun a1 r1 a2 r2
        --(rho1, rho2@FnTypeAST {}) -> do (a1, r1) <- unifyFun rho1 ; subsumedByFun a1 r1 a2 r2
        (rho1,            rho2) -> do unify rho1 rho2 msg
                                      return annexpr

-- equateTypes first attempts to unify the two given types.
-- If unification fails, the provided error message (if any)
-- is printed along with the unification failure error message.
-- If unification succeeds, each unification variable in the two
-- types is updated according to the unification solution.
unify :: TypeAST -> TypeAST -> Maybe String -> Tc ()
unify t1 t2 msg = do
  tcLift $ runOutput $ outCS Green $ "unify " ++ show t1 ++ " ?==? " ++ show t2
  tcLift $ putStrLn ""
  tcOnError (liftM out msg) (tcUnifyTypes t1 t2) $ \(Just soln) -> do
     let univars = concatMap collectUnificationVars [t1, t2]
     forM_ univars $ \m -> do
       mt1 <- readTcMeta m
       case (mt1, Map.lookup (mtvUniq m) soln) of
         (_,       Nothing)          -> return () -- no type to update to.
         (Just x1, Just x2)          -> unify x1 x2 msg
         (Nothing, Just (MetaTyVar m2)) -> do
                         mt2 <- readTcMeta m2
                         case mt2 of
                             Just x2 -> unify (MetaTyVar m) x2 msg
                             Nothing -> writeTcMeta m t2
         (Nothing, Just x2) -> case m `elem` collectUnificationVars x2 of
                             False   -> writeTcMeta m x2
                             True    -> occurdCheck m x2
  where
     collectUnificationVars :: TypeAST -> [MetaTyVar]
     collectUnificationVars x =
         case x of
             PrimIntAST _          -> []
             TyConAppAST _nm types -> concatMap collectUnificationVars types
             TupleTypeAST types    -> concatMap collectUnificationVars types
             FnTypeAST s r _ _     -> concatMap collectUnificationVars [s,r]
             CoroTypeAST s r       -> concatMap collectUnificationVars [s,r]
             ForAllAST _tvs rho    -> collectUnificationVars rho
             TyVarAST  _tv         -> []
             MetaTyVar     m       -> [m]
             RefTypeAST    ty      -> collectUnificationVars ty
             ArrayTypeAST  ty      -> collectUnificationVars ty

     occurdCheck m t = tcFails [out $ "Occurs check for " ++ show (MetaTyVar m)
                                   ++ " failed in " ++ show t]

bindingForVar v = TermVarBinding (identPrefix $ tidIdent v) v

-- Unify the types of the variables with the types expected of them.
equateArgTypes :: [AnnVar] -> (Maybe TypeAST) -> Tc ()
equateArgTypes _     Nothing              = return ()
equateArgTypes []   (Just u@MetaTyVar {}) = unify u (TupleTypeAST []) Nothing
equateArgTypes vars (Just (TupleTypeAST expTys)) = do
  sanityCheck (List.length vars == List.length expTys)
   ("Lengths of tuples must agree! Had " ++ show vars ++ " and " ++ show expTys)
  sequence_ [unify (tidType v) e Nothing | (v, e) <- List.zip vars expTys]
equateArgTypes vars (Just t) =
    tcFails [out $ "unifyArgs not yet implemented for type "
                 ++ show t ++ " against " ++ show vars]

