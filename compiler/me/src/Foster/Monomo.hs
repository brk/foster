-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Monomo (
  monomorphize
)

where

import Control.Monad.State(forM_, execState, get, put, State)

import Foster.Base
import Foster.Kind
import Foster.ILExpr
import Foster.TypeIL
import Foster.Worklist
import Foster.Letable

import Data.Map(Map)
import Data.Map as Map(insert, (!), elems, filter)
import Data.Set(Set)
import Data.Set as Set(member, insert, empty)
import Data.List as List(elem, lookup, all)
import Control.Monad(when)
import Data.Maybe(fromMaybe, isNothing, maybeToList)

-- | Performs worklist-based monomorphization of top-level functions,
-- | roughly as sketched at http://www.bitc-lang.org/docs/bitc/polyinst.html
-- | Limitations:
-- |  * Does not perform tree shaking.
-- |
-- | When we see a type application for a global function symbol,
-- | we apply the tyvar substitution to the referenced proc,
-- | producing a new proc without a forall type and with a new name.
-- | Subsequent type applications with the same type parameters reuse
-- | the cached proc instead of generating a duplicate version.
-- |
-- | After all procs have been generated, we simply filter out those which
-- | still have polymorphic types before returning a new ILProgram.
-- |
-- | Currently different types with the same representation -- such as
-- | (a, b) and (a, b, c), which are both just a pointer at runtime --
-- | will result in different proc definitions, even though they could
-- | share a definition at runtime.

monomorphize :: ILProgram -> ILProgram
monomorphize (ILProgram procdefmap decls datatypes lines) =
        let monoState0 = MonoState Set.empty worklistEmpty procdefmap in
        let monoState  = execState (addMonosAndGo procdefmap) monoState0 in
        let monoProcs  = Map.filter isMono $ monoProcDefs monoState in
        (ILProgram monoProcs decls (monomorphizedDataTypes datatypes) lines)
          where
                addMonosAndGo procdefmap = do
                     addInitialMonoTasksAndGo (Map.elems procdefmap)

isMono procdef = isNothing (ilProcPolyTyVars procdef)
kUnknownPointerType = PtrTypeIL $ PrimIntIL IUnknown

addInitialMonoTasksAndGo procdefs = do
    -- Any proc that is monomorphic when we begin is a root for the
    -- monomorphization process.
    let monoprocs = [pd | pd <- procdefs, isMono pd]
    forM_ monoprocs (\pd -> monoScheduleWork (PlainProc $ ilProcIdent pd))
    goMonomorphize

    -- Any proc that is polymorphic with all pointer-sized type arguments
    -- will have its type arguments conveniently instantiated to void*.

    let isPointyKind (_, kind) = kind == KindPointerSized
    let pointypolyprocs = [(pd,ktvs) | pd <- procdefs,
                                       ktvs <- maybeToList (ilProcPolyTyVars pd),
                                       List.all isPointyKind ktvs]
    forM_ pointypolyprocs (\(pd,ktvs) ->
         let id = ilProcIdent pd in
         monoScheduleWork (NeedsMono id id [kUnknownPointerType | _ <- ktvs])
      )
    goMonomorphize

    -- And similarly for data types with pointer-sized type arguments.
monomorphizedDataTypes :: [DataType TypeIL] -> [DataType TypeIL]
monomorphizedDataTypes dts = map monomorphizedDataType dts
 where monomorphizedDataType (DataType name formals ctors) =
                              DataType name formals ctorsmono where
         ctorsmono = map monomorphizedDataCtor ctors
         monomorphizedDataCtor (DataCtor name tag types) =
                DataCtor name tag [monotype ty | ty <- types]

         -- TODO include kinds on type variables (IL), only subst for boxed kinds
         monotype (TyVarIL _)  = kUnknownPointerType
         monotype ty           = ty

-- TODO we could explicitly represent casts from concrete types to IUnknown*...

--------------------------------------------------------------------

data MonoWork = NeedsMono Ident -- for the eventual monomorphized function
                          Ident -- for the source polymorphic function
                          [TypeIL] -- tyargs for substitution
              | PlainProc Ident
              deriving Show

workTargetId (PlainProc id)     = id
workTargetId (NeedsMono id _ _) = id

data MonoState = MonoState {
    -- Before instantiating a polymorphic function at a given type,
    -- we first check to see if we've already seen it; if so, then
    -- we don't need to add anything to the work list.
    monoSeenIds  :: Set Ident
  , monoWorklist :: WorklistQ MonoWork
  , monoProcDefs :: Map Ident ILProcDef
}

type Mono a = State MonoState a

monoPopWorklist :: Mono (Maybe MonoWork)
monoPopWorklist = do
    state <- get
    case worklistGet $ monoWorklist state of
        Nothing -> return Nothing
        Just (a, rest) -> do put state { monoWorklist = rest }
                             return (Just a)

seen :: MonoWork -> MonoState -> Bool
seen (PlainProc _) _ = False
seen (NeedsMono _ polyid _) state = Set.member polyid (monoSeenIds state)

-- Mark the targetid as seen, and add the source fn and args to the worklist.
monoScheduleWork :: MonoWork -> Mono ()
monoScheduleWork work = do
    state <- get
    when (not $ seen work state) $ do
      put state { monoSeenIds = Set.insert (workTargetId work) (monoSeenIds state)
                , monoWorklist = worklistAdd (monoWorklist state) work
                }

monoGetProc id = do
    state <- get
    return ((monoProcDefs state) Map.! id)

monoPutProc proc = do
    let id = ilProcIdent proc
    state <- get
    put state { monoProcDefs = Map.insert id proc (monoProcDefs state) }

--------------------------------------------------------------------

goMonomorphize :: Mono ()
goMonomorphize = do
  work <- monoPopWorklist
  case work of
    Nothing -> return ()
    Just wk -> monomorphizeProc wk >> goMonomorphize

monomorphizeProc (PlainProc srcid) = do
  proc <- monoGetProc srcid
  doMonomorphizeProc proc

monomorphizeProc (NeedsMono polyid srcid tyargs) = do
  proc_ <- monoGetProc srcid
  let proc = substituteTypeInProc tyargs polyid proc_
  doMonomorphizeProc proc

doMonomorphizeProc :: ILProcDef -> Mono ILProcDef
doMonomorphizeProc proc = do
  blocks <- mapM monomorphizeBlock (ilProcBlocks proc)
  let newproc = proc { ilProcBlocks = blocks  }
  monoPutProc newproc
  return newproc

substituteTypeInProc argtys polyid proc =
 case ilProcPolyTyVars proc of
   Just ktyvars ->
     let tyvarOf (tv, _kind) = tv in
     let subst = Prelude.zip (map tyvarOf ktyvars) argtys in
     -- Return a function without a forall type.
     proc { ilProcPolyTyVars = Nothing
          , ilProcReturnType = parSubstTyIL subst (ilProcReturnType proc)
          , ilProcIdent = polyid
          , ilProcVars = map (substituteTypeInVar subst) (ilProcVars proc)
          , ilProcBlocks = map (substituteTypeInBlock subst) (ilProcBlocks proc)
          }
   Nothing -> error $ "Expected proc to be marked poly " ++ show (ilProcIdent proc)

monomorphizeBlock (Block bid mids last) = do
    newmids <- mapM monomorphizeMid mids
    return $ Block bid newmids last

monomorphizeMid :: ILMiddle -> Mono ILMiddle
monomorphizeMid mid =
  case mid of
    ILLetVal id val -> do valOrVar <- monomorphizeLetable val
                          case valOrVar of
                            Left var -> return $ ILRebindId id var
                            Right val -> return $ ILLetVal id val
    ILClosures ids clos -> do return $ ILClosures ids clos -- TODO
    ILRebindId {}       -> do return mid

monomorphizeLetable expr =
    case expr of
        -- This is the only interesting case!
        ILTyApp t v argty -> do
            let argtys = listize argty
            case v of
              -- If we're polymorphically instantiating a global symbol
              -- (i.e. a proc) then we can statically look up the proc
              -- definition and create a monomorphized copy.
              TypedId (ForAllIL {}) id@(GlobalSymbol _) ->
                do let polyid = getPolyProcId id (show argtys)
                   monoScheduleWork (NeedsMono polyid id argtys)
                   return $ Left (TypedId t polyid)

              -- On the other hand, if we only have a local var, then
              -- (in general) the var is unknown, so we can't statically
              -- monomorphize it. In simple cases we can insert coercions
              -- to/from uniform and non-uniform representations.
              TypedId (ForAllIL ktvs _rho) localvarid ->
                if List.all (\(_tv, kind) -> kind == KindPointerSized) ktvs
                  then return $ Left (TypedId t localvarid)
                  else error $ "Cannot instantiate "
                     ++ show ktvs
                     ++ " with types "
                     ++ show argtys
                     ++ "\nFor now, polymorphic instantiation is only"
                     ++ " allowed on functions at the top level!"
                     ++ "\nThis is a silly restriction for local bindings,"
                     ++ " and could be solved with a dash of flow"
                     ++ " analysis,\nbut the issues are much deeper for"
                     ++ " polymorphic function arguments"
                     ++ " (higher-rank polymorphism)...\n"

              _ -> error $ "Expected polymorphic instantiation to affect a bound variable!"

        -- All other nodes are ignored straightaway.
        _ -> return $ Right expr

-- matching definition from Typecheck.hs
-- does listize (TupleTypeIL []) result in [] or [unit] ?
listize ty =
  case ty of
   TupleTypeIL tys -> tys
   _               -> [ty]

getPolyProcId :: Ident -> String -> Ident
getPolyProcId id s = case id of
                        (GlobalSymbol o) -> (GlobalSymbol (o ++ s))
                        (Ident o m)      -> (Ident (o ++ s) m)

type TyVarSubst = [(TyVar, TypeIL)]

-- Our wanton copying of procs without consistently renaming the copied
-- variables breaks alpha-uniqueness, but it works out at the moment because:
--   1) We don't do any beta-reduction on proc definitions.
--   2) The LLVM lowering uses distinct scopes for each procedure definition.
substituteTypeInVar :: TyVarSubst -> AIVar -> AIVar
substituteTypeInVar subst (TypedId ty id) =
        (TypedId (parSubstTyIL subst ty) id)

substituteTypeInClosure subst (ILClosure id env capts) =
   ILClosure id env (map (substituteTypeInVar subst) capts)

substituteTypeInBlock subst (Block bid mids last) =
    let newmids = map (substituteTypeInMid subst) mids in
    Block bid newmids (substituteTypeInLast subst last)

substituteTypeInMid subst mid =
  case mid of
    ILLetVal id val     -> let newval = substituteTypeInLetable subst val in
                           ILLetVal id newval
    ILClosures ids clos -> let newclos = map (substituteTypeInClosure subst) clos in
                           ILClosures ids newclos
    ILRebindId _ _ -> mid

substituteTypeInLast subst last =
  case last of
        ILRetVoid          -> last
        ILRet   v          -> ILRet (substituteTypeInVar subst v)
        ILBr    _          -> last
        ILIf    t v b1 b2  -> ILIf (parSubstTyIL subst t)
                                   (substituteTypeInVar subst v) b1 b2
        ILCase  t v dt     -> ILCase (parSubstTyIL subst t)
                                     (substituteTypeInVar subst v) dt

substituteTypeInLetable subst expr =
  let q  = parSubstTyIL subst in
  let qv = substituteTypeInVar subst in
  case expr of
      ILBool      b       -> ILBool  b
      ILInt       t i     -> ILInt   (q t) i
      ILTuple       vs    -> ILTuple (map qv vs)
      ILCall      t v vs  -> ILCall     (q t) (qv v) (map qv vs)
      ILCallPrim  t p vs  -> ILCallPrim (q t) p      (map qv vs)
      ILAppCtor   t c vs  -> ILAppCtor  (q t) c      (map qv vs)
      ILAllocate (ILAllocInfo t region arr_var unboxed) ->
          ILAllocate (ILAllocInfo (q t) region  (fmap qv arr_var) unboxed)
      ILAlloc     v       -> ILAlloc            (qv v)
      ILAllocArray t v    -> ILAllocArray (q t) (qv v)
      ILDeref        v    -> ILDeref            (qv v)
      ILStore        v w  -> ILStore            (qv v) (qv w)
      ILArrayRead  t a b  -> ILArrayRead  (q t) (qv a) (qv b)
      ILArrayPoke  v b i  -> ILArrayPoke (qv v) (qv b) (qv i)
      ILTyApp   t v argty -> ILTyApp (q t) (qv v) (q argty)

assocFilterOut :: Eq a => [(a,b)] -> [a] -> [(a,b)]
assocFilterOut lst keys = [(a,b) | (a,b) <- lst, not(List.elem a keys)]

-- Substitute each element of prv with its corresponding element from nxt;
-- unlike tySubst, this replaces arbitrary types with other types.
parSubstTyIL :: TyVarSubst -> TypeIL -> TypeIL
parSubstTyIL prvNextPairs ty =
    let q = parSubstTyIL prvNextPairs in
    case ty of
        TyVarIL tv -> fromMaybe ty $ List.lookup tv prvNextPairs
        -- TODO not sure what the right behavior is for substituting tycons.
        TyConAppIL nm types  -> TyConAppIL nm (map q types)
        PrimIntIL   _        -> ty
        PtrTypeIL   t        -> PtrTypeIL   (q t)
        ArrayTypeIL t        -> ArrayTypeIL (q t)
        TupleTypeIL types    -> TupleTypeIL (map q types)
        FnTypeIL   s t cc cs -> FnTypeIL    (q s) (q t) cc cs
        CoroTypeIL s t       -> CoroTypeIL  (q s) (q t)
        ForAllIL ktvs rho     ->
                let prvNextPairs' = prvNextPairs `assocFilterOut`
                                                      [tv | (tv, _kind) <- ktvs]
                in  ForAllIL ktvs (parSubstTyIL prvNextPairs' rho)

