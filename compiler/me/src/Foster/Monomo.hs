-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Monomo (monomorphize, monomorphizedDataTypes) where

import Foster.Base
import Foster.Kind
import Foster.ILExpr
import Foster.TypeIL
import Foster.Letable
import Foster.MonoExpr
import Foster.MonoType
import Foster.MonoLetable
import Foster.Worklist

import qualified Data.Text as T

import Data.Map(Map)
import Data.Map as Map(insert, lookup, elems, fromList, union, empty)
import Data.Set(Set)
import Data.Set as Set(member, insert, empty)
import Data.List as List(all)
import Control.Monad(when)
import Control.Monad.State(forM_, execStateT, get, put, StateT, liftIO)
import Data.Maybe(isNothing, maybeToList)

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

monomorphize :: ILProgram -> IO MonoProgram
monomorphize (ILProgram procdefmap decls datatypes topprocs lines) = do
    monoState <- execStateT addMonosAndGo monoState0
    return $ MoProgram (monoProcDefs monoState) monodecls monodatatypes lines
      where
        monodatatypes = monomorphizedDataTypes datatypes
        monoState0 = MonoState Set.empty worklistEmpty procdefmap Map.empty Map.empty
        monodecls  = map monoExternDecl decls
        addMonosAndGo = addInitialMonoTasksAndGo topprocs (Map.elems procdefmap)

-- ||||||||||||||||||||||| Initialization |||||||||||||||||||||||{{{

isNotInstantiable procdef = isNothing (ilProcPolyTyVars procdef)

monoExternDecl :: ILExternDecl -> MoExternDecl
monoExternDecl (ILDecl s t) = MoExternDecl s (monoType emptyMonoSubst t)

addInitialMonoTasksAndGo topprocs procdefs = do
    -- Any proc that is not itself subject to polyinstantiation when we begin
    -- is a root for the monomorphization process.
    -- We start with the top-level procs, because we know that
    -- they can be translated starting from the empty type substitution.
    -- Other procs could be lambda-lifted functions that reference type vars
    -- and thus must use the type subsitution from their originating function.
    let monoprocs = [pd | pd <- topprocs, isNotInstantiable pd]
    debug $ "beginning with monoprocs"
    forM_ monoprocs (\pd -> monoScheduleWork (PlainProc $ ilProcIdent pd))
    goMonomorphize
    debug $ "don with with monoprocs, doing the rest..."

    let monoprocs = [pd | pd <- procdefs, isNotInstantiable pd]
    debug $ "beginning with non-top-level monoprocs"
    forM_ monoprocs (\pd -> monoScheduleWork (PlainProc $ ilProcIdent pd))
    goMonomorphize

    -- Create a "generic" version of *every* polymorphic proc, instantiating all
    -- of the type arguments to void*. Note: We do this even for type variables
    -- with non-pointer kinds! If we didn't, then code like
    --         let f = { forall t:Type, ... }; in () end
    -- wouldn't codegen properly, because the procedure referenced by f's
    -- closure would remain un-instantiated and thus be implicitly discarded.
    let polyprocs = [(pd,ktvs) | pd <- procdefs,
                                 ktvs <- maybeToList (ilProcPolyTyVars pd),
                                 not (isNotInstantiable pd)]
    forM_ polyprocs (\(pd,ktvs) -> do
         let id = ilProcIdent pd
         debug $ "monoScheduleWork " ++ show id ++ " //// " ++ show ktvs
         monoScheduleWork (PlainProc id)
      )
    goMonomorphize

-- And similarly for data types with pointer-sized type arguments.
monomorphizedDataTypes :: [DataType TypeIL] -> [DataType MonoType]
monomorphizedDataTypes dts = map monomorphizedDataType dts
 where monomorphizedDataType :: DataType TypeIL -> DataType MonoType
       monomorphizedDataType (DataType name formals ctors) =
                              DataType name formals ctorsmono where
         ctorsmono = map (monomorphizedDataCtor subst) ctors
         subst = extendSubstForFormals emptyMonoSubst formals

         monomorphizedDataCtor :: MonoSubst -> DataCtor TypeIL -> DataCtor MonoType
         monomorphizedDataCtor subst
               (DataCtor name tag _tyformals types) =
                DataCtor name tag [] (map (monoType subst) types)

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- TODO include kinds on type variables (IL), only subst for boxed kinds

-- ||||||||||||||||| Monomorphic Type Substitution ||||||||||||||{{{

type MonoSubst = Map TyVar MonoType
emptyMonoSubst = Map.empty

extendSubstForFormals subst formals =
  let info (TypeFormalAST s k) =
        case k of KindAnySizeType  -> []
                  KindPointerSized -> [(PtrTypeUnknown, (BoundTyVar s, k))] in
  let (tys, kvs) = unzip $ concatMap info formals in
  extendMonoSubst subst tys kvs

extendMonoSubst :: MonoSubst -> [MonoType] -> [(TyVar, Kind)] -> MonoSubst
extendMonoSubst subst monotypes ktyvars =
  let tyvarOf (tv, _kind) = tv in
  let ext = Prelude.zip (map tyvarOf ktyvars) monotypes in
  Map.union (Map.fromList ext) subst

monoType :: MonoSubst -> TypeIL -> MonoType
monoType subst ty =
  let q = monoType subst in
  case ty of
     TyConAppIL nam types -> TyConApp nam (map q types)
     PrimIntIL size       -> PrimInt size
     PrimFloat64IL        -> PrimFloat64
     TupleTypeIL types    -> TupleType (map q types)
     FnTypeIL  ss t cc cs -> FnType    (map q ss) (q t) cc cs
     CoroTypeIL s t       -> CoroType (q s) (q t)
     ArrayTypeIL ty       -> ArrayType (q ty)
     PtrTypeIL ty         -> PtrType   (q ty)
     -- Type checking should prevent us from trying to instantiate a Boxed
     -- variable with anything but a boxed type.
     ForAllIL ktvs rho    -> monoType (extendMonoSubst subst
                                        [PtrTypeUnknown | _ <- ktvs]
                                                        ktvs) rho
     TyVarIL tv _kind     -> monoSubstLookup subst tv -- TODO check kind?

monoSubstLookup :: MonoSubst -> TyVar -> MonoType
monoSubstLookup _subst (SkolemTyVar  _ _ KindPointerSized) = PtrTypeUnknown
monoSubstLookup _subst (SkolemTyVar  _ _ KindAnySizeType)  =
        --TyConApp ("BAD:SKOLEM TY VAR, ANY SIZE TYPE:"++nm) []
        error $ "Monomorphization (Monomo.hs:monoSubsLookup) "
             ++ "found a bad skolem type variable with non-pointer kind"
monoSubstLookup subst tv@(BoundTyVar nm) =
  case Map.lookup tv subst of
      Just monotype -> monotype
      Nothing -> if True
                  then TyConApp ("AAAAAAmissing:"++nm) []
                  else error $
                         "Monomorphization (Monomo.hs:monoSubsLookup) "
                      ++ "found no monotype for variable " ++ show tv
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||| Monadic Helpers ||||||||||||||||||||||{{{

data MonoWork = NeedsMono Ident -- for the eventual monomorphized function
                          Ident -- for the source polymorphic function
                          [MonoType] -- tyargs for substitution
              | PlainProc Ident
              deriving Show

mkNeedsMono = NeedsMono -- so we can grep for ctor sites but not dtor sites.

workTargetId (PlainProc id)     = id
workTargetId (NeedsMono id _ _) = id

data MonoState = MonoState {
    -- Before instantiating a polymorphic function at a given type,
    -- we first check to see if we've already seen it; if so, then
    -- we don't need to add anything to the work list.
    monoSeenIds  :: Set Ident
  , monoWorklist :: WorklistQ MonoWork
  , polyProcDefs :: Map Ident ILProcDef
  , monoProcDefs :: Map Ident MoProcDef
  , monoCloTyEnv :: Map Ident MonoSubst
}

type Mono = StateT MonoState IO

monoPopWorklist :: Mono (Maybe MonoWork)
monoPopWorklist = do
    state <- get
    case worklistGet $ monoWorklist state of
        Nothing -> return Nothing
        Just (a, rest) -> do put state { monoWorklist = rest }
                             return (Just a)

seen :: MonoWork -> Mono Bool
seen (PlainProc _) = return False
seen (NeedsMono targetid _srcid _) = do
         state <- get ; return $ Set.member targetid (monoSeenIds state)

markSeen :: Ident -> Mono ()
markSeen id = do state <- get
                 put state { monoSeenIds = Set.insert id (monoSeenIds state) }

addWork :: MonoWork -> Mono ()
addWork wk = do state <- get
                put state { monoWorklist = worklistAdd (monoWorklist state) wk }

-- Mark the targetid as seen, and add the source fn and args to the worklist.
monoScheduleWork :: MonoWork -> Mono ()
monoScheduleWork work = do
    seenWork <- seen work
    when (not $ seenWork) $
      do markSeen $ workTargetId work
         addWork  $ work

monoGetProc :: Ident -> Mono (Maybe ILProcDef)
monoGetProc id = do
    state <- get
    return $ Map.lookup id (polyProcDefs state)

monoPutProc :: MoProcDef -> Mono ()
monoPutProc proc = do
    let id = moProcIdent proc
    state <- get
    put state { monoProcDefs = Map.insert id proc (monoProcDefs state) }

monoAssociateSubstWithProcId subst id = do
    state <- get
    debug $ "assocating subst with proc " ++ show id
    put state { monoCloTyEnv = Map.insert id subst (monoCloTyEnv state) }

monoGetSubstAssociatedWithProcId id = do
    state <- get
    case Map.lookup id (monoCloTyEnv state) of
       Nothing -> return emptyMonoSubst
       Just  s -> return s

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||||||| Drivers ||||||||||||||||||||||||||{{{
goMonomorphize :: Mono ()
goMonomorphize = do
  work <- monoPopWorklist
  case work of
    Nothing -> return ()
    Just wk -> monomorphizeProc wk >> goMonomorphize

debug s = liftIO $ putStrLn s

monomorphizeProc (PlainProc srcid) = do
  (Just proc) <- monoGetProc srcid
  basesubst <- monoGetSubstAssociatedWithProcId srcid
  debug $ "monomorphizeProc PlainProc " ++ show srcid
  let tyvars = case ilProcPolyTyVars proc of
                 Nothing   -> []
                 Just ktvs -> ktvs
  let tyargs = [PtrTypeUnknown | _ <- tyvars]
  let subst = extendMonoSubst basesubst tyargs tyvars
  newproc <- doMonomorphizeProc proc subst
  monoPutProc $ newproc

monomorphizeProc (NeedsMono polyid srcid tyargs) = do
  debug $ "monomorphizeProc NeedsMono " ++ show polyid ++ " <- " ++ show srcid ++ " // " ++ show tyargs
  mproc <- monoGetProc srcid
  proc <- case mproc of
             Just p -> return p
             Nothing -> error $ "Monomo.hs: Could not find proc " ++ show srcid
  basesubst <- monoGetSubstAssociatedWithProcId srcid
  let (Just tyvars) = ilProcPolyTyVars proc
  let subst = extendMonoSubst basesubst tyargs tyvars
  newproc <- doMonomorphizeProc proc subst
  monoPutProc $ newproc { moProcIdent = polyid }

doMonomorphizeProc :: ILProcDef -> MonoSubst -> Mono MoProcDef
doMonomorphizeProc proc subst = do
  blocks <- mapM (monomorphizeBlock subst proc) (ilProcBlocks proc)
  return $ MoProcDef { moProcBlocks     = blocks
                     , moProcIdent      =                       ilProcIdent proc
                     , moProcRange      =                       ilProcRange proc
                     , moProcReturnType = monoType subst $ ilProcReturnType proc
                     , moProcVars       =  map (monoVar subst) $ ilProcVars proc
                     }

monomorphizeBlock :: MonoSubst -> ILProcDef -> ILBlock -> Mono MoBlock
monomorphizeBlock subst proc (Block (bid, phis) mids last) = do
    newmids <- mapM (monomorphizeMid subst) mids
    let newphis = map (monoVar subst) phis
    return $ MoBlock (bid, newphis) newmids (monoLast subst last)
                     (Map.lookup bid $ ilProcBlockPreds proc)
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

monoLast :: MonoSubst -> ILLast -> MoLast
monoLast subst last =
  let qv = monoVar subst in
  case last of
    ILRetVoid          -> MoRetVoid
    ILRet     v        -> MoRet      (qv v)
    ILBr      bid args -> MoBr       bid (map (monoVar subst) args)
    -- Might as well optimize single-case switches to unconditional branches.
    ILCase _ [arm]    Nothing _   -> MoBr      (snd arm) [] -- TODO?
    -- If pattern matching was exhaustive, use one of the cases as a default.
    ILCase v (a:arms) Nothing occ -> MoCase (qv v) arms (Just $ snd a) (monoOcc subst occ)
    ILCase v    arms def occ      -> MoCase (qv v) arms def            (monoOcc subst occ)

monoOcc :: MonoSubst -> Occurrence TypeIL -> Occurrence MonoType
monoOcc subst occ = map (\(n,info) -> (n, monoCtorInfo subst info)) occ

monoCtorInfo subst (CtorInfo cid (DataCtor nm tag tyformals tys)) =
                   (CtorInfo cid (DataCtor nm tag tyformals tys'))
                where tys' = map (monoType subst') tys
                      subst' = extendSubstForFormals subst tyformals

monoVar :: MonoSubst -> TypedId TypeIL -> TypedId MonoType
monoVar subst (TypedId t id) = TypedId (monoType subst t) id

monomorphizeMid :: MonoSubst -> ILMiddle -> Mono MoMiddle
monomorphizeMid subst mid =
  case mid of
    ILLetVal id val -> do valOrVar <- monomorphizeLetable subst val
                          case valOrVar of
                            Instantiated var -> return $ MoRebindId   id (monoVar subst var)
                            Bitcast      var -> return $ MoLetBitcast id (monoVar subst var)
                            MonoLet      val -> return $ MoLetVal     id val
    ILClosures ids clos -> do clos' <- mapM (monoClosure subst) clos
                              return $ MoClosures ids clos'
    ILRebindId i   v    -> do return $ MoRebindId i (monoVar subst v)

monoClosure subst (ILClosure procid envid captures allocsite) = do
  -- We need to associate the current substitution with the closure's procid
  -- so that any currently-in-scope type variables will remain "in scope"
  -- when we switch to the new proc.
  monoAssociateSubstWithProcId subst (tidIdent procid)
  -- We don't know if the rest of the parent proc will instantiate this procid,
  -- or even reference it, but we must schedule it so that we don't accidentally
  -- try to translate a proc nested within it before we can propagate the subst.
  monoScheduleWork (PlainProc (tidIdent procid))
  return $ MoClosure (monoVar subst procid)
                     envid (map (monoVar subst) captures) allocsite

data LetableResult = MonoLet      MonoLetable
                   | Instantiated (TypedId TypeIL)
                   | Bitcast      (TypedId TypeIL)

-- |||||||||||||||| Monomorphization of Letables ||||||||||||||||{{{
monomorphizeLetable :: MonoSubst -> Letable -> Mono LetableResult
monomorphizeLetable subst expr =
    let qt = monoType subst in
    let qv = monoVar subst  in
    case expr of
        -- This is the only interesting case!
        ILTyApp t v argtys -> do
            let monotys = map (generic qt) argtys
            case v of
              -- If we're polymorphically instantiating a global symbol
              -- (i.e. a proc) then we can statically look up the proc
              -- definition and create a monomorphized copy (equally well for
              -- both pointer-sized and types with special calling conventions).
              TypedId (ForAllIL {}) id@(GlobalSymbol _) -> do
                  let polyid = getPolyProcId id monotys
                  monoScheduleWork (mkNeedsMono polyid id monotys)
                  -- We need to bitcast the proc we generate because we're
                  -- sharing similarly-kinded instantiations, but we want for
                  -- the translated return type of id:[T] to be T, not void*.
                  return $ Bitcast (TypedId t polyid)

              -- On the other hand, if we only have a local var, then
              -- (in general) the var is unknown, so we can't statically
              -- monomorphize it. In simple cases we can insert coercions
              -- to/from uniform and non-uniform representations.
              TypedId (ForAllIL ktvs _rho) localvarid ->
                if List.all (\(_tv, kind) -> kind == KindPointerSized) ktvs
                  then return $ Bitcast (TypedId t localvarid)
                  else error $ "Cannot instantiate unknown function's type variables "
                     ++ show ktvs
                     ++ " with types "
                     ++ show argtys
                     ++ "\ngenericized to "
                     ++ show monotys
                     ++ "\nFor now, polymorphic instantiation of non-pointer-sized types"
                     ++ " is only allowed on functions at the top level!"
                     ++ "\nThis is a silly restriction for local bindings,"
                     ++ " and could be solved with a dash of flow"
                     ++ " analysis,\nbut the issues are much deeper for"
                     ++ " polymorphic function arguments"
                     ++ " (higher-rank polymorphism)...\n"

              _ -> error $ "Expected polymorphic instantiation to affect a bound variable!"

        -- All other nodes are (essentially) ignored straightaway.
        ILText      s         -> return $ MonoLet $ MoText   s
        ILBool      b         -> return $ MonoLet $ MoBool   b
        ILInt       t i       -> return $ MonoLet $ MoInt   (qt t) i
        ILFloat     t f       -> return $ MonoLet $ MoFloat (qt t) f
        ILTuple     vs asrc   -> return $ MonoLet $ MoTuple (map qv vs) asrc
        ILKillProcess t m     -> return $ MonoLet $ MoKillProcess (qt t) m
        ILOccurrence v occ    -> return $ MonoLet $ MoOccurrence (qv v) (monoOcc subst occ)
        ILCallPrim  t p vs    -> return $ MonoLet $ MoCallPrim (qt t) monopr (map qv vs) where monopr = monoPrim subst p
        ILCall      t v vs    -> return $ MonoLet $ MoCall     (qt t) (qv v) (map qv vs)
        ILAppCtor   t c vs    -> return $ MonoLet $ MoAppCtor  (qt t) c      (map qv vs)
        -- ILAllocate  alloc     -> return $ MonoLet $ MoAllocate (monoAllocInfo subst alloc)
        ILAlloc     v rgn     -> return $ MonoLet $ MoAlloc (qv v) rgn
        ILDeref     v         -> return $ MonoLet $ MoDeref (qv v)
        ILStore     v1 v2     -> return $ MonoLet $ MoStore (qv v1) (qv v2)
        ILAllocArray t v      -> return $ MonoLet $ MoAllocArray (qt t) (qv v)
        ILArrayRead  t (ArrayIndex v1 v2 rng s)
                              -> return $ MonoLet $ MoArrayRead (qt t) (ArrayIndex (qv v1) (qv v2) rng s)
        ILArrayPoke  (ArrayIndex v1 v2 rng s) v3
                              -> return $ MonoLet $ MoArrayPoke (ArrayIndex (qv v1) (qv v2) rng s) (qv v3)
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

monoPrim :: MonoSubst -> FosterPrim TypeIL -> FosterPrim MonoType
monoPrim subst p =
  case p of
     NamedPrim    v     -> NamedPrim (monoVar subst v)
     PrimOp       n t   -> PrimOp       n (monoType subst t)
     PrimIntTrunc s t   -> PrimIntTrunc s t
     CoroPrim  cp t1 t2 -> CoroPrim  cp (monoType subst t1) (monoType subst t2)

-- monoAllocInfo :: MonoSubst -> AllocInfo TypeIL -> AllocInfo MonoType
-- monoAllocInfo subst (AllocInfo t rgn arraysize) =
--     AllocInfo (monoType subst t) rgn (fmap (monoVar subst) arraysize)

generic :: (TypeIL -> MonoType) -> TypeIL -> MonoType
generic f t = if kindOfTypeIL t == KindPointerSized then PtrTypeUnknown else f t

getPolyProcId :: Ident -> [MonoType] -> Ident
getPolyProcId id tys =
  if List.all (\t -> case t of { PtrTypeUnknown -> True ; _ -> False }) tys
    then id
    else idAppend id (show tys)

idAppend id s = case id of (GlobalSymbol o) -> (GlobalSymbol $ beforeS o)
                           (Ident o m)      -> (Ident (beforeS o) m)
                where beforeS o = o `T.append` T.pack s

-- Our wanton copying of procs without consistently renaming the copied
-- variables breaks alpha-uniqueness, but it works out at the moment because:
--   1) We don't do any beta-reduction on proc definitions.
--   2) The LLVM lowering uses distinct scopes for each procedure definition.
