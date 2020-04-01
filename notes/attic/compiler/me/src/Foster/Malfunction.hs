module Foster.Malfunction where

import qualified Data.Text as T
import Text.PrettyPrint.ANSI.Leijen

import Foster.Base
import Foster.KNUtil


data MalMod =
     MalMod  [MalBind] [MalExport]

type MalExport = String

data MalSexp =
   MalAtom  String
 | MalVar   String
 | MalBytes String
 | MalSexp  [MalSexp]

data MalBind =
    MalBind String   MalSexp
  | MalEval          MalSexp
  | MalRec [String] [MalSexp]

data MalInt =
    MalInt     Int
  | MalInt32   Integer
  | MalInt64   Integer
  | MalInteger Integer

data MalBlock = MalBlock Int [MalSexp]

data MalSwitch = MalSwitch MalSexp [MalBranch]

data MalBranch = MalBranch [MalSel] MalSexp

data MalSel =
    MalSelInt Int
  | MalSelRange Int Int
  | MalSelAnyInt
  | MalSelTag Int
  | MalSelAnyTag

convertToMalfunction :: ModuleIL KNExpr TypeIL -> MalMod
convertToMalfunction (ModuleIL body _decls datatypes _primtypes _effects _srclines)
    = MalMod [MalEval (kn body)] []

renderMalfunction :: MalMod -> Doc
renderMalfunction m = pretty m

psexp :: [MalSexp] -> Doc
psexp exps = parens $ sep (map pretty exps)

instance Pretty MalMod where
    pretty (MalMod binds exports) = psexp $ [MalAtom "module"]
                                            ++ map sexpBind binds
                                            ++ [MalSexp $ [MalAtom "export"]
                                                        ++ map MalVar exports]

sexpBind :: MalBind -> MalSexp
sexpBind (MalBind x s) = MalSexp [MalVar x, s]
sexpBind (MalEval s) =   MalSexp [MalAtom "_", s]
sexpBind (MalRec xs ss) = MalSexp $ [MalAtom "rec"] ++ map (sexpBind . uncurry MalBind) (zip xs ss)

instance Pretty MalSexp where
    pretty (MalAtom s) = text s
    pretty (MalVar  s) = text "$" <> text s
    pretty (MalBytes s) = dquotes $ text s
    pretty (MalSexp ss) = psexp ss

bind x s = MalSexp [MalVar x, s]

instance Pretty MalBind where
    pretty (MalBind x s) = psexp [MalVar   x,  s]
    pretty (MalEval   s) = psexp [MalAtom "_", s]
    pretty (MalRec xs ss) = psexp $ [MalAtom "rec"] ++ (map (uncurry bind) $ zip xs ss)

instance Pretty MalInt where
    pretty (MalInt x)     = pretty x
    pretty (MalInt32 x)   = pretty x <> text ".i32"
    pretty (MalInt64 x)   = pretty x <> text ".i64"
    pretty (MalInteger x) = pretty x <> text ".ibig"

malInt :: Int -> MalSexp
malInt x = MalAtom (show x)

instance Pretty MalBlock where
    pretty (MalBlock tag exps) = psexp $ malBlock' tag exps

instance Pretty MalSwitch where
    pretty (MalSwitch e branches) = psexp $ [MalAtom "switch", e] ++ map branch branches

branch :: MalBranch -> MalSexp
branch (MalBranch sels e) = malBranch sels e

malBranch sels e = MalSexp $ map sel sels ++ [e]
malSwitch e branches = MalSexp $ [MalAtom "switch", e] ++ map branch branches
malBlock' tag exps = [MalAtom "block", MalSexp [MalAtom "tag", malInt tag]] ++ exps
malBlock  tag exps = MalSexp $ malBlock' tag exps

reprTag (CR_Default x) = x
reprTag (CR_Nullary x) = x -- TODO this ignores nullary encoding optimization
reprTag (CR_Tagged  x) = x
reprTag (CR_Value _) = error $ "malfunction: can't get a tag for CR_Value"
reprTag (CR_Transparent) = error $ "malfunction: no tag for CR_Transparent"
reprTag (CR_TransparentU) = error $ "malfunction: no tag for CR_TransparentU"

sel :: MalSel -> MalSexp
sel (MalSelInt x) = malInt x
sel (MalSelRange x y) = MalSexp [malInt x, malInt y]
sel (MalSelAnyInt) = MalAtom "_"
sel (MalSelTag x) = MalSexp [MalAtom "tag", malInt x]
sel (MalSelAnyTag) = MalSexp [MalAtom "tag", MalAtom "_"]

tid :: TypedId ty -> MalSexp
tid (TypedId _ id) = MalVar (show id)

kn :: KNExpr -> MalSexp
kn (KNLiteral _ (LitInt li)) = malInt (fromIntegral $ litIntValue li)
kn (KNLiteral _ (LitBool b)) = malInt (if b then 1 else 0)
kn (KNLiteral _ (LitFloat _)) = error $ "malfunction: literal float??"
kn (KNLiteral _ (LitByteArray _)) = error $ "malfunction: literal bytes..."
kn (KNLiteral _ (LitText _)) = error $ "malfunction: literal text..."
kn (KNKillProcess _ _ ) = error $ "malfunction: KNKillProcess"
kn (KNTuple _ tids _) = malBlock 0 (map tid tids)
kn (KNIf _ cnd thn els) =
    malSwitch (tid cnd) [MalBranch [MalSelInt 0] (kn els),
                         MalBranch [MalSelAnyInt, MalSelAnyTag] (kn thn)]
kn (KNHandler {}) = error $ "no handler backend for Malfunction"
kn (KNCase _ cnd arms) = error $ "malfunction: KNCase"
kn (KNVar x) = tid x
kn (KNLetVal ident bound body) =
    MalSexp [MalAtom "let", bind (show ident) (kn bound), kn body]
kn (KNLetFuns ids fns body) =
    MalSexp [MalAtom "let",
        (MalSexp $ [MalAtom "rec"] ++ map (uncurry bind)
                                    (zip (map show ids) (map knFn fns))),
        kn body]
kn (KNLetRec ids bounds body) =
    MalSexp [MalAtom "let",
        (MalSexp $ [MalAtom "rec"] ++ map (uncurry bind)
                            (zip (map show ids) (map kn bounds))), kn body]
kn (KNCallPrim _ _ prim xs) = callprim prim xs
kn (KNCall _ callee args) = MalSexp $ [MalAtom "apply"] ++ map tid (callee:args)
kn (KNAppCtor _ (_cid, repr) xs) = malBlock (reprTag repr) (map tid xs)
kn (KNAlloc {}) = error "malfunction: KNAlloc"
kn (KNDeref {}) = error "malfunction: KNDeref"
kn (KNStore {}) = error "malfunction: KNStore"
kn (KNAllocArray {}) = error "malfunction: KNAllocArray"
kn (KNArrayRead {}) = error "malfunction: KNArrayRead"
kn (KNArrayPoke {}) = error "malfunction: KNArrayPoke"
kn (KNArrayLit {}) = error "malfunction: KNArrayLit"
kn (KNTyApp _ x _) = tid x
kn (KNCompiles {}) = error "malfunction: KNCompiles"
kn (KNRelocDoms {}) = error "malfunction: KNRelocDoms"

knFn (Fn _ args body _ _) =
    MalSexp [MalAtom "lambda", MalSexp (map tid args), kn body]

callprim prim xs =
    case prim of
        (PrimOp name _ty) | name `elem` ["==", "-", "+", "*"] ->
            MalSexp $ [MalAtom name] ++ map tid xs
        (PrimOp name _ty) | name == "<s" ->
            MalSexp $ [MalAtom "<"] ++ map tid xs
        (PrimOp name _ty) | name == "<=s" ->
            MalSexp $ [MalAtom "<="] ++ map tid xs
        (PrimOp name _ty) | name == "<u" ->
            MalSexp $ [MalAtom "<"] ++ map tid xs
        (PrimOp name _ty) | name == "<=u" ->
            MalSexp $ [MalAtom "<="] ++ map tid xs
        (NamedPrim (TypedId _ id)) | show id == "expect_i32" ->
            MalSexp $ [MalAtom "apply",
                MalSexp [MalAtom "global", MalVar "Pervasives", MalVar "prerr_int"]] ++ map tid xs
        (NamedPrim (TypedId _ id)) | show id == "print_i32" ->
            MalSexp $ [MalAtom "apply",
                MalSexp [MalAtom "global", MalVar "Pervasives", MalVar "print_int"]] ++ map tid xs
        (NamedPrim (TypedId _ id)) | show id == "opaquely_i32" ->
            tid (head xs)
        (PrimOp name (PrimIntIL I32)) | name == "trunc_i64" ->
            MalSexp $ [MalAtom "convert.i64.i32"] ++ map tid xs
        _ -> error $ "malfunction: KNCallPrim " ++ show prim