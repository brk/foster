{-# LANGUAGE Strict, DeriveGeneric #-}

module Foster.Ident where

import qualified Data.Text as T

type Uniq = Int

identPrefix :: Ident -> T.Text
identPrefix (GlobalSymbol name _) = name
identPrefix (Ident name _)        = name

data Ident = Ident         !T.Text {-# UNPACK #-} !Uniq
            | GlobalSymbol !T.Text !MaybeRename

data MaybeRename = NoRename | RenameTo !T.Text deriving Show

fmapIdent :: (T.Text -> T.Text) -> Ident -> Ident
fmapIdent tt (Ident t u)          = Ident        (tt t) u
fmapIdent tt (GlobalSymbol t alt) = GlobalSymbol (tt t) alt

data TypedId ty = TypedId { tidType :: ty, tidIdent :: Ident }

