module Foster.Kind where

data Kind = KindAnySizeType
          | KindPointerSized
          | KindEffect
          deriving (Eq, Show, Ord)

class Kinded ty where
  kindOf :: ty -> Kind

KindPointerSized `subkindOf` KindPointerSized = True
KindPointerSized `subkindOf` KindAnySizeType  = True
KindAnySizeType  `subkindOf` KindAnySizeType  = True
KindAnySizeType  `subkindOf` KindPointerSized = False
KindEffect       `subkindOf` KindEffect       = True
_ `subkindOf` _ = False
