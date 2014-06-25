module Foster.Kind where

data Kind = KindAnySizeType
          | KindPointerSized
          deriving (Eq, Show, Ord)

data TypeFormal = TypeFormal String Kind deriving (Eq, Show, Ord)

class Kinded ty where
  kindOf :: ty -> Kind

instance Kinded TypeFormal where
  kindOf (TypeFormal _ kind) = kind

KindPointerSized `subkindOf` KindPointerSized = True
KindPointerSized `subkindOf` KindAnySizeType  = True
KindAnySizeType  `subkindOf` KindAnySizeType  = True
KindAnySizeType  `subkindOf` KindPointerSized = False
