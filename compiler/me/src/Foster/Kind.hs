module Foster.Kind where

data Kind = KindAnySizeType
          | KindPointerSized
          deriving (Eq, Show)

data TypeFormalAST = TypeFormalAST String Kind deriving (Show)

KindPointerSized `subkindOf` KindPointerSized = True
KindPointerSized `subkindOf` KindAnySizeType  = True
KindAnySizeType  `subkindOf` KindAnySizeType  = True
KindAnySizeType  `subkindOf` KindPointerSized = False
