module Foster.Kind where

data Kind = KindAnySizeType
          | KindPointerSized
          deriving (Eq, Show)

data TypeFormalAST = TypeFormalAST String Kind deriving (Show)
