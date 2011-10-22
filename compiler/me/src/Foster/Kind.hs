module Foster.Kind where

data Kind = KindAnySizeType
          | KindPointerSized
          deriving (Eq, Show)
