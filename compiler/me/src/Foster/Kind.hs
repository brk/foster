module Foster.Kind where

data Kind = KindAnyType
          | KindPointerSized
          deriving (Eq, Show)
