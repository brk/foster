module Foster.Base where

type Uniq = Int

data Ident = Ident { identPrefix :: String
                   , identNum    :: Uniq }

instance Eq Ident where
    i@(Ident _ _) == j@(Ident _ _) = (show i) == (show j)

instance Show Ident where
    show i = (identPrefix i) ++ "!" ++ (show $ identNum i)

irrelevantIdentNum = (-12345) :: Int
