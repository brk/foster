module Foster.Base where

type Uniq = Int

data Ident = Ident { identPrefix :: String
                   , identNum    :: Uniq }

instance Eq Ident where
    (Ident _ n) == (Ident _ m) = n == m

instance Show Ident where
    show i = (identPrefix i) ++ "!" ++ (show $ identNum i)

irrelevantIdentNum = (-12345) :: Int
