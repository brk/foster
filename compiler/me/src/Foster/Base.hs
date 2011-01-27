module Foster.Base where

import System.Console.ANSI
import Control.Monad

data Outputs = Outputs [SGR] String
type Output = [Outputs]

out :: String -> Output
out s = [(Outputs ([] :: [SGR]) s)]

outLn s = out (s ++ "\n")

outCS :: Color -> String -> Output
outCS c s = [Outputs [SetColor Foreground Dull c] s]

outCSLn c s = outCS c (s ++ "\n")

runOutput :: Output -> IO ()
runOutput outs = do
    forM_ outs $ (\(Outputs sgrs str) -> do
                _ <- setSGR sgrs
                putStr str
                setSGR []
            )

type Uniq = Int

data Ident = Ident { identPrefix :: String
                   , identNum    :: Uniq }

instance Eq Ident where
    i@(Ident _ _) == j@(Ident _ _) = (show i) == (show j)

instance Show Ident where
    show i = (identPrefix i) ++ "!" ++ (show $ identNum i)

irrelevantIdentNum = (-12345) :: Int
