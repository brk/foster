module Foster.Base where

import System.Console.ANSI
import Control.Monad

data OutputData = OutputData { outputDataSGRs :: [SGR]
                             , outputDataString :: String }
type Output = [OutputData]

instance Eq OutputData where
    (OutputData _ sa) == (OutputData _ sb) = sa == sb

out :: String -> Output
out s = [(OutputData ([] :: [SGR]) s)]

outLn s = out (s ++ "\n")

outCS :: Color -> String -> Output
outCS c s = [OutputData [SetColor Foreground Dull c] s]

outCSLn c s = outCS c (s ++ "\n")

outToString o = fmap outputDataString o

runOutput :: Output -> IO ()
runOutput outs = do
    forM_ outs $ (\(OutputData sgrs str) -> do
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


