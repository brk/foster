#PATH=$PATH:$HOME/llvm/3.9.0/bin ghc --make -fllvm -O2 -XBangPatterns -rtsopts -funbox-strict-fields binarytrees.ghc-4.hs -o binarytrees.ghc-4.ghc_run
ghc --make -O1 -XBangPatterns -rtsopts binarytrees.ghc-4.hs -o binarytrees.ghc-4.ghc_run
perf stat ./binarytrees.ghc-4.ghc_run +RTS -K68M -H -sgclog.txt -RTS 19

#ghc --make -O2 -XBangPatterns -rtsopts -funbox-strict-fields binarytrees.ghc-4.hs -o binarytrees.ghc-4.ghc_run
#perf stat ./binarytrees.ghc-4.ghc_run +RTS -K68M -H -sgclog.txt -RTS 19

