#PATH=$PATH:$HOME/llvm/3.9.0/bin ghc --make -fllvm -O2 -XBangPatterns -rtsopts -funbox-strict-fields binarytrees.ghc-4.hs -o binarytrees.ghc-4.ghc_run
ghc --make -O2 -XBangPatterns -rtsopts -funbox-strict-fields binarytrees.ghc-4.hs -o binarytrees.ghc-4.ghc_run
perf stat ./binarytrees.ghc-4.ghc_run +RTS -K256M -H -sgclog.txt -RTS 20
