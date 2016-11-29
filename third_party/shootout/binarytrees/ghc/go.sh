#PATH=$PATH:$HOME/llvm/3.9.0/bin ghc --make -fllvm -O2 -XBangPatterns -rtsopts -funbox-strict-fields binarytrees.ghc-4.hs -o binarytrees.ghc-4.ghc_run
ghc --make -O2 -XBangPatterns -rtsopts -funbox-strict-fields binarytrees.ghc-4.hs -o binarytrees.ghc-4.ghc_run

echo "================= heap limit 168 MB, standard generational"
perf stat ./binarytrees.ghc-4.ghc_run +RTS -M168M -sgclog.txt -RTS 19
cat gclog.txt

echo "================= appel-style generational, 168M"
perf stat ./binarytrees.ghc-4.ghc_run +RTS -H -M168M -sgclog.txt -RTS 19
cat gclog.txt

echo "================== heap limit 86 MB, standard generational"
perf stat ./binarytrees.ghc-4.ghc_run +RTS -M86M -sgclog.txt -RTS 19
cat gclog.txt

echo "================= appel-style generational, 86M"
perf stat ./binarytrees.ghc-4.ghc_run +RTS -H -M86M -sgclog.txt -RTS 19
cat gclog.txt

echo "================= semispace limit 85 MB"
perf stat ./binarytrees.ghc-4.ghc_run +RTS -M170M -G1 -sgclog.txt -RTS 19
cat gclog.txt
