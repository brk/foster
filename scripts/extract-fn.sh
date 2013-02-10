#!/bin/sh

LLVM=~/llvm/3.1/bin

TEST=$1
FUNC=$2

BASE=test-tmpdir/$TEST

$LLVM/llvm-extract $BASE/out.preopt.bc -func=$FUNC -o $BASE/ju.bc
$LLVM/llvm-dis     $BASE/ju.bc
cat                $BASE/ju.ll | awk '/gc "fostergc" {/,/^}/'
