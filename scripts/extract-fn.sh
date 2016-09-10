#!/bin/sh

SD=$(dirname `which $0`)/../scripts
LLVM=$($SD/echo-llvmdir)/bin

TEST=$1
FUNC=$2

BASE=test-tmpdir/$TEST

$LLVM/llvm-extract $BASE/out.preopt.bc -func=$FUNC -o $BASE/ju.bc
$LLVM/llvm-dis     $BASE/ju.bc
cat                $BASE/ju.ll | awk '/gc "fostergc" {/,/^}/'
