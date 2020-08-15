#!/usr/bin/env python3

import sys
import re

# This script is a helper for the `c2foster` program, which needs to
# separate out positional arguments for code files from non-file flags.

def argsplit(args):
    files = []
    nonfiles = []
    c2fflags = []
    eatNext = False

    for a in args:
        if len(a) == 0:
            continue
        if eatNext:
            c2fflags.append(a)
            eatNext = False
        elif (a in ['-dump-cfgs', '-dump-orig-source', '-c2f-verbose', '-c2f-bareliterals']):
            c2fflags.append(a)
        elif (a in ['-c2f-nonnull', '-c2f-imm', '-c2f-arr']):
            c2fflags.append(a)
            eatNext = True
        elif a[0] == '-':
            nonfiles.append(a)
        elif re.search(r"\.[ch]$", a):
            files.append(a)
        else:
            nonfiles.append(a)
    return (files, nonfiles, c2fflags)

def arg(x):
    if ' ' in x:
        return '"' + x + '"'
    else:
        return x

if __name__ == '__main__':
    fs, nf, cf = argsplit(sys.argv[1:])
    print(' '.join(arg(f) for f in fs))
    print(' '.join(arg(f) for f in nf))
    print(' '.join(arg(f) for f in cf))

