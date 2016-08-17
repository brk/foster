#!/usr/bin/env python

import sys
import fileinput

# Usage: cat input.txt | python align-on-first.py @ > aligned.txt

sep = sys.argv[1]

def offsetof(sep, s):
    return s.find(sep)

def spaces(n):
    return (" " * n)

block = []
def process_block():
    global block

    if len(block) == 0:
        return

    offsets = [offsetof(sep, s) for s in block]
    maxoffset = max(offsets)

    for line in block:
        (before, after) = line.split(sep, 1)
        print before,
        print spaces(maxoffset - len(before)),
        print sep,
        print after,

    block = []

lines = list(fileinput.input(sys.argv[2:]))
for line in lines:
    if sep in line:
        block.append(line)
    else:
        process_block()
        print line,
process_block()
sys.stdout.flush()

