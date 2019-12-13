#!/usr/bin/env python3

import sys
import fileinput

# Usage: cat input.txt | align-on-first.py @ > aligned.txt

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
        print(before, end='')
        print(spaces(maxoffset - len(before)), end='')
        print(sep, end='')
        print(after, end='')

    block = []

lines = list(fileinput.input(sys.argv[2:]))
for line in lines:
    if sep in line:
        block.append(line)
    else:
        process_block()
        print(line, end='')
process_block()
sys.stdout.flush()

