#!/usr/bin/env python

import fileinput
import json

# Speed is roughly 70s per 100 MB of log input...

h = []
s = []
c = []
a = []
o = []

tsc0 = 0
trimbits = 0
nignored = 0
numCalls = 0
mainish = 0
mainend = 0

# Per-function, the first function call seen will have an artificially inflated
# runtime from Pin's instrumentation, so we toss it out.
seenfuncs = {}

for line in fileinput.input():
  line = line.strip()
  parts = line.split()
  try:
    if len(parts) == 0 or parts[0] == 'X':
        pass
    elif parts[0] == 'main-end':
        if mainend == 0:
            mainend = int(parts[1], 16)
    elif parts[0] == 'main-ish':
        h = []
        s = []
        c = []
        a = []
        o = []
        mainish = int(parts[1], 16)
    elif parts[0] == 'T':
        tsc0 = int(parts[1], 16)
        trimbits = int(parts[2])
    elif parts[0] == 'C':
        numCalls = int(parts[1])
    elif parts[0] == 'malloc' or parts[0] == 'calloc' or parts[0] == 'realloc':
        if parts[0] in seenfuncs:
            # name size tsc-bucket tsc-cost
            tsc = int(parts[2], 16)
            cyc = int(parts[3], 16)
            sz = int(parts[1])
            if sz < 8:
                sz = 8
            h.append( (tsc, sz, cyc) )
        else:
            seenfuncs[parts[0]] = True
    elif parts[0] == '2': # memalloc cell
        tsc = int(parts[1], 16)
        sz = int(parts[2])
        c.append( (tsc, sz, 1) )
    elif parts[0] == '3': # memalloc array
        tsc = int(parts[1], 16)
        sz = int(parts[2])
        a.append( (tsc, sz, 1) )
    elif parts[0] == 'mmap' or parts[0] == 'mremap' or parts[0] == 'mprotect' or parts[0] == 'free':
        # name fulltimestamp tsc-cost
        pass
    elif parts[0] == 'B': # bucket
        tsc = int(parts[1], 16)
        idx = 2
        while idx < len(parts):
            k = parts[idx]
            sz = int(parts[idx + 1])
            cnt = int(parts[idx + 2])
            mx = int(parts[idx + 3])
            idx += 4

            if sz < 18000000000000000000:
                if   k == '4': # sub or -add
                    s.append( (tsc, sz, cnt, mx) )
                elif k == '6': # push(es)
                    s.append( (tsc, sz, cnt, mx) )
                elif k == '7': # sub/add, non-const
                    s.append( (tsc, sz, cnt, mx) )
                elif k == '9': # ocaml alloc
                    o.append( (tsc, sz, cnt, mx) )
                elif k == '8': # add negative
                    s.append( (tsc, sz, cnt, mx) )
                else:
                    nignored += 1
  except:
    #print 'line is:', line
    raise

if nignored > 0:
    print "non H/S lines ignored:", nignored

def min_tsc_of(x):
    return min(parts[0] for parts in x)
def max_tsc_of(x):
    return max(parts[0] for parts in x)

mintsc = min_tsc_of(s)
maxtsc = max_tsc_of(s)
if len(h) > 0:
    mintsc = min( [mintsc, min_tsc_of(h)] )
    maxtsc = max( [maxtsc, max_tsc_of(h)] )

print "#Sinsn: ", len(s)
print " S>8: max", max(mx for (tsc, sz, cnt, mx) in s if sz > 8)

print "#H: ", len(h)
print "#C: ", len(c)
print "#A: ", len(a)
print "#O: ", len(o)

if True:
    malloc_b     = sum(sz for (tsc, sz, cyc) in h)
    memalloc_b   = sum(sz for (tsc, sz, one) in c)
    arralloc_b   = sum(sz for (tsc, sz, one) in a)
    ocamlalloc_b = sum(sz for (tsc, sz, cnt, mx) in o)
    stackalloc_b = sum(sz for (tsc, sz, cnt, mx) in s)
    print "stack alloc:", stackalloc_b, "b", "(%.2f per frame, %d calls)" % ((float(stackalloc_b) / float(numCalls)), numCalls)
    print "malloc     :", malloc_b, "b", "(%d per cell)" % int(malloc_b / len(h))
    if memalloc_b > 0:
        print "memalloc   :", memalloc_b, "b"
    if arralloc_b > 0:
        print "memallocarr:", arralloc_b, "b"
    if ocamlalloc_b > 0:
        print "ocaml alloc:", ocamlalloc_b, "b"

with open('hst.json.js', 'w') as hst:
    hst.write('var hst = ')
    json.dump({'h':h, 's':s, 'a':a, 'o':o, 'mintsc': mintsc, 'maxtsc':maxtsc, 'trimbits':trimbits, 'maintsc':mainish, 'mainend':mainend}, hst)
    hst.write(';')
