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
nignored = 0
numCalls = 0
for line in fileinput.input():
  line = line.strip()
  parts = line.split()
  try:
    if len(parts) == 0 or parts[0] == 'X':
        pass
    elif parts[0] == '5':
        h = []
        s = []
        c = []
        a = []
        o = []
    elif parts[0] == 'T':
        tsc0 = int(parts[1], 16)
    elif parts[0] == 'C':
        numCalls = int(parts[1])
    elif parts[0] == '1': # malloc
        tsc = int(parts[1], 16)
        sz = int(parts[2])
        h.append( (tsc, sz) )
    elif parts[0] == '2': # memalloc
        tsc = int(parts[1], 16)
        sz = int(parts[2])
        c.append( (tsc, sz) )
    elif parts[0] == '3': # array alloc
        tsc = int(parts[1], 16)
        sz = int(parts[2])
        a.append( (tsc, sz) )
    elif parts[0] == 'B': # bucket
        tsc = int(parts[1], 16)
        idx = 2
        while idx < len(parts):
            k = parts[idx]
            sz = int(parts[idx + 1])
            idx += 2

            if sz < 18000000000000000000:
                if   k == '4': # sub or -add
                    s.append( (tsc, sz) )
                elif k == '6': # push(es)
                    s.append( (tsc, sz) )
                elif k == '7': # sub/add, non-const
                    s.append( (tsc, sz) )
                elif k == '9': # ocaml alloc
                    o.append( (tsc, sz) )
                elif k == '8': # add negative
                    s.append( (tsc, sz) )
                else:
                    nignored += 1
  except:
    print 'line is:', line
    raise

if nignored > 0:
    print "non H/S lines ignored:", nignored

def min_tsc_of(x):
    return min(tsc for (tsc, sz) in x)
def max_tsc_of(x):
    return max(tsc for (tsc, sz) in x)

if True:
    mintsc = min_tsc_of(s)
    maxtsc = max_tsc_of(s)
    if len(h) > 0:
        mintsc = min( [mintsc, min_tsc_of(h)] )
        maxtsc = max( [maxtsc, max_tsc_of(h)] )
    d_tsc =  (maxtsc - mintsc)
    print "d_tsc:", d_tsc


print "#Sinsn: ", len(s)
print " S>8: max", max(sz for (tsc, sz) in s if sz > 8)

print "#H: ", len(h)
print "#C: ", len(c)
print "#A: ", len(a)
print "#O: ", len(o)

if True:
    malloc_b = sum(sz for (tsc, sz) in h)
    memalloc_b = sum(sz for (tsc, sz) in c)
    arralloc_b = sum(sz for (tsc, sz) in a)
    ocamlalloc_b = sum(sz for (tsc, sz) in o)
    stackalloc_b = sum(sz for (tsc, sz) in s)
    print "stack alloc:", stackalloc_b, "b", "(%.2f per frame, %d calls)" % ((float(stackalloc_b) / float(numCalls)), numCalls)
    print "malloc     :", malloc_b, "b", "(%d per cell)" % int(malloc_b / len(h))
    if memalloc_b > 0:
        print "memalloc   :", memalloc_b, "b"
    if arralloc_b > 0:
        print "memallocarr:", arralloc_b, "b"
    if ocamlalloc_b > 0:
        print "ocaml alloc:", ocamlalloc_b, "b"

with open('hst.json', 'w') as hst:
    json.dump({'h':h, 's':s, 'a':a, 'o':o}, hst)
