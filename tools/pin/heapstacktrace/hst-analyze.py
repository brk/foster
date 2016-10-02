#!/usr/bin/env python

import fileinput
import json
import argparse
import sys

parser = argparse.ArgumentParser(description='Process the output of heap[stack]trace pintools')
parser.add_argument('infile', nargs='?', type=argparse.FileType('r'), default=sys.stdin)
parser.add_argument('--cmdline', dest='cmdline', action='store',
                    help='The command line run by Pin')
args = parser.parse_args()

# Speed is roughly 70s per 100 MB of log input...

h = []
s = []
c = []
a = []
o = []
g = []
f = []
m = []
sd = []
callcounts = []

tsc0 = 0
trimbits = 0
nignored = 0
numCalls = 0
mainish = 0
mainend = 0

mintsc = 99999999
maxtsc = 0

for line in args.infile.readlines():
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
        g = []
        f = []
        m = []
        sd = []
        callcounts = []
        mainish = int(parts[1], 16)
    elif parts[0] == 'SD':
        tsc = int(parts[1], 16)
        minstack = int(parts[2], 16)
        maxstack = int(parts[3], 16)
        sd.append( (tsc, minstack, maxstack) )
    elif parts[0] == 'T':
        tsc0 = int(parts[1], 16)
        trimbits = int(parts[2])
    elif parts[0] == 'C':
        numCalls = int(parts[1])
    elif parts[0] == 'malloc' or parts[0] == 'calloc' or parts[0] == 'realloc':
            # name size tsc-bucket tsc-cost tsc
            tsc = int(parts[2], 16)
            cyc = int(parts[3], 16)
            tscfull = int(parts[4], 16)
            sz = int(parts[1])
            if sz < 8:
                sz = 8
            h.append( (tsc, sz, cyc, tscfull) )
    elif parts[0] == 'gc':
        tsc = int(parts[1], 16)
        cyc = int(parts[2], 16)
        g.append( (tsc, cyc) )
    elif parts[0] == '2': # memalloc cell
        tsc = int(parts[1], 16)
        sz = int(parts[2])
        c.append( (tsc, sz, 1) )
    elif parts[0] == '3': # memalloc array
        tsc = int(parts[1], 16)
        sz = int(parts[2])
        a.append( (tsc, sz, 1) )
    elif parts[0] == 'mmap' or parts[0] == 'mremap' or parts[0] == 'mprotect':
        # name fulltimestamp tsc-cost
        tsc = int(parts[1], 16)
        cyc = int(parts[2], 16)
        m.append( (tsc, cyc) )
    elif parts[0] == 'free':
        # name fulltimestamp tsc-cost
        tsc = int(parts[1], 16)
        cyc = int(parts[2], 16)
        f.append( (tsc, cyc) )
    elif parts[0] == 'CC': # call count
        tsc = int(parts[1], 16)
        cnt = int(parts[2])
        callcounts.append( (tsc, cnt) )
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

print 'mainish', mainish
print len(h)
# Filter out samples from before main started.
# This is the common case, but might not be desirable
# if you're analyzing the performance impact of C++
# global constructors or something like that.
h = [tup for tup in h if tup[0] >= mainish]
print len(h)
s = [tup for tup in s if tup[0] >= mainish]
c = [tup for tup in c if tup[0] >= mainish]
a = [tup for tup in a if tup[0] >= mainish]
o = [tup for tup in o if tup[0] >= mainish]

if nignored > 0:
    print "non H/S lines ignored:", nignored

def min_tsc_of(x):
    return min(parts[0] for parts in x)
def max_tsc_of(x):
    return max(parts[0] for parts in x)

if len(s) > 0:
    mintsc = min( [mintsc, min_tsc_of(s)] )
    maxtsc = max( [maxtsc, max_tsc_of(s)] )
if len(h) > 0:
    mintsc = min( [mintsc, min_tsc_of(h)] )
    maxtsc = max( [maxtsc, max_tsc_of(h)] )

if len(sd) > 0:
    max_stack_val = max(max(s1, s2) for (tsc, s1, s2) in sd)
    # note we swap s2 and s1, since we go from absolute ptr vals
    # to depths, which means smaller values (s1) become larger deltas.
    new_sd = [(tsc, max_stack_val - s2, max_stack_val - s1) for (tsc, s1, s2) in sd]
    sd = new_sd[:]

print "#Stack ops:   ", len(s)
print "#H/mallocs:   ", len(h)
print "#Cell allocs: ", len(c)
print "#Arr allocs : ", len(a)
print "#OCaml allocs:", len(o)
print "#GC pauses:   ", len(g)
print "#Free ops:    ", len(f)
print "#Mem (VM sys):", len(m)
print "#StackDepths: ", len(sd)
print "#CallCounts:  ", len(callcounts)

if len(callcounts) > 0:
    numCalls = sum(tup[1] for tup in callcounts)

if True:
    malloc_b     = sum(tup[1] for tup in h)
    memalloc_b   = sum(tup[1] for tup in c)
    arralloc_b   = sum(tup[1] for tup in a)
    ocamlalloc_b = sum(tup[1] for tup in o)
    ocamlalloc_n = sum(tup[2] for tup in o)
    if len(s) > 0:
        stackalloc_b = sum(tup[1] for tup in s)
        print "stack alloc:", stackalloc_b, "b", "(%.2f per frame, %d calls)" % ((float(stackalloc_b) / float(numCalls)), numCalls)
    if len(h) > 0:
        print "malloc     :", malloc_b, "b", "(%d per cell)" % int(malloc_b / len(h))
        print "min malloc pause:", min( tup[2] for tup in h), "cyc"
        print "max malloc pause:", max( tup[2] for tup in h), "cyc"
        print "sum malloc pauses:", sum(tup[2] for tup in h), "cyc"
        print "avg malloc pause :", sum(tup[2] for tup in h) / len(h), "cyc"
    if memalloc_b > 0:
        print "memalloc   :", memalloc_b, "b"
    if arralloc_b > 0:
        print "memallocarr:", arralloc_b, "b"
    if ocamlalloc_b > 0:
        print "ocaml alloc:", ocamlalloc_b, "b", "avg %.2f over %d allocs" % ((ocamlalloc_b / ocamlalloc_n), ocamlalloc_n)
    if len(g) > 0:
        print "min GC pause:", min(cyc for (tsc, cyc) in g), "cyc"
        print "max GC pause:", max(cyc for (tsc, cyc) in g), "cyc"
        print "sum GC pauses:", sum(cyc for (tsc, cyc) in g), "cyc"
        print "avg GC pause :", sum(cyc for (tsc, cyc) in g) / len(g), "cyc"
    if len(f) > 0:
        print "min free() pause:", min(cyc for (tsc, cyc) in f), "cyc"
        print "max free() pause:", max(cyc for (tsc, cyc) in f), "cyc"
        print "sum free() pauses:", sum(cyc for (tsc, cyc) in f), "cyc"
        print "avg free() pause :", sum(cyc for (tsc, cyc) in f) / len(f), "cyc"
    if len(m) > 0:
        print "min VMem pause:", min(cyc for (tsc, cyc) in m), "cyc"
        print "max VMem pause:", max(cyc for (tsc, cyc) in m), "cyc"
        print "sum VMem pauses:", sum(cyc for (tsc, cyc) in m), "cyc"
        print "avg VMem pause :", sum(cyc for (tsc, cyc) in m) / len(m), "cyc"

try:
    perfstat = open('perf.stat.txt', 'r').readlines()
except:
    perfstat = []

print 'buckets elapsed:', (mainend - mainish)
with open('hst.json.js', 'w') as hst:
    hst.write('var hst = ')
    json.dump({'h':h, 's':s, 'c':c, 'a':a, 'o':o, 'g':g, 'f':f, 'm':m, 'callcounts':callcounts, 'sd':sd,
               'mintsc': mintsc, 'maxtsc':maxtsc, 'perfstat': perfstat,
               'trimbits':trimbits, 'maintsc':mainish, 'mainend':mainend,'cmdline':args.cmdline}, hst)
    hst.write(';')
