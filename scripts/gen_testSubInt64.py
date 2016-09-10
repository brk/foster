#!/usr/bin/env python2

import random

def n64(a,b):
  return a*2**32 + abs(b)

for x in range(50):
  a = random.randrange(0,65000)
  b = random.randrange(0,65000)
  c = random.randrange(0,65000)
  d = random.randrange(0,65000)
  print "    testSubInt64 %d %d %d %d  %d %d %d;" % (a,b,c,d, n64(a,b), n64(c,d), n64(a,b)-n64(c,d))
