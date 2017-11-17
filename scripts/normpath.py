#!/usr/bin/env python2

import os
import sys

if len(sys.argv) == 2:
  print os.path.normpath(sys.argv[1])
else:
  print """Usage: %s <path-to-normalize>""" % sys.argv[0]
