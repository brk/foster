#!/usr/bin/env python

# Copyright (c) 2010 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

from __future__ import with_statement

import re
import sys
import tempfile

from run_cmd import *

# Runs the given Google Test-based unittest, only printing failing lines.

if __name__ == "__main__":
  if not len(sys.argv) in [2, 3]:
    print "Usage: %s <unittest_binary>"
    sys.exit(1)

  binary = sys.argv[1]
  
  with tempfile.TemporaryFile() as tmp:
    run_command(binary, {}, binary, tmp, None, None, False)
    
    tmp.seek(0)
    
    for line in tmp:
      if (line.startswith('[---') or
	  line.startswith('[ RUN') or
	  line.startswith('[    ') or
	  re.match(r"^\s*$", line)):
        continue
      print line.rstrip()
