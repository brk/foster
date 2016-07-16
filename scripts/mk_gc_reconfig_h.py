#!/usr/bin/env python

# Copyright (c) 2013 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

import os
import os.path

from optparse import OptionParser

def ensure_file_exists(path):
  open(path, 'a').close()

def get_parser(usage):
  parser = OptionParser(usage=usage)
  parser.add_option("--srcdir", dest="srcdir", action="store",
                    help="Use srcdir as default place to find source")
  return parser

if __name__ == "__main__":
  parser = get_parser("usage: %prog [options]")
  (options, args) = parser.parse_args()

  reconfig_path = os.path.join(options.srcdir, 'runtime', 'gc', 'foster_gc_reconfig-inl.h')
  ensure_file_exists(reconfig_path)
