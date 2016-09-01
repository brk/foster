#!/usr/bin/env python

from __future__ import with_statement

from test_c2f import run_cmd, attempt_test_named
import os.path

csmith_dir = os.path.expanduser("~/sw/local/csmith-2016-08-26")

#############################

def generate_test_named(c_code):
    run_cmd("csmith-minimal.sh", stdout=open(c_code, 'w'))

def attempt_test_numbered(x):
    c_code  = "csf_%03d.c" % x
    generate_test_named(c_code)
    attempt_test_named(c_code)

#for x in range(20):
#    attempt_test_numbered(x)

#for x in ['csf_000.c', 'csf_001.c']:

for x in range(20):
    c_code  = "csf_%03d.c" % x
    generate_test_named(c_code)
    attempt_test_named(c_code)

