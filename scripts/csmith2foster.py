#!/usr/bin/env python3

from test_c2f import run_cmd, attempt_test_named
import os.path

#############################

def generate_test_named(c_code):
    # This assumes foster/scripts/ is in the PATH.
    run_cmd("csmith-minimal.sh", stdout=open(c_code, 'w'))

def attempt_test_numbered(x):
    c_code  = "csf_%03d.c" % x
    generate_test_named(c_code)
    attempt_test_named(c_code, [])

#for x in range(20):
#    attempt_test_numbered(x)

#for x in ['csf_000.c', 'csf_001.c']:

for x in range(20):
    c_code  = "csf_%03d.c" % x
    generate_test_named(c_code)
    attempt_test_named(c_code, [])

