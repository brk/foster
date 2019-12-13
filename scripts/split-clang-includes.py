#!/usr/bin/env python3
import fileinput
for line in fileinput.input():
    parts = line.strip().split(':')
    iparts = [p + '/include' for p in parts]
    for ip in iparts:
        print(' -I ' + ip, end=' ')

