#!/usr/bin/env python

import fileinput
import re

def remove_ansi_escapes_from(line):
  return re.sub('\033[^m]*m', '', line)

if __name__ == '__main__':
  for line in fileinput.input():
    print remove_ansi_escapes_from(line),
