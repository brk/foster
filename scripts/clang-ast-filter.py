#!/usr/bin/env python

import sys
import re

import ansifilter

def is_toplevel_nested_decl(line):
  return line[:2] == "|-"

def is_from_main_TU(line):
  m = re.match("([\| ]+-)?[^<]+ <(?:col:\d+, )?(...)", line)
  if m is None:
    return False
  else:
    #print "groups are", m.groups()
    return m.group(2) in ["col", "lin", "/ho"]

if __name__ == '__main__':
  shouldshow = True
  for line in sys.stdin:
    cleaned = ansifilter.remove_ansi_escapes_from(line)
    if is_toplevel_nested_decl(cleaned):
      shouldshow = is_from_main_TU(cleaned)
      #print "shouldshow is now ", shouldshow, "for line: ", line,

    if shouldshow:
      print line,

