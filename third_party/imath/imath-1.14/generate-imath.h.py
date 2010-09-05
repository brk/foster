#!/usr/bin/env python
##
## Name:     generate-imath.h.py, modified from findsizes.py
## Purpose:  Find acceptable digit and word types for IMath.
## Author:   M. J. Fromberger <http://spinning-yarns.org/michael/>
## Info:     $Id: findsizes.py 635 2008-01-08 18:19:40Z sting $
##

import getopt, os, re, subprocess, sys, tempfile
from string import Template

# These are the type names to test for suitability.  If your compiler
# does not support "long long", e.g., it is strict ANSI C90, then you
# should remove "long long" from this list.
try_types = [ "unsigned %s" % s for s in
              ("char", "short", "int", "long", "long long") ]

def main(args):
    """Scan the Makefile to find appropriate compiler settings, and
    then compile a test program to emit the sizes of the various types
    that are considered candidates.  The -L (--nolonglong) command
    line option disables the use of the "long long" type, which is not
    standard ANSI C90; by default, "long long" is considered.
    """
    try:
        opts, args = getopt.getopt(args, 'LFC', ('nolonglong','',''))
    except getopt.GetoptError, e:
        print >> sys.stderr, "Usage: generate-imath.h.py <path/to/imath.in.h> <path/to/imath.h> -F 'cflags' -C 'compiler' [-L/--nolonglong]"
        sys.exit(1)

    CC = "g++"
    CFLAGS = [""]

    for opt, arg in opts:
        if opt in ('-L', '--nolonglong'):
            try:
                try_types.pop(try_types.index("unsigned long long"))
            except ValueError: pass
        if opt in ('-C',):
          CC = arg
        if opt in ('-F',):
          CFLAGS = arg

    sizes = get_type_sizes(try_types, CC, CFLAGS)

    stypes = sorted(sizes.keys(), key = lambda k: sizes[k], reverse = True)
    word_type = stypes[0]
    for t in stypes[1:]:
        if sizes[t] <= sizes[word_type] / 2:
            digit_type = t
            break
    else:
        print >> sys.stderr, "Unable to find a compatible digit type."
        sys.exit(1)
    return {
      'word_type': word_type,
      'word_size': sizes[word_type],
      'digit_type': digit_type,
      'digit_size': sizes[digit_type],
      'args': args
    }

def get_type_sizes(types, cc, cflags = ()):
    """Return a dictionary mapping the names of the specified types to
    their sizes in bytes, based on the output of the C compiler whose
    path and arguments are given.
    """
    fd, tpath = tempfile.mkstemp(suffix = '.c')
    fp = os.fdopen(fd, 'r+')
    fp.seek(0)

    fp.write("#include <stdio.h>\n\nint main(void)\n{\n")
    for t in types:
        fp.write('  printf("%%lu\\t%%s\\n", (unsigned long) sizeof(%s), '
                 '\"%s\");\n' % (t, t))
    fp.write('\n  return 0;\n}\n')
    fp.close()

    print >> sys.stderr, \
          "Compiler:  %s\n" \
          "Flags:     %s\n" \
          "Source:    %s\n" % (cc, ' '.join(cflags), tpath)

    cmd = [cc] + list(cflags) + [tpath]
    if subprocess.call(cmd) <> 0:
        raise ValueError("Error while running '%s'" % ' '.join(cmd))

    os.unlink(tpath)
    if not os.path.isfile('a.out'):
        raise ValueError("No executable a.out found")

    result = subprocess.Popen(['./a.out'],
                              stdout = subprocess.PIPE).communicate()[0]

    out = {}
    for line in result.split('\n'):
        if line.strip() == '':
            continue
        size, type = re.split(r'\s+', line, 1)
        out[type] = int(size)

    os.unlink("a.out")
    return out

def readfile(filename):
  f = open(filename, 'r')
  c = ""
  try:
    c = f.read()
  finally:
    f.close()
  return c

def writefile(filename, contents):
  f = open(filename, 'w')
  try:
    f.write(contents)
  finally:
    f.close()

def file_substitute(defns, infilename, outfilename):
  contents = readfile(infilename)
  t = Template(contents).safe_substitute(defns)
  writefile(outfilename, t)

if __name__ == "__main__":
    info = main(sys.argv[1:])
    typedefs = "typedef %-20s mp_word;   /* %d bytes */\n" \
               "typedef %-20s mp_digit;  /* %d bytes */\n" % \
          (info['word_type'], info['word_size'],
           info['digit_type'], info['digit_size'])
    subst = {'MP_DIGIT_MP_WORD_TYPEDEFS': typedefs}
    imath_in_h = info['args'][0]
    imath_h = info['args'][1]
    print typedefs
    file_substitute(subst, imath_in_h, imath_h)

# Here there be dragons

