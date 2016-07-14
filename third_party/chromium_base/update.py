#!/usr/bin/env python

import os
import os.path
import re
import shutil
import subprocess
import errno

def dropFrom(prefix, string):
    if string.startswith(prefix):
        return string[len(prefix):]
    return string

srcbase = os.path.expanduser("~/chrm/src/base")

assert os.path.exists(srcbase)

newbase = "base"
if not os.path.isdir(newbase):
    os.mkdir(newbase)

assert os.path.exists(newbase)

lines = open("CMakeLists.txt", 'r').readlines()
files = []
for line in lines:
    m = re.search("^[^#]*_BASE}/base/([^ ]*)", line)
    if m:
        files.append( m.groups()[0].strip() )

# http://stackoverflow.com/questions/600268/mkdir-p-functionality-in-python
def mkdir_p(path):
    try:
        os.makedirs(path)
    except OSError as exc:  # Python >2.5
        if exc.errno == errno.EEXIST and os.path.isdir(path):
            pass
        else:
            raise

def blacklisted(fragment):
    bad = fragment in ["gtest_prod_util.h"]
    if bad:
        print "Refusing to copy blacklisted file", fragment, "..."
    return bad

def copyrel(fragment):
    if not blacklisted(fragment):
        path = os.path.join(srcbase, fragment)
        dest = os.path.join(newbase, fragment)
        mkdir_p(os.path.dirname(dest))
        #print "copying", path, "to", dest
        assert os.path.exists(path), path
        shutil.copy2(path, dest)
        return (path, dest)

def mkrel(abspath):
    prefixpath = os.path.join(srcbase, '')
    dropped = dropFrom(prefixpath, abspath)
    if dropped != abspath:
        return dropped
    else:
        m = re.search("chromium_base/base/(.*)", abspath)
        if m:
            return m.groups()[0]
        else:
            print "expected to find chromium_base/base in:", abspath
            raise "oops"

def copy_files_from_CMakeLists(files):
  for fp in files:
    if os.path.exists(os.path.join(srcbase, fp)):
        if not os.path.exists(os.path.join(newbase, fp)):
          copyrel(fp)
    else:
        filename = os.path.basename(fp)
        foundbytes = subprocess.check_output(["find", srcbase, "-iname", filename])
        foundlines = foundbytes.strip().split('\n')
        founds = [mkrel(line) for line in foundlines if line.strip() != '']
        if len(founds) == 1 and founds[0].strip() != "":
            print "          File appears to have been moved from", fp, "to", "'" + founds[0] + "'"
            copyrel(founds[0])
        elif len(founds) > 1:
            print "File appears to have been moved, with multiple alternatives:"
            for x in founds:
                print "      ", x
            print "Please edit CMakeLists.txt as appropriate and re-run this script."
        else:
            print "Unable to find anything like", filename, "; maybe", fp, "is no longer needed?"

copy_files_from_CMakeLists(files)

def exise_gtest_from_header(output, relpath):
    print "Copying a gtest-less version of", relpath
    if relpath is None:
        return False
    (src, dest) = copyrel(relpath)
    contents = open(src, 'r').read()
    contents = contents.replace('#include "base/gtest_prod_util.h"', '//#include "base/gtest_prod_util.h"')
    contents = contents.replace("FRIEND_TEST_ALL_PREFIXES", "//FRIEND_TEST_ALL_PREFIXES")
    open(dest, 'w').write(contents)
    return relpath

def find_last_including_header(output):
    absheaderpath = None
    lines = output.split('\n')
    for line in lines:
        m = re.match('In file included from ([^:]+):', line)
        if m:
            absheaderpath = m.groups()[0]
    if absheaderpath is None:
        return None
    else:
        return mkrel(absheaderpath)

def summarize_missing_symbols(output):
    matches = re.findall('"([^"]+)", referenced from', output)
    if len(matches) >= 1:
        print "Missing symbols:"
        for symbol in matches:
            print "   ", symbol
    else:
        print output

def try_make():
    try:
        subprocess.check_output(["make", "-C", "~/Code/foster/_obj"], stderr=subprocess.STDOUT)
        print "Success!"
        return True

    except subprocess.CalledProcessError as e:
        m = re.search("fatal error: 'base/(.*?\.h)' file not found", e.output)
        if m:
            header = m.groups()[0]
            copyrel(header)
            print "Copied header file:", header, "; trying again..."
            return False
        else:
            ok = False
            m = re.search('testing/gtest/include/gtest/gtest_prod.h', e.output)
            if m:
                exise_gtest_from_header(e.output, find_last_including_header(e.output))
                return False

            if re.search('Undefined symbols', e.output):
                summarize_missing_symbols(e.output)
                return True

            if not ok:
                print "Compilation failed but we didn't find a missing base/ header."
                print "Output was:"
                print e.output
                return True

while True:
    finished = try_make()
    if finished:
        break


