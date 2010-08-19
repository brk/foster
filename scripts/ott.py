import urllib2
import run_cmd
import os
import os.path

OTT_VERSION = "0.20.1"

OTT_DIR = "ott_distro_%s" % OTT_VERSION
OTT_TGZ = "%s.tar.gz" % OTT_DIR
OTT_URL = "http://www.cl.cam.ac.uk/~pes20/ott/%s" % OTT_TGZ

if not os.path.isfile(OTT_TGZ):
  print "Downloading %s ..." % OTT_URL

  otgz = urllib2.urlopen(OTT_URL)

  with open(OTT_TGZ, 'wb') as local:
    local.write(otgz.read())
  otgz.close()

if not os.path.isdir(OTT_DIR):
  run_cmd.run_command("tar -xzvf %s" % OTT_TGZ, {}, "")

run_cmd.run_command("make -C %s world-opt" % OTT_DIR, {}, "")
