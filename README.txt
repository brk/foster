============================= Usage ========================================

$ # Run through "Installation" steps below, then:

$ hg clone https://foster.googlecode.com/hg/ foster
$ cd foster
$ mkdir _obj        # Separate directory for compilation results and such
$ cd _obj           # The name can be whatever you'd like, but it should
                    # be located outside of the foster source directory.
$ ccmake .. -G "Unix Makefiles"
        # Press 'c' to configure; if CMake cannot find the listed paths,
        #                         please set them by hand.
        # Press 'g' to generate Makefiles and exit once paths are OK

Once the first-time steps are done:

$ make            # Recompile any updated files.
$ make regress    # Run regression tests

After running regression tests, you can look for trace messages
from the middle-end with a command like this:

$ cat test-tmpdir/*/compile.log.txt | grep '...' | sort | uniq

Other commands of interest, from _obj:

$ make hs_clean    # Delete just the Haskell-generated .o files
$ make list_regression_tests

From project root:

$ scripts/countlines.sh  # Give an overview of where code is, volume-wise.

============================= Installation =================================
Paths:
  You'll want to append $PATH_TO_FOSTER/scripts to $PATH and $PYTHONPATH,
  probably in .bashrc or equivalent.

Ubuntu 10.10:
	Dependencies: CMake, ANTLR3 C runtime, Java, LLVM,
                      Google protobuf, z3

   You can install llvm by executing   bash scripts/install-llvm.sh

	Assuming you already have LLVM installed, in $PATH and $PKG_CONFIG_PATH...

	Interesting packages:
		cmake		libgmp3c2      m4       ministat
	(universe)
		binutils-gold	cmake-curses-gui	mercurial
					libffi-dev
		ccache		ack-grep        libedit-dev

                libprotobuf6 (7 on newer Ubuntus)
                protobuf-compiler       libprotobuf-dev
                python-protobuf libprotobuf-java
      subversion    vim     curl  ctags

      For GHC, to get profiling libraries, do not use apt-get;
      instead, download a generic binary tarball directly from
      http://www.haskell.org/ghc/download
      and cabal-install from
      http://www.haskell.org/cabal/download.html

      To get GHC to see libgmp:
        sudo apt-get install libgmp3-dev
        sudo ln -s /usr/lib/i386-linux-gnu/libgmp.so{,.3}

        For Ott:
                coq             texlive-latex-base

        For Sphinx:
          # If you don't have easy_install available already:
          curl -O http://peak.telecommunity.com/dist/ez_setup.py
          sudo python ez_setup.py -U setuptools

          sudo easy_install -U sphinx

	If you need Java on Ubuntu 9.10,
	sudo apt-get install sun-java6-jdk

	on 10.04, install default-jdk


	sudo apt-get install cmake cmake-curses-gui # etc

	For emscripten:
	        sudo apt-get install python-software-properties
	        sudo apt-get update
	        sudo add-apt-repository ppa:chris-lea/node.js
	        sudo apt-get install nodejs npm

      For CVC4, add the following lines to /etc/apt/sources.list::

          deb http://cvc4.cs.nyu.edu/debian/ unstable/
          deb-src http://cvc4.cs.nyu.edu/debian/ unstable/

      Then::

          $ sudo apt-get update
          $ sudo apt-get install cvc4 libcvc4-dev


Mac OS X:
	Interesting ports (via MacPorts):

	protobuf-cpp protobuf-java protobuf-python26

        cairo  pango  gtk2

ANTLR on Linux and OS X:
	ANTLR_VERSION=3.2
	ANTLR_DIR=~/antlr/${ANTLR_VERSION}
	mkdir tmp
	cd tmp
		wget http://antlr3.org/download/C/libantlr3c-${ANTLR_VERSION}.tar.gz
		tar xzvf libantlr3c-${ANTLR_VERSION}.tar.gz
                cd libantlr3c-${ANTLR_VERSION}
		./configure --prefix=${ANTLR_DIR} --enable-64bit && make && make install
                cd ..
	cd ..
	rm -rf ./tmp
	pushd ${ANTLR_DIR}
	wget http://antlr3.org/download/antlr-${ANTLR_VERSION}.jar
	popd

On Ubuntu 10.10:
      sudo apt-get install libglib2.0-{bin,dev} libpng12-dev
                           libcairo2-dev libpango1.0-dev libgtk2.0-dev
                           libgtksourceview2.0-{0,dev}

Haskell:
   To enable profiling, add    library-profiling: True   to   ~/.cabal/config
   before installing any further packages. Then:
      cabal update
      cabal install cabal-install
      cabal install happy alex
      export PATH=$PATH:~/.cabal/bin
      cabal install haskell-src
      cabal install gtk2hs-buildtools
      cabal install chart
      cabal install criterion hoopl cbor
      cabal install text protocol-buffers filepath hprotoc ansi-terminal ansi-wl-pprint fgl boxes data-dword smtLib union-find
      cabal install language-lua

Python:
        pip install pyyaml

Other libraries/tools:
        gperftools: https://code.google.com/p/gperftools/
        	If you install via deb, you'll need to install both...
        kcachegrind: http://kcachegrind.sourceforge.net/html/Home.html
        valgrind
        pin:        http://software.intel.com/en-us/articles/pin-a-dynamic-binary-instrumentation-tool
        leveldb:    https://code.google.com/p/leveldb/
        leveldb-go: https://code.google.com/p/leveldb-go/
        snappy:     https://code.google.com/p/snappy/
        cityhash:   https://code.google.com/p/cityhash/
        ocaml-core: https://bitbucket.org/janestreet/core

        hprotoc:    http://hackage.haskell.org/package/hprotoc

Networking
==========

On Linux:

        sudo ip tuntap add tun8 mode tun  # For IP-format frames
        sudo ip link   set tun8 up
        sudo ip addr   add 192.168.6.6/24 dev tun8
        Process open()s /dev/net/tun, then calls ioctl() with TUNSETIFF
                to get a fd for tun8
        (once a process is blocked reading from tun8:)
        ping 192.168.6.42 # if we ping 6.6 the kernel delivers packets to lo

On Mac OS X, first install tuntaposx <http://tuntaposx.sourceforge.net/>, then:

        Process open()s /dev/tun8
        Process calls system(sudo ifconfig tun8 192.168.6.41 192.168.6.42)
        ping 192.168.6.42

