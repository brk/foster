#!/bin/sh

set -e
set -x

    sudo apt update
    sudo apt-get install --yes build-essential git gnuplot curl \
                           python3-pygments python3-matplotlib  python3-scipy python3-sphinx \
                           python3-pandas python3-pip python3-numpy python3-pyqt5 \
                           z3 libdw-dev
    sudo apt-get install --yes vim libsparsehash-dev \
                  curl exuberant-ctags aptitude libcairo2-dev libc6-dev default-jdk
    sudo apt-get install --yes m4 ministat meld \
             linux-tools-virtual linux-tools-generic \
             libffi-dev libffi7 libedit-dev cmake cmake-curses-gui
    
    sudo apt-get install --yes libncurses5-dev libncurses-dev libncurses5 libtinfo5

    # LLVM 17 needs these libraries
    sudo apt-get install --yes zlib1g-dev libxml2-dev libzstd-dev

    
      # GMP is needed for GHC to build Cabal from source.
      sudo apt-get install --yes libgmp3-dev libgmp-dev libgmp10 
    
      curl https://beyondgrep.com/ack-v3.5.0 > ~/.local/bin/ack && chmod 0755 ~/.local/bin/ack
    
      # Get GHC
      #curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
      #ghcup install ghc -u 'https://downloads.haskell.org/~ghc/9.0.1/ghc-9.0.1-x86_64-deb10-linux-dwarf.tar.xz' 9.0.1-dwarf
      #ghcup set ghc 9.0.1-dwarf
    
      # Python packages, mostly used by benchmarking infrastructure
      pip3 install pyyaml jinja2 statsmodels mpld3 seaborn
    
      mkdir tmp
      cd tmp
      wget https://www.thrysoee.dk/editline/libedit-20210522-3.1.tar.gz
      tar xf libedit*.gz
      rm libedit*.gz
      cd libedit*
      ./configure --prefix=$HOME/.local && make -j && make install
      cd ..
    
    
      #wget http://prdownloads.sourceforge.net/swig/swig-3.0.12.tar.gz
      wget http://prdownloads.sourceforge.net/swig/swig-4.0.2.tar.gz
      tar xf swig-*.gz
      rm swig-*.gz
      cd swig-*
      ./configure --prefix=$HOME/.local && make -j && make install
      cd ..
    
      #wget https://downloads.haskell.org/~ghc/8.8.1/ghc-8.8.1-x86_64-deb9-linux-dwarf.tar.xz
      #tar xf ghc-*.xz
      #rm ghc-*.xz
      #cd ghc-* && ./configure --prefix=$HOME/.local/ghc-8.8.1 && make -j install && cd ..
    
      #wget https://downloads.haskell.org/~cabal/cabal-install-latest/cabal-install-3.0.0.0-x86_64-unknown-linux.tar.xz
      #tar xf cabal-*.tar.*
      #rm cabal-*.tar.*
      #mv cabal ~/.local/bin
    
      curl -O https://capnproto.org/capnproto-c++-0.8.0.tar.gz
      tar xf capnproto-*.gz
      rm     capnproto-*.gz
      cd capnproto-c++-0.8.0
      ./configure --prefix=$HOME/.local/capnp-c++-0.8.0
      make -j check
      make install
      cd ..
    
    
      cd ..
      rm -rf tmp/
    
    
    	ANTLR_VERSION=3.4
    	ANTLR_DIR=~/antlr/${ANTLR_VERSION}
    	mkdir tmp
    	cd tmp
    		wget http://antlr3.org/download/C/libantlr3c-${ANTLR_VERSION}.tar.gz
    		tar xzvf libantlr3c-${ANTLR_VERSION}.tar.gz
                    cd libantlr3c-${ANTLR_VERSION}
    		./configure --prefix=${ANTLR_DIR} --enable-64bit && make -j && make install
                    cd ..
    	cd ..
    	rm -rf ./tmp
    	pushd ${ANTLR_DIR}
    	wget http://antlr3.org/download/antlr-${ANTLR_VERSION}-complete.jar
            mv antlr-${ANTLR_VERSION}-complete.jar antlr-${ANTLR_VERSION}.jar
    	popd
    
    
    export PATH=$PATH:$HOME/.local/bin:$HOME/.local/capnp-c++-0.8.0/bin
    source ~/.ghcup/env
    
    cabal update
    
    cat ~/.cabal/config | sed 's/-- library-profiling:/library-profiling: True/' > tmp.txt
    mv tmp.txt ~/.cabal/config
    
    
    git clone https://github.com/brk/sw.git ~/sw
    
    if [ ! -d ~/foster ]; then
      git clone https://github.com/brk/foster.git ~/foster
    fi

    git clone https://github.com/brk/minuproto.git ~/sw/local/minuproto
    cd ~/sw/local/minuproto
    cabal v2-build
    cabal v2-install

echo Okay, starting to install LLVM...
bash ~/foster/scripts/install-llvm.sh


pushd ~/foster/third_party/nacl-20110221
echo "Building NaCl, this will take several minutes."
./do
popd

echo Time to build Foster itself!
cd ~/foster
mkdir _obj
cd _obj
cmake ..


    pushd ~/foster/compiler/me
    cabal v2-install happy alex
    cabal v2-install --only-dependencies
    popd

make

