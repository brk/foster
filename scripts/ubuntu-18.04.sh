#!/bin/sh

set -e
set -x

sudo apt-get install --yes build-essential g++ g++-multilib git gnuplot \
                       python3-pygments python3-matplotlib  python3-scipy python3-sphinx \
                       python3-pandas python3-pip python3-numpy python3-pyqt4 \
                       z3 libdw-dev
sudo apt-get install --yes vim libsparsehash-dev \
              curl exuberant-ctags aptitude libcairo2-dev libc6-dev default-jdk
sudo apt-get install --yes m4 ministat meld \
         linux-tools-virtual linux-tools-generic \
         libffi-dev libedit-dev cmake cmake-curses-gui

    sudo apt-get install --yes libncurses5-dev

  # GMP is needed for GHC to build Cabal from source.
  sudo apt-get install --yes libgmp3-dev libgmp-dev


  # Mercurial from the Ubuntu repositories uses Python 2.7;
  # we need a 3.0-compatible version to successfully build LLDB 9+.
  pip3 install Mercurial dulwich
  hg clone https://dev.heptapod.net/mercurial/hg-git ~/.local/hg-git
  echo "" >> ~/.hgrc
  echo "[extensions]" >> ~/.hgrc
  echo "hggit = ~/.local/hg-git/hggit" >> ~/.hgrc


  # TortoiseHG from source, since the PPA packages have been taken down.
  hg clone https://bitbucket.org/tortoisehg/thg ~/.local/tortoisehg
  # Assuming ~/.local/bin is on $PATH, which it was in Ubuntu MATE 16.04
  mkdir -p ~/.local/bin
  ln -s ~/.local/tortoisehg/thg ~/.local/bin/thg

curl https://beyondgrep.com/ack-2.20-single-file > ~/.local/bin/ack && chmod 0755 ~/.local/bin/ack


  # Python packages, mostly used by benchmarking infrastructure
  pip3 install pyyaml jinja2 statsmodels mpld3 seaborn

  mkdir tmp
  cd tmp
  wget http://thrysoee.dk/editline/libedit-20191025-3.1.tar.gz
  tar xf libedit*.gz
  rm libedit*.gz
  cd libedit*
  ./configure --prefix=$HOME/.local && make -j && make install
  cd ..


  wget http://prdownloads.sourceforge.net/swig/swig-3.0.12.tar.gz
  tar xf swig-*.gz
  rm swig-*.gz
  cd swig-*
  ./configure --prefix=$HOME/.local && make -j && make install
  cd ..

  wget https://downloads.haskell.org/~ghc/8.8.1/ghc-8.8.1-x86_64-deb9-linux-dwarf.tar.xz
  tar xf ghc-*.xz
  rm ghc-*.xz
  cd ghc-* && ./configure --prefix=$HOME/.local/ghc-8.8.1 && make -j install && cd ..

  wget https://downloads.haskell.org/~cabal/cabal-install-latest/cabal-install-3.0.0.0-x86_64-unknown-linux.tar.xz
  tar xf cabal-*.tar.*
  rm cabal-*.tar.*
  mv cabal ~/.local/bin

  # Capnp 0.7.0 exists but produces output that minuproto
  # cannot yet parse, so for now we'll stick to the older version.
  curl -O https://capnproto.org/capnproto-c++-0.6.1.tar.gz
  tar xf capnproto-*.gz
  rm     capnproto-*.gz
  cd capnproto-c++-0.6.1
  ./configure --prefix=$HOME/.local/capnp-c++-0.6.1
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


export PATH=$PATH:$HOME/.local/bin:$HOME/.local/capnp-c++-0.7.0/bin:$HOME/.local/ghc-8.8.1/bin
cabal update

cat ~/.cabal/config | sed 's/-- library-profiling:/library-profiling: True/' > tmp.txt
mv tmp.txt ~/.cabal/config


hg clone https://github.com/brk/sw.git ~/sw

if [ ! -d ~/foster ]; then
  hg clone https://github.com/brk/foster.git ~/foster
fi
#hg clone git+ssh://git@github.com/brk/foster.git ~/foster
hg clone https://github.com/brk/minuproto.git ~/sw/local/minuproto

cd ~/foster/compiler/me
cabal v1-sandbox init
cabal v1-update
cabal v1-sandbox add-source ~/sw/local/minuproto
#If necessary, download source for hoopl and update its version and bounds.
#cabal v1-sandbox add-source ~/sw/local/hoopl-3.10.2.2
cabal v1-install happy alex
cabal v1-install --only-dependencies

echo Okay, starting to install LLVM...
. ~/foster/scripts/install-llvm.sh


pushd ~/foster/third_party/nacl-20110221
echo "Building NaCl, this will take several minutes."
./do
popd

echo Time to build Foster itself!
cd ~/foster
mkdir _obj
cd _obj
cmake .. && make
