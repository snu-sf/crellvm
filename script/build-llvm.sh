#!/usr/bin/env bash

JOBS=${1-1}
ROOT=`pwd`
SRCDIR=$ROOT/lib/llvm
OBJDIR=$ROOT/.build/llvm-obj
LOCALDIR=$ROOT/build

function check_exit {
if [ "$?" = "0" ]; then
	echo "$1 succeeded."
else
	echo "$1 failed." 1>&2
	exit 1
fi
}

mkdir -p $OBJDIR
mkdir -p $LOCALDIR

cd $OBJDIR

if [ ! -f $OBJDIR/Makefile ]; then
  cmake $SRCDIR
  #$SRCDIR/configure --prefix=$LOCALDIR --enable-optimized --enable-bindings=ocaml; check_exit "llvm/configure"
fi

#PROJ_INSTALL_ROOT=$LOCALDIR make -j$JOBS; check_exit "llvm/make"
cmake --build .
make ocaml_doc
#make -j$JOBS; check_exit "llvm/make"
#cp bindings/ocaml/llvm/META.llvm bindings/ocaml/llvm/Release/META.llvm
#make install; check_exit "llvm/make install"
