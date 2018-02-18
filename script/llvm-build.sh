#!/usr/bin/env bash

ROOT=`pwd`
SRCDIR=$ROOT/lib/llvm
OBJDIR=$ROOT/.build/llvm-obj

function check_exit {
if [ "$?" = "0" ]; then
	echo "$1 succeeded."
else
	echo "$1 failed." 1>&2
	exit 1
fi
}

mkdir -p $OBJDIR

cd $OBJDIR

if [ ! -f $OBJDIR/Makefile ]; then
  cmake $SRCDIR -DCMAKE_BUILD_TYPE=Release
fi

cmake --build . -- -j$1
make ocaml_doc
#make -j$JOBS; check_exit "llvm/make"
#cp bindings/ocaml/llvm/META.llvm bindings/ocaml/llvm/Release/META.llvm
#make install; check_exit "llvm/make install"
