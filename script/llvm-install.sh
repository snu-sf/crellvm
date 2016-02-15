#!/bin/bash

JOBS=${1-1}
ROOT=`pwd`
SRCDIR=$ROOT/lib/llvm
OBJDIR=$ROOT/.build/llvm-obj
LOCALDIR=$ROOT/build

cd $OBJDIR
mkdir $LOCALDIR

cmake -DCMAKE_INSTALL_PREFIX=${LOCALDIR} -P cmake_install.cmake
