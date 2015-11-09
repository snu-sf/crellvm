#!/usr/bin/env bash

JOBS=${1-1}
ROOT=`pwd`
VELLVMDIR=$ROOT/lib/vellvm

function check_exit {
if [ "$?" = "0" ]; then
	echo "$1 succeeded."
else
	echo "$1 failed." 1>&2
	exit 1
fi
}

cd $VELLVMDIR

if [ ! -d $VELLVMDIR/lib/metalib-20090714 ]; then
  ./scripts/fetch-libs.sh; check_exit "vellvm/fetch-libs libs"
fi

make libs -j$JOBS; check_exit "vellvm/make libs"
make -j$JOBS; check_exit "vellvm/make"
