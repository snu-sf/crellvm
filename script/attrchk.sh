#!/bin/bash

set -e -u

# set clang and opt paths
VALI="$( cd "$( dirname "$0" )" && pwd )"
ROOT="$(dirname $(dirname $VALI))"
BIN=$ROOT/installed/llvm/bin

CMP_ATTR=$VALI/cmp_attrs.native
OPT=$BIN/opt
DIS=$BIN/llvm-dis
AS=$BIN/llvm-as


if [ $# -lt 1 ]
  then echo "usage: ./attrchk.sh a.bc"
fi

filename=$1
tmpname="tmp"

#echo $filename

$DIS $filename -o "$tmpname"1.ll
sed "s/^define\(.*\) readonly /define\1 /g" "$tmpname"1.ll > "$tmpname"2.ll
sed "s/^define\(.*\) readnone /define\1 /g" "$tmpname"2.ll > "$tmpname"3.ll
$OPT -functionattrs "$tmpname"3.ll -o "$tmpname"4.bc
$CMP_ATTR $filename "$tmpname"4.bc
rm "$tmpname"1.ll "$tmpname"2.ll "$tmpname"3.ll "$tmpname"4.bc


# using mkfifo: exception by Llvm.IoError on ($CMP_ATTR $filename "$tmpname"4.bc)

#rm -f "$tmpname"1.ll "$tmpname"2.ll "$tmpname"3.ll "$tmpname"4.bc
#mkfifo "$tmpname"1.ll
#mkfifo "$tmpname"2.ll
#mkfifo "$tmpname"3.ll
#mkfifo "$tmpname"4.bc
#
#$DIS $filename -o "$tmpname"1.ll & \
#sed "s/^define\(.*\) readonly /define\1 /g" "$tmpname"1.ll > "$tmpname"2.ll & \
#sed "s/^define\(.*\) readnone /define\1 /g" "$tmpname"2.ll > "$tmpname"3.ll & \
#$AS < "$tmpname"3.ll | $OPT -functionattrs  > "$tmpname"4.bc & \
#$CMP_ATTR $filename "$tmpname"4.bc
#rm "$tmpname"1.ll "$tmpname"2.ll "$tmpname"3.ll "$tmpname"4.bc
