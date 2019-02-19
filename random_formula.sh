#!/usr/bin/env bash
#
#

MAX_CLAUSES=10
MAX_LITERALS=3
MAX_VARS=7

C=$(($RANDOM % $MAX_CLAUSES))
C=$(($C + 1))
count=1



while [ "$count" -le "$C" ]
do
  L=$(($RANDOM % $MAX_LITERALS))
  let "L += 1"
  lcount=1
  while [ "$lcount" -le "$L" ]
  do
    v=$(($RANDOM % $MAX_VARS))
    let "v += 1"

    if [ $(($RANDOM % 2)) -ne "0" ]; then
      v="-$v"
    fi
    str="$str $v"
    let "lcount += 1"
  done
  str="$str 0"
  let "count += 1"
done
echo "$str"
