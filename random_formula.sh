#!/usr/bin/env bash
#
#

MAX_CLAUSES=90
MAX_LITERALS=5
MAX_VARS=3

C=$(($RANDOM % $MAX_CLAUSES))
C=$(($C + 1))
count=1



while [ "$count" -le "$C" ]
do
  L=$(($RANDOM % MAX_LITERALS))
  L=$(($L + 2))
  lcount=1
  while [ "$lcount" -le "$L" ]
  do
    v=$(($RANDOM % $MAX_VARS))
    v=$(($v + 1))

    if [ $((RANDOM % 2)) -ne "0" ]; then
      v="-$v"
    fi
    str="$str $v"
    let "lcount += 1"
  done
  str="$str 0"
  let "count += 1"
done
echo "$str"
