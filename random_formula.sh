#!/usr/bin/env bash
#
#

C=$(($RANDOM % 5))
C=$(($C + 1))
count=1
while [ "$count" -le "$C" ]
do
  L=$(($RANDOM % 5))
  L=$(($L + 2))
  lcount=1
  while [ "$lcount" -le "$L" ]
  do
    v=$(($RANDOM % 3))
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
