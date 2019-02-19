#!/usr/bin/env bash

F=$(./random_formula.sh)
OUT="$(cargo run -- $F)"
SMT2=$(echo "$OUT" | grep -v SAT)
RUST=1
Z3=0
if [ "$(echo "$OUT" | grep UNSAT)" == "UNSAT" ]; then
  RUST=1
else
  RUST=0
fi
Z3RES=$(echo "$SMT2" | ~/.bin/z3/bin/z3 -smt2 -in | grep unsat)
if [ "$Z3RES" == "unsat" ]; then
  Z3=1
else
  Z3=0
fi

if [ $Z3 -eq $RUST ]; then
  echo "OK($Z3)"
  exit 0
else
  echo "FAIL ON:"
  echo "$F"
  exit 1
fi
