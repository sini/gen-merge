#!/usr/bin/env bash
# A REDECLARATION'S COST PER DECLARING MODULE, as a THUNK-COUNT instrument with a bound.
#
#   ./ci/bench/redeclaration-cost.sh   -> per-arm readings, then WITHIN BOUND | OVER BOUND | INVALID
#
# Two arms of `redeclaration-cost.nix` at two sizes each. What each must read:
#
#   agreement           both arms evaluate                      — else a counter is not a reading
#   leafN marginal      > 0                                     — the engine really collected them
#   sameN - leafN       <= BOUND                                — the redeclaration fold's cost
#
# BOUND is the reading at the landing (Nix 2.34.8): 2 thunks per declaring module. The declaration
# guard forces the key set per declaring module and never the merged record (ADR-0033), so one
# option declared in n modules costs what n options declared once cost, plus the fold's own step.
# The guard re-running the redeclaration fold reads 45 here. `nrThunks` only; no cpu row is read.
# The guard deleted outright ALSO reads within bound, so this row never stands alone: the
# `one-evaluator` stratification cell in `./ci#tests` is its pair.
#
# A second row reads BYTES, which a thunk count cannot see: the published `overridden` list
# (`sameOv`) and the `provenance` of undeclared keys (`provSame`, `provDist`), forced. Each reads
# `log2(bytes(BIG) / bytes(SMALL))` against XBOUND = 1.1; a `++` per step or a `//` accumulator
# reads 1.4 to 1.6 there. Determinate's bytes move in ~256 KiB quanta, so read its exponent, never
# its absolute bytes. Exit status is read UNPIPED.
set -u
cd "$(dirname "$0")/../.." || exit 99

STATS_DIR=$(mktemp -d)
trap 'rm -rf "$STATS_DIR"' EXIT
BOUND=2
XBOUND=1.1

# stat <arm> <n> <field>: the field of NIX_SHOW_STATS, or -1 when the arm failed to evaluate
stat() {
  local sp="$STATS_DIR/$1-$2.json"
  if [ ! -s "$sp" ]; then
    NIX_SHOW_STATS=1 NIX_SHOW_STATS_PATH="$sp" \
      nix-instantiate --eval --strict --json \
      --argstr arm "$1" --argstr n "$2" ./ci/bench/redeclaration-cost.nix >/dev/null
    local rc=$?
    [ "$rc" -ne 0 ] && {
      rm -f "$sp"
      echo "-1"
      return
    }
  fi
  python3 -c "import json,sys; s=json.load(open(sys.argv[1])); print(s['gc']['totalBytes'] if sys.argv[2]=='bytes' else s[sys.argv[2]])" "$sp" "$3"
}

SMALL=1600
BIG=3200
STEP=$((BIG - SMALL))

fail=0
note() {
  echo "  $1"
  fail=$((fail + 1))
}

echo "== nrThunks (the named row; no cpu row is read) =="
ls_=$(stat leafN "$SMALL" nrThunks)
lb=$(stat leafN "$BIG" nrThunks)
ss=$(stat sameN "$SMALL" nrThunks)
sb=$(stat sameN "$BIG" nrThunks)
printf '  %-8s n=%-4s %10s   n=%-4s %10s\n' leafN "$SMALL" "$ls_" "$BIG" "$lb"
printf '  %-8s n=%-4s %10s   n=%-4s %10s\n' sameN "$SMALL" "$ss" "$BIG" "$sb"
for v in "$ls_" "$lb" "$ss" "$sb"; do
  [ "$v" = "-1" ] && {
    note "INVALID: an arm failed to evaluate under stats collection"
    break
  }
done

if [ "$fail" -eq 0 ]; then
  lm=$(((lb - ls_) / STEP))
  sm=$(((sb - ss) / STEP))
  d=$((sm - lm))
  echo
  echo "== marginal thunks per declaring module =="
  printf '  %-22s %d\n' leafN "$lm" sameN "$sm" "redeclaration's cost" "$d"
  [ "$lm" -gt 0 ] || note "INVALID: the leafN arm has no per-module cost, so it collected nothing"
fi

echo
echo "== gc.totalBytes growth exponent, log2(bytes(n=$BIG) / bytes(n=$SMALL)), bound $XBOUND =="
over=""
for arm in sameOv provSame provDist; do
  bs=$(stat "$arm" "$SMALL" bytes)
  bb=$(stat "$arm" "$BIG" bytes)
  if [ "$bs" = "-1" ] || [ "$bb" = "-1" ]; then
    note "INVALID: $arm failed to evaluate under stats collection"
    continue
  fi
  x=$(python3 -c "import math,sys; print('%.2f' % math.log2(int(sys.argv[2]) / int(sys.argv[1])))" "$bs" "$bb")
  printf '  %-8s n=%-4s %12s   n=%-4s %12s   exponent %s\n' "$arm" "$SMALL" "$bs" "$BIG" "$bb" "$x"
  python3 -c "import sys; sys.exit(0 if float(sys.argv[1]) <= float(sys.argv[2]) else 1)" "$x" "$XBOUND" ||
    over="$over $arm=$x"
done

echo
if [ "$fail" -ne 0 ]; then
  echo "INVALID ($fail readings did not hold)"
  exit 1
elif [ "$d" -gt "$BOUND" ] || [ -n "$over" ]; then
  [ "$d" -gt "$BOUND" ] && echo "OVER BOUND: a redeclaration costs $d thunks per declaring module, bound $BOUND"
  [ -n "$over" ] && echo "OVER BOUND: bytes grow super-linearly:$over (bound $XBOUND)"
  exit 6
else
  echo "WITHIN BOUND: a redeclaration costs $d thunks per declaring module (bound $BOUND), and every bytes exponent is <= $XBOUND"
fi
