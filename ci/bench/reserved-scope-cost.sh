#!/usr/bin/env bash
# THE RESERVATION SCOPE'S COST PER SCOPED ENTRY, as a THUNK-COUNT instrument with a bound.
#
#   ./ci/bench/reserved-scope-cost.sh   -> per-arm readings, then WITHIN BOUND | OVER BOUND | INVALID
#
# Two arms of one construction (`reserved-scope-cost.nix`) at two sizes each. What each must read:
#
#   agreement           the two arms resolve to the SAME config      — else the cheap arm did less work
#   plain marginal      > 0                                          — the engine really collected them
#   scoped - plain      > 0                                          — the scope really ran
#   scoped - plain      <= BOUND                                     — the scoped path's cost property
#
# BOUND is the reading at the landing (Nix 2.34.8): 15 thunks per scoped entry, of which the
# malformed-marker check is 6 and the scope and its key read are 9. The hub perf bench gates the
# off-scope path and reaches no scoped entry, so this is the scoped path's only meter. `nrThunks`
# only; no cpu row is read. Exit status is read UNPIPED.
set -u
cd "$(dirname "$0")/../.." || exit 99

STATS_DIR=$(mktemp -d)
trap 'rm -rf "$STATS_DIR"' EXIT
BOUND=15

value() {
  nix-instantiate --eval --strict --json \
    --argstr arm "$1" --argstr n "$2" ./ci/bench/reserved-scope-cost.nix
}

thunks() {
  local sp="$STATS_DIR/$1-$2.json"
  NIX_SHOW_STATS=1 NIX_SHOW_STATS_PATH="$sp" \
    nix-instantiate --eval --strict --json \
    --argstr arm "$1" --argstr n "$2" ./ci/bench/reserved-scope-cost.nix >/dev/null
  local rc=$?
  [ "$rc" -ne 0 ] && { echo "-1"; return; }
  python3 -c "import json,sys; print(json.load(open(sys.argv[1]))['nrThunks'])" "$sp"
}

SMALL=100
BIG=400
STEP=$((BIG - SMALL))

fail=0
note() {
  echo "  $1"
  fail=$((fail + 1))
}

echo "== agreement (the two arms must resolve to the same config) =="
pv=$(value plain "$SMALL")
sv=$(value scoped "$SMALL")
if [ -z "$pv" ] || [ -z "$sv" ]; then
  note "INVALID: an arm produced no value at all"
elif [ "$pv" != "$sv" ]; then
  note "INVALID: the arms disagree, so a counter difference is not a cost reading"
else
  echo "  the plain and scoped arms resolve identically at n=$SMALL"
fi

echo
echo "== nrThunks (the named row; no cpu row is read) =="
ps=$(thunks plain "$SMALL")
pb=$(thunks plain "$BIG")
ss=$(thunks scoped "$SMALL")
sb=$(thunks scoped "$BIG")
printf '  %-8s n=%-4s %10s   n=%-4s %10s\n' plain "$SMALL" "$ps" "$BIG" "$pb"
printf '  %-8s n=%-4s %10s   n=%-4s %10s\n' scoped "$SMALL" "$ss" "$BIG" "$sb"
for v in "$ps" "$pb" "$ss" "$sb"; do
  [ "$v" = "-1" ] && { note "INVALID: an arm failed to evaluate under stats collection"; break; }
done

if [ "$fail" -eq 0 ]; then
  pm=$(((pb - ps) / STEP))
  sm=$(((sb - ss) / STEP))
  d=$((sm - pm))
  echo
  echo "== marginal thunks per imported entry =="
  printf '  %-14s %d\n' plain "$pm" scoped "$sm" "scope's cost" "$d"
  [ "$pm" -gt 0 ] || note "INVALID: the plain arm has no per-entry cost, so it collected nothing"
  [ "$d" -gt 0 ] || note "INVALID: the scoped arm costs nothing more, so the scope did not run"
fi

echo
if [ "$fail" -ne 0 ]; then
  echo "INVALID ($fail readings did not hold)"
  exit 1
elif [ "$d" -gt "$BOUND" ]; then
  echo "OVER BOUND: the scope costs $d thunks per scoped entry, bound $BOUND"
  exit 6
else
  echo "WITHIN BOUND: the scope costs $d thunks per scoped entry (bound $BOUND)"
fi
