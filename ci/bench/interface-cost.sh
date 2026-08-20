#!/usr/bin/env bash
# O5 — the per-instance cost of the protocol boundary, as a THUNK-COUNT instrument.
#
#   ./ci/bench/interface-cost.sh   -> per-arm readings, then MEASURED | INVALID
#
# Two arms of one construction (`interface-cost.nix`) at two sizes each. What each must read:
#
#   agreement           the two arms resolve to the SAME config      — else the cheap arm did less work
#   gen marginal        > 0                                          — the engine really folded them
#   exported marginal   > gen marginal                               — the crossing path pays, per type
#   exported marginal   > 0                                          — the crossing path did not vanish
#
# ★ THE ROW IS `nrThunks` AND IT IS NAMED HERE BECAUSE THE ALTERNATIVE IS THEATRE. `cpuTime` moves
# with whatever else the machine is doing and is not comparable between two runs, let alone between
# two machines; thunk counts are deterministic for a fixed expression. This script never reads a cpu
# row and no claim from it may cite one.
#
# ★ MARGINAL, NOT TOTAL: each arm runs at N and 4N and the reading is (big - small) / (4N - N), so a
# fixed set-up overhead cancels and what is left is what ONE MORE TYPE costs. A total-only comparison
# would be satisfied by a constant overhead with no per-instance term, which is not the claim.
#
# ★ AGREEMENT IS CHECKED FIRST AND A DISAGREEMENT IS FATAL, not a footnote. "Fewer thunks" from an arm
# that resolved to something else is not a saving, and an arm that threw would be cheapest of all.
set -u
cd "$(dirname "$0")/../.." || exit 99

STATS_DIR=$(mktemp -d)
trap 'rm -rf "$STATS_DIR"' EXIT

# value <arm> <n> — the resolved config, as JSON. No stats collection, so nothing perturbs it.
value() {
  nix-instantiate --eval --strict --json \
    --argstr arm "$1" --argstr n "$2" ./ci/bench/interface-cost.nix 2>/dev/null
}

# thunks <arm> <n> — the `nrThunks` row for one evaluation. The exit status is read UNPIPED; a `$?`
# after a pipeline reads the pipeline's last stage and is a false green.
thunks() {
  local sp="$STATS_DIR/$1-$2.json"
  NIX_SHOW_STATS=1 NIX_SHOW_STATS_PATH="$sp" \
    nix-instantiate --eval --strict --json \
    --argstr arm "$1" --argstr n "$2" ./ci/bench/interface-cost.nix >/dev/null 2>&1
  local rc=$?
  [ "$rc" -ne 0 ] && { echo "-1"; return; }
  python3 -c "import json,sys; print(json.load(open(sys.argv[1]))['nrThunks'])" "$sp"
}

SMALL=32
BIG=128
STEP=$((BIG - SMALL))

fail=0
note() {
  echo "  $1"
  fail=$((fail + 1))
}

echo "== agreement (the two arms must resolve to the same config) =="
gv=$(value gen "$SMALL")
ev=$(value exported "$SMALL")
if [ -z "$gv" ] || [ -z "$ev" ]; then
  note "INVALID: an arm produced no value at all"
elif [ "$gv" != "$ev" ]; then
  note "INVALID: the arms disagree, so a counter difference is not a cost reading"
else
  echo "  the gen and exported arms resolve identically at n=$SMALL"
fi

echo
echo "== nrThunks (the named row; no cpu row is read) =="
gs=$(thunks gen "$SMALL")
gb=$(thunks gen "$BIG")
es=$(thunks exported "$SMALL")
eb=$(thunks exported "$BIG")
printf '  %-10s n=%-4s %10s   n=%-4s %10s\n' gen "$SMALL" "$gs" "$BIG" "$gb"
printf '  %-10s n=%-4s %10s   n=%-4s %10s\n' exported "$SMALL" "$es" "$BIG" "$eb"

for v in "$gs" "$gb" "$es" "$eb"; do
  [ "$v" = "-1" ] && note "INVALID: an arm failed to evaluate under stats collection"
done

gm=$(((gb - gs) / STEP))
em=$(((eb - es) / STEP))
echo
echo "== marginal thunks per type instance =="
printf '  %-10s %d\n' gen "$gm"
printf '  %-10s %d\n' exported "$em"
printf '  %-10s %d\n' difference "$((em - gm))"

[ "$gm" -gt 0 ] || note "INVALID: the gen arm has no per-instance cost, so it folded nothing"
[ "$em" -gt 0 ] || note "INVALID: the crossing arm costs nothing per instance, so nothing was stamped"
[ "$em" -gt "$gm" ] || note "the crossing path does not cost more per instance than the gen-native one"

echo
if [ "$fail" -eq 0 ]; then
  echo "MEASURED: the foreign protocol costs $((em - gm)) thunks per type instance, and a type that"
  echo "does not cross no longer pays it."
else
  echo "INVALID ($fail readings did not hold)"
  exit 1
fi
