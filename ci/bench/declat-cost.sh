#!/usr/bin/env bash
# A SEED'S DECLARATION ADDRESS IS LINEAR IN DEPTH AND BREADTH, as a THUNK-COUNT instrument with
# bounds (den-hoag-mg94o).
#
#   ./ci/bench/declat-cost.sh   -> per-shape readings, then WITHIN BOUND | OVER BOUND | INVALID
#
# The address cost is `flag=true − flag=false` of `declat-cost.nix` (nrThunks), at each size:
#
#   agreement     both flag arms evaluate to the same count  — else a counter is not a reading
#   depth         per chain, the cost's slope (n 200 → 400) at d = 1..4; its THIRD difference
#                 <= DBOUND, so the cost per element is linear in depth
#   spread, fan   the cost's curvature a in f(n) = a n² + b n + c over n = 100/200/400,
#                 a <= ABOUND, so the cost is linear in the definitions a group holds
#   live          the depth cost at d = 1 is > 0, else the flagged arm read no address
#
# Readings at the landing (Nix 2.34.8, Lix 2.95.3 and Determinate 3.22.5 identical): third
# difference −4, spread 0.0, fan 0.0. Recomputing every ancestor per read (the address derived where
# it is read) reads 183, 12.0 and 24.0. `nrThunks` only; no cpu row is read. Exit status is read
# UNPIPED.
set -u
cd "$(dirname "$0")/../.." || exit 99

STATS_DIR=$(mktemp -d)
trap 'rm -rf "$STATS_DIR"' EXIT
DBOUND=16
ABOUND=1

fail=0
note() {
  echo "  $1"
  fail=$((fail + 1))
}

# run <shape> <flag> <d> <n>: "<count> <nrThunks>", or "-1 -1" when the arm failed to evaluate
run() {
  local sp="$STATS_DIR/$1-$2-$3-$4.json" out
  out=$(NIX_SHOW_STATS=1 NIX_SHOW_STATS_PATH="$sp" \
    nix-instantiate --eval --strict --json \
    --argstr shape "$1" --argstr flag "$2" --argstr d "$3" --argstr n "$4" \
    ./ci/bench/declat-cost.nix)
  local rc=$?
  if [ "$rc" -ne 0 ] || [ ! -s "$sp" ]; then
    echo "-1 -1"
    return
  fi
  echo "$out $(python3 -c "import json,sys; print(json.load(open(sys.argv[1]))['nrThunks'])" "$sp")"
}

# cost <shape> <d> <n>: flagged − unflagged nrThunks, or the word INVALID
cost() {
  local con ton coff toff
  read -r con ton <<<"$(run "$1" true "$2" "$3")"
  read -r coff toff <<<"$(run "$1" false "$2" "$3")"
  if [ "$ton" = "-1" ] || [ "$toff" = "-1" ]; then
    echo INVALID
  elif [ "$con" != "$coff" ]; then
    echo INVALID
  else
    echo $((ton - toff))
  fi
}

echo "== depth: per-chain address cost, slope n 200 -> 400 =="
slopes=()
for d in 1 2 3 4; do
  a=$(cost depth "$d" 200)
  b=$(cost depth "$d" 400)
  if [ "$a" = INVALID ] || [ "$b" = INVALID ]; then
    note "INVALID: depth d=$d did not evaluate, or its two flag arms disagree"
    slopes+=(0)
    continue
  fi
  s=$(((b - a) / 200))
  slopes+=("$s")
  printf '  d=%s  n=200 %10s   n=400 %10s   per chain %s\n' "$d" "$a" "$b" "$s"
done
d3=$((slopes[3] - 3 * slopes[2] + 3 * slopes[1] - slopes[0]))
echo "  third difference $d3 (bound $DBOUND)"
[ "${slopes[0]}" -gt 0 ] || note "INVALID: the depth-1 address costs nothing, so the flagged arm read no address"

declare -A curv
for shape in spread fan; do
  echo
  echo "== $shape: address cost at n = 100 / 200 / 400 =="
  f1=$(cost "$shape" 1 100)
  f2=$(cost "$shape" 1 200)
  f4=$(cost "$shape" 1 400)
  if [ "$f1" = INVALID ] || [ "$f2" = INVALID ] || [ "$f4" = INVALID ]; then
    note "INVALID: $shape did not evaluate, or its two flag arms disagree"
    curv[$shape]=0
    continue
  fi
  curv[$shape]=$(python3 -c "import sys; f1,f2,f4=map(int,sys.argv[1:]); print('%.1f' % ((f4 - 3*f2 + 2*f1) / 60000))" "$f1" "$f2" "$f4")
  printf '  %10s %10s %10s   curvature %s thunks per n² (bound %s)\n' "$f1" "$f2" "$f4" "${curv[$shape]}" "$ABOUND"
done

echo
over=""
[ "$d3" -gt "$DBOUND" ] && over="$over depth third difference $d3 > $DBOUND;"
for shape in spread fan; do
  python3 -c "import sys; sys.exit(0 if float(sys.argv[1]) <= float(sys.argv[2]) else 1)" "${curv[$shape]}" "$ABOUND" ||
    over="$over $shape curvature ${curv[$shape]} > $ABOUND;"
done
if [ "$fail" -ne 0 ]; then
  echo "INVALID ($fail readings did not hold)"
  exit 1
elif [ -n "$over" ]; then
  echo "OVER BOUND:$over a declaration address is superlinear"
  exit 6
else
  echo "WITHIN BOUND: third difference $d3 (bound $DBOUND), spread ${curv[spread]}, fan ${curv[fan]} (bound $ABOUND)"
fi
