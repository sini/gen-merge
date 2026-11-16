#!/usr/bin/env bash
# THE LEAF FOLD'S CONTEXT UNION, AND THE OUTPUT SLOT OVER `raw`, AGAINST THEIR REFERENCES: a thunk- and
# byte-count instrument with bounds.
#
#   nix develop ./ci --command ./ci/bench/leaf-context-cost.sh   -> per-row readings, then WITHIN BOUND | OVER BOUND | INVALID
#
# Arms of `leaf-context-cost.nix`. What each row must read:
#
#   agreement         every arm evaluates, and returns the key count (or the served string's 1 context)
#   slot vs twin      per added definition per key (N = 3 -> 6, W = 200), on each of the eight shapes: the slot's
#                     nrThunks and bytes are AT OR UNDER nixpkgs' twin's
#   W                 the same on the two context shapes at W = 800
#   depth             per depth level (D = 1 -> 8, N = 2, W = 100): the slot's step is at or under the twin's
#   string length     the leaf fold's gc.totalBytes per added definition (N = 2 -> 6) on a string carrying a
#                     context, at 2^12 and 2^18 characters, on both engines: it does not grow with the length
#                     by more than LBOUND
#
# Bytes are values + envs + sets + list bytes, which counts no string data; gc.totalBytes counts the string
# copies the union could make, so the string-length row reads it. A union folded one concatenation per
# definition copies the whole string at every step and reads ~2^18 bytes per added definition at 2^18
# characters; one concatenation per collapse, copying the head only when the union adds context, reads
# what the unchanged fold does. LBOUND, 16 KiB, sits under that copy by 16x and over the collector's
# quantum divided over four added definitions. Exit status is read UNPIPED.
set -u
cd "$(dirname "$0")/../.." || exit 99
# The counted evaluations are serial (gen-harness `lib.serialEval`, which the ci devshell exports): a count
# is defined only for a serial run. Outside the devshell this refuses, rather than read unpinned.
[ -n "${GEN_SERIAL_EVAL:-}" ] || {
  echo "leaf-context-cost: CONTROL FAILED: GEN_SERIAL_EVAL is unset; run under nix develop ./ci" >&2
  exit 2
}
# shellcheck disable=SC1090
source "$GEN_SERIAL_EVAL"
serialEvalOptions "$(command -v nix-instantiate)" || exit 2
echo "leaf-context-cost: serial options: ${SERIAL_EVAL[*]:-(none)}"

STATS_DIR=$(mktemp -d)
trap 'rm -rf "$STATS_DIR"' EXIT
LBOUND=16384

fail=0
note() {
  echo "  $1"
  fail=$((fail + 1))
}

# run <tag> <want> <argstr pairs...>: evaluates once with statistics on, checks the value, and leaves
# "thunks bytes gcbytes" in $row, or notes INVALID and leaves $row empty
run() {
  local tag=$1 want=$2
  shift 2
  local sp="$STATS_DIR/$tag.json" args=() v rc
  while [ $# -gt 0 ]; do
    args+=(--argstr "$1" "$2")
    shift 2
  done
  v=$(NIX_SHOW_STATS=1 NIX_SHOW_STATS_PATH="$sp" \
    nix-instantiate "${SERIAL_EVAL[@]}" --eval --strict --json "${args[@]}" ./ci/bench/leaf-context-cost.nix)
  rc=$?
  row=""
  if [ "$rc" -ne 0 ]; then
    note "INVALID: $tag exited $rc"
    return
  fi
  if [ "$v" != "$want" ]; then
    note "INVALID: $tag returned '$v', want $want"
    return
  fi
  row=$(python3 -c "import json,sys; s=json.load(open(sys.argv[1])); print(s['nrThunks'], s['values']['bytes']+s['envs']['bytes']+s['sets']['bytes']+s['list']['bytes'], s['gc']['totalBytes'])" "$sp") ||
    note "INVALID: $tag wrote no readable statistics to $sp"
}

# field <row> <1|2|3>
field() { echo "$1" | cut -d' ' -f"$2"; }

over=""
# step <label> <slot-small> <slot-big> <twin-small> <twin-big>: the slot's increment against the twin's
step() {
  local st=$(($(field "$3" 1) - $(field "$2" 1))) sb=$(($(field "$3" 2) - $(field "$2" 2)))
  local tt=$(($(field "$5" 1) - $(field "$4" 1))) tb=$(($(field "$5" 2) - $(field "$4" 2)))
  printf '  %-26s slot %8d t %10d B   twin %8d t %10d B   (B over twin %d)\n' "$1" "$st" "$sb" "$tt" "$tb" "$((sb - tb))"
  [ "$st" -gt 0 ] || note "INVALID: $1 reads no thunk increment, so it collected nothing"
  [ "$st" -le "$tt" ] || over="$over $1:thunks(+$((st - tt)))"
  [ "$sb" -le "$tb" ] || over="$over $1:bytes(+$((sb - tb)))"
}

pair() {
  # pair <label> <w> <n-small> <n-big> <d> <shape>
  local label=$1 w=$2 ns=$3 nb=$4 d=$5 shape=$6 s1 s2 t1 t2
  run "slot-$label-$ns" "$w" arm slot shape "$shape" w "$w" n "$ns" d "$d"
  s1=$row
  run "slot-$label-$nb" "$w" arm slot shape "$shape" w "$w" n "$nb" d "$d"
  s2=$row
  run "twin-$label-$ns" "$w" arm twin shape "$shape" w "$w" n "$ns" d "$d"
  t1=$row
  run "twin-$label-$nb" "$w" arm twin shape "$shape" w "$w" n "$nb" d "$d"
  t2=$row
  if [ -n "$s1" ] && [ -n "$s2" ] && [ -n "$t1" ] && [ -n "$t2" ]; then
    step "$label" "$s1" "$s2" "$t1" "$t2"
  fi
}

echo "== the slot against nixpkgs' twin, per added definition (N = 3 -> 6), W = 200 =="
for shape in leaf list attrs drv drvFresh str strCtx strMix; do
  pair "$shape" 200 3 6 1 "$shape"
done

echo
echo "== the same at W = 800, on the context shapes =="
for shape in strCtx strMix; do
  pair "$shape@W800" 800 3 6 1 "$shape"
done

echo
echo "== per depth level (D = 1 -> 8), N = 2, W = 100 =="
d1s="" d8s="" d1t="" d8t=""
run slot-deep-1 100 arm slot shape deep w 100 n 2 d 1
d1s=$row
run slot-deep-8 100 arm slot shape deep w 100 n 2 d 8
d8s=$row
run twin-deep-1 100 arm twin shape deep w 100 n 2 d 1
d1t=$row
run twin-deep-8 100 arm twin shape deep w 100 n 2 d 8
d8t=$row
if [ -n "$d1s" ] && [ -n "$d8s" ] && [ -n "$d1t" ] && [ -n "$d8t" ]; then
  step "deep D1->D8" "$d1s" "$d8s" "$d1t" "$d8t"
fi

echo
echo "== the leaf fold's gc.totalBytes per added definition (N = 2 -> 6), by string length, bound $LBOUND =="
for site in np gen; do
  for shape in ctx mix; do
    per=()
    for len in 12 18; do
      run "len-$site-$shape-$len-2" 1 arm len site "$site" shape "$shape" n 2 len "$len"
      a=$row
      run "len-$site-$shape-$len-6" 1 arm len site "$site" shape "$shape" n 6 len "$len"
      b=$row
      if [ -n "$a" ] && [ -n "$b" ]; then
        per+=($((($(field "$b" 3) - $(field "$a" 3)) / 4)))
      fi
    done
    if [ "${#per[@]}" -eq 2 ]; then
      g=$((per[1] - per[0]))
      printf '  %-4s %-4s 2^12 %10d B   2^18 %10d B   growth %d\n' "$site" "$shape" "${per[0]}" "${per[1]}" "$g"
      [ "$g" -le "$LBOUND" ] || over="$over len-$site-$shape:+$g"
    fi
  done
done

echo
if [ "$fail" -ne 0 ]; then
  echo "INVALID ($fail readings did not hold)"
  exit 1
elif [ -n "$over" ]; then
  echo "OVER BOUND:$over"
  exit 6
else
  echo "WITHIN BOUND: the slot is at or under nixpkgs' twin on every shape, W and depth row, and the leaf fold's union does not grow with the string's length"
fi
