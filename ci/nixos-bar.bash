# The body of every replacement-bar runner from stage 2 on: `nixos-bar` (`nixos-bar.nix`, stage 2) and
# `hm-bar` (`hm-bar.nix`, stage 3) set the BAR_* paths, source their stage's `cells` function, and source
# this. It pins the evaluator, runs each evaluation in its own `nix-instantiate` process (`evalArm`), and
# scores the records with `nixos-bar-compare.jq`. What a stage evaluates is its `cells`; the rest is here.
# EXIT: 0 no disagreement · 1 a disagreement · 2 CONTROL FAILED, a broken instrument, never a verdict.
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
# A control failing inside a background evaluation (`par`) exits only that subshell, so it also leaves
# its message where the runner reads it after the wait (`joinAll`).
control() {
  echo "$BAR_NAME: CONTROL FAILED: $*" >&2
  echo "$*" >>"$tmp/control"
  exit 2
}
base=$BAR_BASE

# admissions <new register>: what `ci/modules-sh-ratchet.sh` will ask to have admitted against the
# committed register, with the hash each trailer names. A RISE also says whether the new gen figure is at
# or under its reference (`parity-now`) and whether the row was above its reference at the anchor
# (`above-at-anchor`): either one makes a `parity` admission valid.
admissions() {
  jq -rn --arg keyform json --slurpfile old "$base" --slurpfile new "$1" -f "$BAR_RATCHET" |
    while IFS=$'\t' read -r key was now; do
      echo "LOWERED $(printf '%s' "$key" | sha256sum | cut -c1-12) $was -> $now $key"
    done
  jq -rn --arg keyform json --arg part rise --slurpfile old "$base" --slurpfile new "$1" -f "$BAR_RATCHET" |
    while IFS=$'\t' read -r key e was now par above; do
      echo "RISE $(printf '%s\t%s' "$key" "$e" | sha256sum | cut -c1-12) $was -> $now parity-now=$par above-at-anchor=$above $key $e"
    done
}

# --fold F LOG...: the register with each log's `PERF` lines merged in. A log with none is a column that
# did not run the arm (or a wrong file), never "no perf". A log carries every stage's PERF lines, so only
# this register's keys are read: a line naming a row the register lacks is refused by the compare.
if [ "${1:-}" = --fold ]; then
  [ $# -ge 3 ] || control "usage: $BAR_NAME --fold F LOG..."
  out=$2
  shift 2
  for log in "$@"; do
    [ -r "$log" ] || control "cannot read $log"
    n=$(grep -c "PERF $BAR_NAME {" "$log" || true)
    [ "$n" -gt 0 ] || control "$log carries no PERF $BAR_NAME line"
    grep -o "PERF $BAR_NAME {.*}\$" "$log" | sed "s/^PERF $BAR_NAME //" >>"$tmp/perf.jsonl"
    echo "$BAR_NAME: $log: $n PERF lines"
  done
  jq -rn --arg mode fold --slurpfile base "$base" --slurpfile perf "$tmp/perf.jsonl" \
    -f "$BAR_COMPARE" >"$out"
  echo "$BAR_NAME: wrote $(wc -l <"$out") rows to $out"
  admissions "$out"
  exit 0
fi

# THE EVALUATOR IS RESOLVED ONCE, and never falls back (`modules-sh.nix`'s rule): BAR_EVALUATOR is the bin
# directory that must provide `nix-instantiate`, BAR_EVALUATOR_VERSION the first line of its `--version`.
# Either one unmet is CONTROL FAILED, before any evaluation.
ni=$(command -v nix-instantiate) || control "no nix-instantiate on PATH"
if [ -n "${BAR_EVALUATOR:-}" ] && [ "$ni" != "$BAR_EVALUATOR/nix-instantiate" ]; then
  control "the evaluator is pinned to $BAR_EVALUATOR, but nix-instantiate resolves to $ni"
fi
evl=$("$ni" --version | sed -n 1p)
if [ -n "${BAR_EVALUATOR_VERSION:-}" ] && [ "$evl" != "$BAR_EVALUATOR_VERSION" ]; then
  control "the evaluator is pinned to '$BAR_EVALUATOR_VERSION', but $ni reports '$evl'"
fi
echo "$BAR_NAME: evaluator $evl ($ni), nixpkgs $BAR_NIXPKGS"

# The whole run has a deadline, checked before each evaluation and bounding the last one.
deadline=$(($(date +%s) + ${BAR_DEADLINE:-3600}))

# evalArm <name> <engine> <read> <arg>...: one evaluation in its own process, `--argstr engine <engine>`
# then the stage's own arguments, under the stage's mode flags (BAR_FLAGS). Leaves rc set and
# $tmp/<name>.arm holding the arm: {refused, v, err, perf}. `v` is left out for the walk (it is read off
# $tmp/<name>.out by `nixos-bar-docs.jq`).
evalArm() {
  local n=$1 eng=$2 r=$3 t0 ms left perf want
  shift 3
  left=$((deadline - $(date +%s)))
  [ "$left" -gt 0 ] || control "the run passed its deadline before $n"
  [ "$left" -lt 1200 ] || left=1200
  t0=$(date +%s%N)
  rc=0
  # NIX_PATH is emptied: its entries are allocated into every evaluation, so an ambient NIX_PATH moves the
  # attributed bytes the bound is exact on (measured: +112 B per cell on a host with one entry), and no
  # cell reads a `<…>` path. CI's columns run with none, so this is the same count there.
  # shellcheck disable=SC2086
  NIX_PATH="" NIX_SHOW_STATS=1 NIX_SHOW_STATS_PATH="$tmp/$n.stats" timeout -k 10 "$left" "$ni" --eval --strict --json \
    "${BAR_FLAGS[@]}" "$BAR_EVAL" --arg srcs "$BAR_SRCS" --argstr engine "$eng" "$@" >"$tmp/$n.out" 2>"$tmp/$n.err" || rc=$?
  ms=$((($(date +%s%N) - t0) / 1000000))
  # An evaluation that ran out of its memory, or lost its connection to the store, is the instrument's
  # failure, never a refusal: both read exit 1 (Lix's out-of-memory; every evaluator's broken pipe), with the
  # refusals.
  if grep -qiE 'out of memory|bad_alloc|^ *error: write of [0-9]+ bytes: Broken pipe' "$tmp/$n.err"; then
    control "$n could not be measured (exit $rc): $(grep -iE 'out of memory|bad_alloc|Broken pipe' "$tmp/$n.err" | tail -1)"
  fi
  if [ "$rc" -ne 0 ] && [ "$rc" -ne 1 ]; then
    [ "$(date +%s)" -lt "$deadline" ] || control "the run passed its deadline in $n"
    control "$n exited $rc, neither 0 nor 1: $(grep -E '^ *error' "$tmp/$n.err" | tail -1)"
  fi
  perf=null
  if [ "$rc" -eq 0 ]; then
    # A served arm has its stats file and non-zero counters; a refused one writes none (all three evaluators).
    [ -s "$tmp/$n.stats" ] || control "$n exited 0 but wrote no stats file"
    perf=$(jq -c --argjson ms "$ms" '{thunks: .nrThunks, bytes: ([.envs, .list, .sets, .values, .symbols] | map(.bytes) | add), ms: $ms}
      | if .thunks > 0 and .bytes > 0 then . else error("a zero counter") end' "$tmp/$n.stats") ||
      control "$n: unreadable stats $tmp/$n.stats"
    # The arm ran the engine it names: gen-merge's evaluation answers a field nixpkgs' does not.
    want=false
    [ "$eng" = ref ] || want=true
    [ "$(jq -r .gen "$tmp/$n.out")" = "$want" ] || control "$n: the $eng arm did not run $eng (control answered $(jq -r .gen "$tmp/$n.out"))"
  fi
  jq -cn --argjson rc "$rc" --argjson perf "$perf" --rawfile err "$tmp/$n.err" \
    --argjson v "$(if [ "$rc" -eq 0 ] && [ "$r" != walk ]; then jq -c .v "$tmp/$n.out"; else echo null; fi)" \
    '{refused: ($rc == 1), v: $v, err: $err, perf: $perf}' >"$tmp/$n.arm"
}
# cell <key> <read> <claim, or ""> <arg>...: both arms of one cell, appended to the records.
cell() {
  local key=$1 r=$2 claim=$3 n
  shift 3
  n=$(printf '%s' "$key" | sha256sum | cut -c1-16)
  evalArm "$n-ref" ref "$r" "$@"
  evalArm "$n-gen" gen "$r" "$@"
  jq -cn --argjson key "$key" --arg claim "$claim" --slurpfile ref "$tmp/$n-ref.arm" --slurpfile gen "$tmp/$n-gen.arm" \
    '{key: $key, ref: $ref[0], gen: $gen[0]} + (if $claim == "" then {} else {claim: $claim} end)' >>"$tmp/records.jsonl"
}

# par <command>...: run it in the background, at most BAR_JOBS at once (default: the host's cores).
# joinAll: wait for every one, then stop if any of them failed a control.
par() {
  while [ "$(jobs -rp | wc -l)" -ge "${BAR_JOBS:-$(nproc)}" ]; do wait -n || true; done
  "$@" &
}
joinAll() {
  wait || true
  [ ! -s "$tmp/control" ] || exit 2
}

# docsWalk <walk key> <set, or ""> <args-of>: the docs walk, its conservation read and one record per
# node. `<args-of> <read> <route>` prints, one per line, the stage's arguments for that read (`wargs`).
# The walk runs first in a stage, so a broken conservation stops the run before the rest is paid for.
docsWalk() {
  local wk=$1 set=$2 args=$3 walk want got rec
  local -a a
  mapfile -t a < <("$args" walk '[]')
  cell "$wk" walk "" "${a[@]}"
  walk=$(printf '%s' "$wk" | sha256sum | cut -c1-16)
  # CONSERVATION: the reference walk ran to its end and has exactly as many lines as nixpkgs' own list
  # over the same options has entries. Off, the walk is not the manual's entry set.
  jq -e '.ref.refused | not' <(tail -1 "$tmp/records.jsonl") >/dev/null ||
    control "the reference docs walk $wk refused: $(grep -E '^ *error' "$tmp/$walk-ref.err" | tail -1)"
  mapfile -t a < <("$args" docsLen '[]')
  evalArm "len-$walk" ref docsLen "${a[@]}"
  [ "$rc" -eq 0 ] || control "the conservation read of $wk refused: $(grep -E '^ *error' "$tmp/len-$walk.err" | tail -1)"
  want=$(jq -r .v "$tmp/len-$walk.out")
  got=$(jq -r '.v | split("\n") | length' "$tmp/$walk-ref.out")
  [ "$got" = "$want" ] || control "conservation $wk: the reference walk has $got nodes, nixpkgs' optionAttrSetToDocList $want entries"
  echo "$BAR_NAME: conservation $wk $got = $want"
  # The doc nodes, one record each. gen's walk is empty where it refused, so every node reads gen-absent.
  [ -s "$tmp/$walk-gen.out" ] || echo '{"v":""}' >"$tmp/$walk-gen.out"
  jq -cn --arg set "$set" --slurpfile ref "$tmp/$walk-ref.out" --slurpfile gen "$tmp/$walk-gen.out" \
    -f "$BAR_DOCS" >"$tmp/docs-$walk.jsonl"
  # `tryEval` loses a refusal's message, so each node gen refuses is evaluated again alone, without it,
  # for the text its class is read from. It must refuse there too, or the walk's reading was not the node's.
  while IFS= read -r rec; do
    nodes=$((nodes + 1))
    mapfile -t a < <("$args" node "$(jq -c '[.gen.step] + .gen.route' <<<"$rec")")
    evalArm "node-$nodes" gen node "${a[@]}"
    [ "$rc" -eq 1 ] || control "doc node $(jq -c .key <<<"$rec") refused in gen's walk but served alone"
    jq -c --rawfile err "$tmp/node-$nodes.err" '.gen.err = $err' <<<"$rec" >>"$tmp/records.jsonl"
  done < <(jq -c 'select(.gen.refused == true)' "$tmp/docs-$walk.jsonl")
  jq -c 'select(.gen.refused != true)' "$tmp/docs-$walk.jsonl" >>"$tmp/records.jsonl"
}

: >"$tmp/records.jsonl"
nodes=0
cells
echo "$BAR_NAME: $(wc -l <"$tmp/records.jsonl") cells evaluated, $nodes gen-refused doc nodes read alone"

jq -rs --arg mode perf --arg label "$BAR_NAME" --arg ev "$evl" --slurpfile base "$base" -f "$BAR_COMPARE" "$tmp/records.jsonl"
if [ "${1:-}" = --write-baseline ]; then
  [ $# -ge 2 ] || control "usage: $BAR_NAME --write-baseline F"
  jq -rs --arg mode write --arg ev "$evl" --slurpfile base "$base" -f "$BAR_COMPARE" "$tmp/records.jsonl" >"$2"
  echo "$BAR_NAME: wrote $(wc -l <"$2") rows to $2"
  admissions "$2"
  exit 0
fi
jq -rs --arg mode check --arg label "$BAR_NAME" --arg ev "$evl" --slurpfile base "$base" -f "$BAR_COMPARE" "$tmp/records.jsonl" >"$tmp/report"
cat "$tmp/report"
tail -1 "$tmp/report" | grep -q '; 0 disagreements$'
