# The body of `nixos-bar` (`nixos-bar.nix` sets the NIXOS_BAR_* paths and sources this). Runs every cell's
# two arms, each in its own `nix-instantiate` process, and scores them with `nixos-bar-compare.jq`.
# EXIT: 0 no disagreement · 1 a disagreement · 2 CONTROL FAILED, a broken instrument, never a verdict.
control() {
  echo "nixos-bar: CONTROL FAILED: $*" >&2
  exit 2
}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
base=$NIXOS_BAR_BASE

# admissions <new register>: what `ci/modules-sh-ratchet.sh` will ask to have admitted against the
# committed register, with the hash each trailer names. A RISE also says whether the new gen figure is at
# or under its reference (`parity-now`) and whether the row was above its reference at the anchor
# (`above-at-anchor`): either one makes a `parity` admission valid.
admissions() {
  jq -rn --arg keyform json --slurpfile old "$base" --slurpfile new "$1" -f "$NIXOS_BAR_RATCHET" |
    while IFS=$'\t' read -r key was now; do
      echo "LOWERED $(printf '%s' "$key" | sha256sum | cut -c1-12) $was -> $now $key"
    done
  jq -rn --arg keyform json --arg part rise --slurpfile old "$base" --slurpfile new "$1" -f "$NIXOS_BAR_RATCHET" |
    while IFS=$'\t' read -r key e was now par above; do
      echo "RISE $(printf '%s\t%s' "$key" "$e" | sha256sum | cut -c1-12) $was -> $now parity-now=$par above-at-anchor=$above $key $e"
    done
}

# --fold F LOG...: the register with each log's `PERF` lines merged in. A log with none is a column that
# did not run the arm (or a wrong file), never "no perf".
if [ "${1:-}" = --fold ]; then
  [ $# -ge 3 ] || control "usage: nixos-bar --fold F LOG..."
  out=$2
  shift 2
  for log in "$@"; do
    [ -r "$log" ] || control "cannot read $log"
    n=$(grep -c 'PERF {' "$log" || true)
    [ "$n" -gt 0 ] || control "$log carries no PERF line"
    grep -o 'PERF {.*}$' "$log" | sed 's/^PERF //' >>"$tmp/perf.jsonl"
    echo "nixos-bar: $log: $n PERF lines"
  done
  jq -rn --arg mode fold --slurpfile base "$base" --slurpfile perf "$tmp/perf.jsonl" \
    -f "$NIXOS_BAR_COMPARE" >"$out"
  echo "nixos-bar: wrote $(wc -l <"$out") rows to $out"
  admissions "$out"
  exit 0
fi

# THE EVALUATOR IS RESOLVED ONCE, and never falls back (`modules-sh.nix`'s rule): NIXOS_BAR_EVALUATOR is
# the bin directory that must provide `nix-instantiate`, NIXOS_BAR_EVALUATOR_VERSION the first line of its
# `--version`. Either one unmet is CONTROL FAILED, before any evaluation.
ni=$(command -v nix-instantiate) || control "no nix-instantiate on PATH"
if [ -n "${NIXOS_BAR_EVALUATOR:-}" ] && [ "$ni" != "$NIXOS_BAR_EVALUATOR/nix-instantiate" ]; then
  control "the evaluator is pinned to $NIXOS_BAR_EVALUATOR, but nix-instantiate resolves to $ni"
fi
evl=$("$ni" --version | sed -n 1p)
if [ -n "${NIXOS_BAR_EVALUATOR_VERSION:-}" ] && [ "$evl" != "$NIXOS_BAR_EVALUATOR_VERSION" ]; then
  control "the evaluator is pinned to '$NIXOS_BAR_EVALUATOR_VERSION', but $ni reports '$evl'"
fi
echo "nixos-bar: evaluator $evl ($ni), nixpkgs $NIXOS_BAR_NIXPKGS"

# The whole run has a deadline, checked before each evaluation and bounding the last one.
deadline=$(($(date +%s) + ${NIXOS_BAR_DEADLINE:-3600}))

# evalArm <name> <engine> <cfg> <read> [route]: one evaluation in its own process. Leaves rc set and
# $tmp/<name>.arm holding the arm: {refused, v, err, perf}. `v` is left out for the walk (it is read off
# $tmp/<name>.out by `nixos-bar-docs.jq`).
evalArm() {
  local n=$1 eng=$2 c=$3 r=$4 rt=${5:-[]} t0 ms left perf want
  left=$((deadline - $(date +%s)))
  [ "$left" -gt 0 ] || control "the run passed its deadline before $n"
  [ "$left" -lt 1200 ] || left=1200
  t0=$(date +%s%N)
  rc=0
  # NIX_PATH is emptied: its entries are allocated into every evaluation, so an ambient NIX_PATH moves the
  # attributed bytes the bound is exact on (measured: +112 B per cell on a host with one entry), and no
  # cell reads a `<…>` path. CI's columns run with none, so this is the same count there.
  NIX_PATH="" NIX_SHOW_STATS=1 NIX_SHOW_STATS_PATH="$tmp/$n.stats" timeout -k 10 "$left" "$ni" --eval --strict --json \
    --readonly-mode "$NIXOS_BAR_EVAL" --arg srcs "$NIXOS_BAR_SRCS" --argstr engine "$eng" --argstr cfg "$c" \
    --argstr read "$r" --argstr route "$rt" >"$tmp/$n.out" 2>"$tmp/$n.err" || rc=$?
  ms=$((($(date +%s%N) - t0) / 1000000))
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
# cell <key> <cfg> <read> [claim]: both arms of one cell, appended to the records.
cell() {
  local key=$1 c=$2 r=$3 claim=${4:-} n
  n=$(printf '%s' "$key" | sha256sum | cut -c1-16)
  evalArm "$n-ref" ref "$c" "$r"
  evalArm "$n-gen" gen "$c" "$r"
  jq -cn --argjson key "$key" --arg claim "$claim" --slurpfile ref "$tmp/$n-ref.arm" --slurpfile gen "$tmp/$n-gen.arm" \
    '{key: $key, ref: $ref[0], gen: $gen[0]} + (if $claim == "" then {} else {claim: $claim} end)' >>"$tmp/records.jsonl"
}

: >"$tmp/records.jsonl"
# The docs walk first, so a broken conservation stops the run before the toplevel cells are paid for.
cell '{"kind":"docs-walk"}' docs walk
walk=$(printf '%s' '{"kind":"docs-walk"}' | sha256sum | cut -c1-16)
# CONSERVATION: the reference walk ran to its end and has exactly as many lines as nixpkgs' own list
# over the same options has entries. Off, the walk is not the manual's entry set.
jq -e '.ref.refused | not' "$tmp/records.jsonl" >/dev/null || control "the reference docs walk refused: $(grep -E '^ *error' "$tmp/$walk-ref.err" | tail -1)"
evalArm len ref docs docsLen
[ "$rc" -eq 0 ] || control "the conservation read refused: $(grep -E '^ *error' "$tmp/len.err" | tail -1)"
want=$(jq -r .v "$tmp/len.out")
got=$(jq -r '.v | split("\n") | length' "$tmp/$walk-ref.out")
[ "$got" = "$want" ] || control "conservation: the reference walk has $got nodes, nixpkgs' optionAttrSetToDocList $want entries"
echo "nixos-bar: conservation $got = $want"
cell '{"kind":"options"}' docs options identity
for c in smallContainer tinyContainer ec2 kde xfce gnome pantheon lapp; do
  cell "{\"kind\":\"toplevel\",\"cfg\":\"$c\"}" "$c" toplevel identity
done

# The doc nodes, one record each. gen's walk is empty where it refused, so every node reads gen-absent.
[ -s "$tmp/$walk-gen.out" ] || echo '{"v":""}' >"$tmp/$walk-gen.out"
jq -cn --slurpfile ref "$tmp/$walk-ref.out" --slurpfile gen "$tmp/$walk-gen.out" -f "$NIXOS_BAR_DOCS" >"$tmp/docs.jsonl"
# `tryEval` loses a refusal's message, so each node gen refuses is evaluated again alone, without it,
# for the text its class is read from. It must refuse there too, or the walk's reading was not the node's.
i=0
while IFS= read -r rec; do
  i=$((i + 1))
  evalArm "node-$i" gen docs node "$(jq -c '[.gen.step] + .gen.route' <<<"$rec")"
  [ "$rc" -eq 1 ] || control "doc node $(jq -c .key <<<"$rec") refused in gen's walk but served alone"
  jq -c --rawfile err "$tmp/node-$i.err" '.gen.err = $err' <<<"$rec" >>"$tmp/records.jsonl"
done < <(jq -c 'select(.gen.refused == true)' "$tmp/docs.jsonl")
jq -c 'select(.gen.refused != true)' "$tmp/docs.jsonl" >>"$tmp/records.jsonl"
echo "nixos-bar: $(wc -l <"$tmp/records.jsonl") cells evaluated, $i gen-refused doc nodes read alone"

jq -rs --arg mode perf --arg ev "$evl" --slurpfile base "$base" -f "$NIXOS_BAR_COMPARE" "$tmp/records.jsonl"
if [ "${1:-}" = --write-baseline ]; then
  [ $# -ge 2 ] || control "usage: nixos-bar --write-baseline F"
  jq -rs --arg mode write --arg ev "$evl" --slurpfile base "$base" -f "$NIXOS_BAR_COMPARE" "$tmp/records.jsonl" >"$2"
  echo "nixos-bar: wrote $(wc -l <"$2") rows to $2"
  admissions "$2"
  exit 0
fi
jq -rs --arg mode check --arg ev "$evl" --slurpfile base "$base" -f "$NIXOS_BAR_COMPARE" "$tmp/records.jsonl" >"$tmp/report"
cat "$tmp/report"
tail -1 "$tmp/report" | grep -q '; 0 disagreements$'
