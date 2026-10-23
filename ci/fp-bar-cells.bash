# Stage 4's cells (den-hoag-stage4-flake-parts-3qh4l, `fp-bar.nix`), run by the shared body `nixos-bar.bash`.
#
# MODE: stage 3's. `--read-write-mode` (the flakes' path literals are copied into the store), import from
# derivation off (no builds), restricted evaluation with no allowed URI (no network), `-I /nix/store` for the
# store paths the sources arrive as.
BAR_FLAGS=(--read-write-mode --option allow-import-from-derivation false --option restrict-eval true --option allowed-uris "" -I /nix/store)
# `--write-baseline` writes the register this run's cells define, so the conservation against the committed one
# is not read there.
fpWrite=${1:-}
# The poison engine's token, generated fresh per run and never written down, so no text a cell or a document
# carries can be mistaken for a firing.
token="fp-bar-poison-$(head -c 12 /dev/urandom | od -An -tx1 | tr -d ' \n')"

# THE KINDS ARE DISJOINT. The compare's `perfKind` and `identityKind` gained this stage's kinds, so a row of
# stages 1-3 can move under that edit only if it carries one of them. Each register must answer at least one kind
# (a census that reads nothing is a broken instrument, never a clean one).
kinds() {
  local f k
  local -a regs
  read -ra regs <<<"$BAR_OTHER_REGISTERS"
  [ "${#regs[@]}" -eq 3 ] || control "BAR_OTHER_REGISTERS names ${#regs[@]} registers, not stages 1-3's 3"
  for f in "${regs[@]}"; do
    k=$(jq -rs 'map(.key.kind) | unique | join(",")' "$f") || control "cannot read the kinds of $f"
    [ -n "$k" ] || control "$f answered no kind"
    jq -ne --arg k "$k" '$k | split(",") | any(IN("unit", "memo", "template", "flake", "flake-drv")) | not' >/dev/null ||
      control "$f carries a stage-4 kind ($k): the compare's kind lists would move its rows"
  done
  echo "$BAR_NAME: stages 1-3's registers carry none of this stage's kinds"
}

# unitArm <name>: a unit's arm off its `tryEval` read. Served: `v` is the hash. Caught: refused, `caught`, no `v`.
# Refused uncatchably (the process exited 1): evalArm's arm, not caught. `unit`, flake-parts' own verdict, rides
# beside the value as evidence; the compare never reads it.
unitArm() {
  jq -c --slurpfile o "$tmp/$1.out" '
    if .refused then . + { caught: false }
    elif $o[0].v.ok == null then . + { refused: true, caught: true, v: null, unit: $o[0].v.unit }
    else . + { v: $o[0].v.ok, unit: $o[0].v.unit } end' "$tmp/$1.arm"
}
# poisoned <name> <what>: the poison read refused with this run's token, so the seam reached what it read. One
# that serves fails evalArm's control (it answers no `gen`); one refusing with another text reached something else.
poisoned() {
  jq -e --arg t "$token" '.refused and (.err | contains($t))' "$tmp/$1.arm" >/dev/null ||
    control "$2: the poison read did not refuse with the run's token, so the seam did not reach it: $(grep -E '^ *error' "$tmp/$1.err" | tail -1)"
}
# served <name> <what>: the reference serves every cell (else the tip set does not evaluate together).
served() {
  jq -e '.refused | not' "$tmp/$1.arm" >/dev/null || control "the reference refused $2: $(grep -E '^ *error' "$tmp/$1.err" | tail -1)"
}

cells() {
  local jobs i e n t f p key want mem s0
  local -a units tpls planes
  kinds
  mem=$(($(awk '/^MemTotal:/ { print $2 }' /proc/meminfo) * 1024))

  # PHASE 1, the suite: units, the memo check, the templates and their poison reads, up to BAR_JOBS processes at
  # once (default: the host's cores), each under a GC heap of BAR_HEAP bytes (default: the host's memory over
  # BAR_JOBS); an evaluation that exceeds it is CONTROL FAILED (`evalArm`), never a verdict.
  jobs=${BAR_JOBS:-$(nproc)}
  export GC_MAXIMUM_HEAP_SIZE=${BAR_HEAP:-$((mem / jobs))}
  s0=$(date +%s)
  echo "$BAR_NAME: phase 1: $jobs processes at once, each under a GC heap of $GC_MAXIMUM_HEAP_SIZE bytes"
  evalArm names ref names --argstr read names
  [ "$rc" -eq 0 ] || control "the unit names read refused: $(grep -E '^ *error' "$tmp/names.err" | tail -1)"
  mapfile -t units < <(jq -c '.v[]' "$tmp/names.out")
  n=${#units[@]}
  [ "$n" -gt 0 ] || control "the unit names read answered no unit"
  # CONSERVATION: the suite's units are the register's unit rows.
  if [ "$fpWrite" != --write-baseline ]; then
    want=$(jq -s 'map(select(.key.kind == "unit")) | length' "$base")
    [ "$n" = "$want" ] || control "conservation: flake-parts' suite collects $n units, the register holds $want unit rows"
  fi
  evalArm templates ref templates --argstr read templates
  [ "$rc" -eq 0 ] || control "the template names read refused: $(grep -E '^ *error' "$tmp/templates.err" | tail -1)"
  mapfile -t tpls < <(jq -r '.v[]' "$tmp/templates.out")
  [ "${#tpls[@]}" -gt 0 ] || control "the template names read answered no template"
  for ((i = 0; i < n; i++)); do
    for e in ref gen; do par evalArm "u$i-$e" "$e" unit --argstr read unit --argstr path "${units[i]}"; done
  done
  for e in ref gen; do par evalArm "memo-$e" "$e" memo --argstr read memo; done
  for t in "${tpls[@]}"; do
    for e in ref gen; do par evalArm "t-$t-$e" "$e" template --argstr read template --argstr name "$t"; done
    par evalArm "t-$t-poison" poison template --argstr read template --argstr name "$t" --argstr token "$token"
  done
  joinAll

  # A unit gen refuses under `tryEval` where the reference serves is read again alone, without it, for the text
  # (it must refuse there too). A unit both arms refuse under `tryEval` is read again alone on each arm with
  # `--show-trace`, for the shared throw's `trace` (`nixos-bar-compare.jq`); `caught` is its `tryEval` read.
  for ((i = 0; i < n; i++)); do
    for e in ref gen; do unitArm "u$i-$e" >"$tmp/u$i-$e.a"; done
    # flake-parts' own verdict on the reference is true on every unit, or the reference fails its own suite.
    jq -e '(.refused | not) or .caught' "$tmp/u$i-ref.a" >/dev/null && jq -e '.unit == true' "$tmp/u$i-ref.a" >/dev/null ||
      control "flake-parts' own verdict on the reference is not true for unit ${units[i]}: the reference tree fails its own suite"
    if jq -se '.[0].caught == true and .[1].caught == true' "$tmp/u$i-ref.a" "$tmp/u$i-gen.a" >/dev/null; then
      for e in ref gen; do par evalArm "u$i-$e-x" "$e" unitRaw --argstr read unitRaw --argstr path "${units[i]}" --show-trace; done
    elif jq -e '.caught == true' "$tmp/u$i-gen.a" >/dev/null; then
      par evalArm "u$i-gen-r" gen unitRaw --argstr read unitRaw --argstr path "${units[i]}"
    fi
  done
  joinAll
  for ((i = 0; i < n; i++)); do
    if [ -e "$tmp/u$i-ref-x.arm" ]; then
      for e in ref gen; do
        jq -e .refused "$tmp/u$i-$e-x.arm" >/dev/null || control "unit ${units[i]} refused under tryEval on both arms but its traced $e read served"
        jq -c --rawfile tr "$tmp/u$i-$e-x.err" '. + { err: $tr, trace: $tr }' "$tmp/u$i-$e.a" >"$tmp/u$i-$e.b"
        mv "$tmp/u$i-$e.b" "$tmp/u$i-$e.a"
      done
    elif [ -e "$tmp/u$i-gen-r.arm" ]; then
      jq -e .refused "$tmp/u$i-gen-r.arm" >/dev/null || control "unit ${units[i]} refused under tryEval on gen but served alone"
      jq -c --rawfile err "$tmp/u$i-gen-r.err" '.err = $err' "$tmp/u$i-gen.a" >"$tmp/u$i-gen.b"
      mv "$tmp/u$i-gen.b" "$tmp/u$i-gen.a"
    fi
    jq -cn --argjson p "${units[i]}" --slurpfile ref "$tmp/u$i-ref.a" --slurpfile gen "$tmp/u$i-gen.a" \
      '{ key: { kind: "unit", path: $p }, ref: $ref[0], gen: $gen[0] }' >>"$tmp/records.jsonl"
  done

  # THE MEMO CELL's value is `{result, traces}`: `traces` is read off each arm's stderr, the count of lines
  # carrying the literal upstream's own check counts, and spliced into the value before the compare. The
  # reference reads exactly 1, or the instrument is broken (0 is a literal that matches nothing, never a pass).
  for e in ref gen; do
    t=$(grep -cF -- "$BAR_MEMO_LITERAL" "$tmp/memo-$e.err" || true)
    jq -c --argjson c "$t" 'if .refused then . else .v = { result: .v, traces: $c } end' "$tmp/memo-$e.arm" >"$tmp/memo-$e.a"
  done
  served memo-ref "the memo cell"
  jq -e '.v.traces == 1' "$tmp/memo-ref.a" >/dev/null ||
    control "the reference memo read counts $(jq .v.traces "$tmp/memo-ref.a") lines carrying '$BAR_MEMO_LITERAL', not 1: a broken instrument"
  jq -cn --slurpfile ref "$tmp/memo-ref.a" --slurpfile gen "$tmp/memo-gen.a" \
    '{ key: { kind: "memo" }, ref: $ref[0], gen: $gen[0] }' >>"$tmp/records.jsonl"

  for t in "${tpls[@]}"; do
    served "t-$t-ref" "template $t"
    poisoned "t-$t-poison" "template $t"
    jq -cn --arg t "$t" --slurpfile ref "$tmp/t-$t-ref.arm" --slurpfile gen "$tmp/t-$t-gen.arm" \
      '{ key: { kind: "template", name: $t }, ref: $ref[0], gen: $gen[0] }' >>"$tmp/records.jsonl"
  done
  echo "$BAR_NAME: phase 1: $n units, the memo cell, ${#tpls[@]} templates (${tpls[*]}) and their poison reads, $(($(date +%s) - s0)) s"

  # PHASE 2, the real flakes, ONE EVALUATION AT A TIME, under a GC heap of the host's memory less 2 GiB of
  # headroom (BAR_HEAP overrides it), so `evalArm`'s out-of-memory control, not the kernel, decides an
  # evaluation that outgrows it. Each flake's `names` read is evaluated once more on the poison engine.
  export GC_MAXIMUM_HEAP_SIZE=${BAR_HEAP:-$((mem - 2147483648))}
  s0=$(date +%s)
  echo "$BAR_NAME: phase 2: 1 process at a time, under a GC heap of $GC_MAXIMUM_HEAP_SIZE bytes"
  for f in $(jq -r '.flakes | keys[]' "$BAR_SRCS"); do
    mapfile -t planes < <(jq -r --arg f "$f" '.flakes[$f].planes[]' "$BAR_SRCS")
    for p in "${planes[@]}"; do
      if [ "$p" = names ]; then
        key=$(jq -cn --arg f "$f" '{ kind: "flake", flake: $f, plane: "names" }')
        cell "$key" flake "" --argstr read flake --argstr flake "$f" --argstr plane "$p"
      else
        key=$(jq -cn --arg f "$f" --arg p "$p" '{ kind: "flake-drv", flake: $f, plane: $p }')
        cell "$key" flake identity --argstr read flake --argstr flake "$f" --argstr plane "$p"
      fi
      served "$(printf '%s' "$key" | sha256sum | cut -c1-16)-ref" "$key"
    done
    evalArm "f-$f-poison" poison flake --argstr read flake --argstr flake "$f" --argstr plane names --argstr token "$token"
    poisoned "f-$f-poison" "real flake $f"
  done
  echo "$BAR_NAME: phase 2: $(jq -r '[.flakes[].planes | length] | add' "$BAR_SRCS") real-flake cells over $(jq -r '.flakes | keys | join(", ")' "$BAR_SRCS") and their poison reads, $(($(date +%s) - s0)) s"
}
