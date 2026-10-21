#!/usr/bin/env bash
# THE RATCHET GUARD (den-hoag-06toi, den-hoag-fwkzx): a replacement-bar register never lowers the bar
# silently. The property is about HISTORY, not a tree — a regression written into a register by
# `--write-baseline` reads green against itself — so this walks every revision of each register on HEAD's
# first-parent history and compares each with its predecessor (`modules-sh-ratchet.jq`). The registers,
# each with its id form and its decrease-trailer key (`registers` below):
#
#   ci/modules-sh-baseline.jsonl   stage 1, `Modules-Sh-Decrease:`
#   ci/nixos-bar-baseline.jsonl    stage 2, `Nixos-Bar-Decrease:`, perf rises `Bar-Perf-Rise:`
#
# Each fallen key must be ADMITTED by its register's decrease trailer, naming the key's hash, on a commit
# after the older revision (up to HEAD, so a later commit can admit a fall that already landed; a trailer
# never admits a later fall):
#
#   <Decrease>: <hash> relock den-hoag-<census row>
#       admitted only if nixpkgs' lock node moved between the two revisions: upstream moved the bar,
#       and the key's failure enters the census (den-hoag-uccyi, rx8sv rule 4);
#   <Decrease>: <hash> correction <reason>
#       a register correction (a class row that was wrong-class, say), with its reason.
#
# Any other fall is a regression of a working cell (rx8sv rule 2) and refuses.
#
# THE PERF CLAUSE (a register with a perf trailer key). A RISE of a committed gen `thunks` or `bytes`
# (ADR-0032's EXACT bound; a lowering needs no admission) must be admitted by `Bar-Perf-Rise: <hash>
# <class>`, the hash being that of `<id>\t<evaluator>`, under one of ADR-0032's authorization classes:
#
#   reanchor             admitted only if the ENVIRONMENT moved and nothing under test did: nixpkgs' lock
#                        node moved AND every gen member lock node (owner sini, repo gen-*), gen-merge's
#                        own lib/, and the gen arm's ci/ inputs (ci/modules-sh-lib.nix,
#                        ci/nixos-bar-eval.nix, ci/nixos-bar.bash) are unchanged between the two
#                        revisions. ADR-0032: a bound re-anchors
#                        "only when the environment moves — the evaluator or a REFERENCE pin … and never
#                        on a gen member pin, which is the change under test". An evaluator move needs no
#                        trailer: the perf entry is keyed by the evaluator's `--version` line, so a new
#                        evaluator is a new anchor, never a rise.
#   parity               ADR-0032 as written: "A rise on a gated cost row is authorized, whether constant or
#                        marginal, when it does not move the row across parity with its reference arm. A
#                        row already above its reference at the anchor may rise and stays authorized."
#                        Admitted if the new gen figure is <= the new ref figure on both counters, OR the
#                        row was already above its reference at the anchor (the older revision). The
#                        second arm is the passage's own reading ("orchestrator, defaulted, reversible").
#   floor den-hoag-<row> the correctness floor, its attribution the cited row;
#   owner den-hoag-<row> an owner reading.
#
# Every trailer in range naming a key's hash is read, and any valid one admits it, so a later trailer for
# the same key (another change's, of a class that does not hold there) never shadows a valid one.
#
# `nixos-bar --write-baseline` and `--fold` print every hash a change needs. Git reads trailers from a
# message's LAST paragraph only, so all of a commit's trailers go in one paragraph (one `-m`).
#
# A FORCE-PUSH rewrites the history this walks, so on a GitHub push event with `forced: true` two more
# reads run against the history the push replaced (`before`): its own register revisions that HEAD no
# longer carries are walked the same way (a fall a squash erased stays a fall), and its tip's register
# is compared with HEAD's (a squash that lowers the bar is a fall). Off GitHub there is no event file
# and this arm does not run.
#
# WHAT THIS DOES NOT DECIDE, read by the landing's review instead:
# - whether the named census row exists, or a correction's reason is right: the trailer is the record;
# - which change a relock admission covers: it is as wide as the gap between two register revisions,
#   so once nixpkgs moved anywhere in that gap, a gen-merge regression landed in it with a `relock`
#   trailer is admitted too (a `reanchor` is not that wide: it refuses on any gen pin, lib/ or arm-input move);
# - its own edits: it runs from HEAD's tree, so a commit that weakens this file or
#   `modules-sh-ratchet.jq`, or moves a register and edits `registers` with it, escapes it. Review reads
#   every diff to `ci/modules-sh-ratchet.*` and to `registers`.
#
# Needs git and jq, never an evaluator. Run from the repository root:  bash ci/modules-sh-ratchet.sh
# EXIT: 0 every fall admitted · 1 REFUSED, naming each key · 2 CONTROL FAILED, history not read.
set -euo pipefail
# <register> <id form> <decrease-trailer key> <perf-rise trailer key, or ->
registers=(
  "ci/modules-sh-baseline.jsonl legacy Modules-Sh-Decrease -"
  "ci/nixos-bar-baseline.jsonl json Nixos-Bar-Decrease Bar-Perf-Rise"
)
here=$(dirname "$0")
control() {
  echo "modules-sh-ratchet: CONTROL FAILED: $*" >&2
  exit 2
}
if [ "$(git rev-parse --is-shallow-repository)" = true ]; then
  # CI checks out at depth 1; the property needs the register's whole history.
  git fetch --quiet --unshallow origin || control "could not unshallow"
fi
# A lock whose nixpkgs is not a node-name string (a follows path, say) is unreadable, never "moved".
nixpkgsAt() {
  git show "$1:ci/flake.lock" |
    jq -er '.nodes[.nodes.root.inputs.nixpkgs | strings].locked | (.rev // .narHash) | strings' ||
    control "cannot read nixpkgs' lock node at ${1:0:9}"
}
# Everything under test at a revision: every gen member lock node's rev, and gen-merge's own lib/ tree.
underTestAt() {
  git show "$1:ci/flake.lock" |
    jq -erc '[.nodes[] | .locked // {} | select(.owner == "sini" and (.repo // "" | startswith("gen-"))) | "\(.repo)@\(.rev)"] | unique | if length > 0 then . else error("no gen member node") end' ||
    control "cannot read the gen member lock nodes at ${1:0:9}"
  git rev-parse "$1:lib" || control "cannot read lib/ at ${1:0:9}"
  # The gen arm's own inputs in ci/: the file that wires evalModuleTree in, the evaluation, and the runner
  # whose argv is allocated into every evaluation's bytes. None of them is environment.
  local f
  for f in ci/modules-sh-lib.nix ci/nixos-bar-eval.nix ci/nixos-bar.bash; do
    git rev-parse "$1:$f" || control "cannot read $f at ${1:0:9}"
  done
}
hashOf() { printf '%s' "$1" | sha256sum | cut -c1-12; }
refused=0 checked=0
summary=""
# judge <label> <old rev> <old register spec> <new rev> <trailer range>…: the falls (and perf rises) from
# the old register to <new rev>'s, each needing an admission among the trailers of the ranges.
judge() {
  local label=$1 old=$2 oldSpec=$3 new=$4 fallen rises trailers="" ptrailers="" r a b ua ub moved env key was now h adm why c e par above cands
  shift 4
  checked=$((checked + 1))
  fallen=$(jq -rn --arg keyform "$form" --slurpfile old <(git show "$oldSpec") --slurpfile new <(git show "${new}:$reg") \
    -f "$here/modules-sh-ratchet.jq")
  rises=""
  if [ "$rise" != - ]; then
    rises=$(jq -rn --arg keyform "$form" --arg part rise --slurpfile old <(git show "$oldSpec") \
      --slurpfile new <(git show "${new}:$reg") -f "$here/modules-sh-ratchet.jq")
  fi
  [ -n "$fallen$rises" ] || return 0
  for r in "$@"; do
    trailers+=$(git log --format="%(trailers:key=$decrease,valueonly)" "$r")$'\n'
    [ "$rise" = - ] || ptrailers+=$(git log --format="%(trailers:key=$rise,valueonly)" "$r")$'\n'
  done
  a=$(nixpkgsAt "$old") || exit 2
  b=$(nixpkgsAt "$new") || exit 2
  moved=no
  [ "$a" = "$b" ] || moved=yes
  if [ -n "$fallen" ]; then
    while IFS=$'\t' read -r key was now; do
      h=$(hashOf "$key")
      # Every trailer naming the hash is read, and ANY valid one admits: a later invalid trailer for the
      # same key (another change's) never shadows a valid one.
      mapfile -t cands < <(grep -E "^$h (relock den-hoag-[a-z0-9.]+|correction .+)\$" <<<"$trailers" || true)
      adm="" why="no $decrease: $h trailer in $*"
      for c in "${cands[@]}"; do
        if [[ "$c" == "$h relock "* && "$moved" == no ]]; then
          why="a relock admission, but nixpkgs did not move in ${old:0:9}..${new:0:9}"
        else
          adm=$c
          break
        fi
      done
      if [ -z "$adm" ]; then
        echo "REFUSED $label $h $was -> $now $key ($why)"
        refused=$((refused + 1))
      else
        echo "admitted $label $h $was -> $now ($adm)"
      fi
    done <<<"$fallen"
  fi
  [ -n "$rises" ] || return 0
  # reanchor's environment test: nixpkgs moved, and nothing under test did.
  ua=$(underTestAt "$old") || exit 2
  ub=$(underTestAt "$new") || exit 2
  env=no
  if [ "$moved" = yes ] && [ "$ua" = "$ub" ]; then env=yes; fi
  while IFS=$'\t' read -r key e was now par above; do
    h=$(hashOf "$key"$'\t'"$e")
    mapfile -t cands < <(grep -E "^$h (reanchor|parity|floor den-hoag-[a-z0-9.]+|owner den-hoag-[a-z0-9.]+)\$" <<<"$ptrailers" || true)
    adm="" why="no $rise: $h trailer in $*"
    for c in "${cands[@]}"; do
      if [[ "$c" == "$h reanchor" && "$env" == no ]]; then
        why="a reanchor admission, but the environment did not move alone in ${old:0:9}..${new:0:9}: nixpkgs moved=$moved, and a gen member pin, lib/ or an arm input moved, or nixpkgs did not"
      elif [[ "$c" == "$h parity" && "$par" == no && "$above" == no ]]; then
        why="a parity admission, but the rise crosses parity: at parity at the anchor, above it now"
      else
        adm=$c
        break
      fi
    done
    if [ -z "$adm" ]; then
      echo "REFUSED $label $h perf rise $was -> $now $key '$e' ($why)"
      refused=$((refused + 1))
    else
      echo "admitted $label $h perf rise $was -> $now ($adm)"
    fi
  done <<<"$rises"
}
for spec in "${registers[@]}"; do
  read -r reg form decrease rise <<<"$spec"
  mapfile -t revs < <(git rev-list --first-parent HEAD -- "$reg")
  [ "${#revs[@]}" -gt 0 ] || control "no revision of $reg on HEAD's history"
  # revs is newest first; revs[i+1] is the revision revs[i] replaced.
  for ((i = 0; i + 1 < ${#revs[@]}; i++)); do
    new=${revs[i]} old=${revs[i + 1]}
    judge "${new:0:9}" "$old" "${new}^:$reg" "$new" "${old}..HEAD"
  done
  if [ -n "${GITHUB_EVENT_PATH:-}" ] && [ -e "$GITHUB_EVENT_PATH" ]; then
    forced=$(jq -r '(.forced // false) | if type == "boolean" then tostring else error("not a boolean") end' \
      "$GITHUB_EVENT_PATH") || control "cannot read .forced from $GITHUB_EVENT_PATH"
    if [ "$forced" = true ]; then
      before=$(jq -er '.before | strings' "$GITHUB_EVENT_PATH") || control "a forced push with no .before in $GITHUB_EVENT_PATH"
      git cat-file -e "${before}^{commit}" 2>/dev/null || git fetch --quiet origin "$before" ||
        control "could not fetch the force-pushed-over ${before:0:9}"
      mb=$(git merge-base "$before" HEAD) && since="${mb}..HEAD" || since=HEAD
      mapfile -t gone < <(git rev-list --first-parent "$before" -- "$reg")
      for ((i = 0; i + 1 < ${#gone[@]}; i++)); do
        new=${gone[i]} old=${gone[i + 1]}
        git merge-base --is-ancestor "$new" HEAD && continue
        judge "replaced:${new:0:9}" "$old" "${new}^:$reg" "$new" "${old}..${before}" "$since"
      done
      if [ "${#gone[@]}" -gt 0 ]; then
        judge "forced:${before:0:9}" "$before" "${before}:$reg" HEAD "$since"
      fi
    fi
  fi
  summary+="${#revs[@]} revisions of $reg, "
done
echo "modules-sh-ratchet: ${summary}$checked changes read, $refused refused"
[ "$refused" -eq 0 ] || exit 1
