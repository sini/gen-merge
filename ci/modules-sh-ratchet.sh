#!/usr/bin/env bash
# THE RATCHET GUARD (den-hoag-06toi): the modules.sh baseline never lowers the bar silently. The property
# is about HISTORY, not a tree — a regression written into the register by `--write-baseline` reads green
# against itself — so this walks every revision of the register on HEAD's first-parent history and
# compares each with its predecessor (`modules-sh-ratchet.jq`). Each fallen key must be ADMITTED by a
# `Modules-Sh-Decrease:` trailer, naming the key's hash, on a commit after the older revision (up to
# HEAD, so a later commit can admit a fall that already landed; a trailer never admits a later fall):
#
#   Modules-Sh-Decrease: <hash> relock den-hoag-<census row>
#       admitted only if nixpkgs' lock node moved between the two revisions: upstream moved the bar,
#       and the key's failure enters the census (den-hoag-uccyi, rx8sv rule 4);
#   Modules-Sh-Decrease: <hash> correction <reason>
#       a register correction (a class row that was wrong-class, say), with its reason.
#
# Any other fall is a regression of a working cell (rx8sv rule 2) and refuses.
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
#   trailer is admitted too;
# - its own edits: it runs from HEAD's tree, so a commit that weakens this file or
#   `modules-sh-ratchet.jq`, or moves the register and edits `reg=` with it, escapes it. Review reads
#   every diff to `ci/modules-sh-ratchet.*` and to `reg=`.
#
# Needs git and jq, never an evaluator. Run from the repository root:  bash ci/modules-sh-ratchet.sh
# EXIT: 0 every fall admitted · 1 REFUSED, naming each key · 2 CONTROL FAILED, history not read.
set -euo pipefail
reg=ci/modules-sh-baseline.jsonl
here=$(dirname "$0")
control() {
  echo "modules-sh-ratchet: CONTROL FAILED: $*" >&2
  exit 2
}
if [ "$(git rev-parse --is-shallow-repository)" = true ]; then
  # CI checks out at depth 1; the property needs the register's whole history.
  git fetch --quiet --unshallow origin || control "could not unshallow"
fi
mapfile -t revs < <(git rev-list --first-parent HEAD -- "$reg")
[ "${#revs[@]}" -gt 0 ] || control "no revision of $reg on HEAD's history"
# A lock whose nixpkgs is not a node-name string (a follows path, say) is unreadable, never "moved".
nixpkgsAt() {
  git show "$1:ci/flake.lock" |
    jq -er '.nodes[.nodes.root.inputs.nixpkgs | strings].locked | (.rev // .narHash) | strings' ||
    control "cannot read nixpkgs' lock node at ${1:0:9}"
}
hashOf() { printf '%s' "$1" | sha256sum | cut -c1-12; }
refused=0 checked=0
# judge <label> <old rev> <old register spec> <new rev> <trailer range>…: the falls from the old
# register to <new rev>'s, each needing an admission among the trailers of the ranges.
judge() {
  local label=$1 old=$2 oldSpec=$3 new=$4 fallen trailers="" r a b moved key was now h adm
  shift 4
  checked=$((checked + 1))
  fallen=$(jq -rn --slurpfile old <(git show "$oldSpec") --slurpfile new <(git show "${new}:$reg") \
    -f "$here/modules-sh-ratchet.jq")
  [ -n "$fallen" ] || return 0
  for r in "$@"; do
    trailers+=$(git log --format='%(trailers:key=Modules-Sh-Decrease,valueonly)' "$r")$'\n'
  done
  a=$(nixpkgsAt "$old") || exit 2
  b=$(nixpkgsAt "$new") || exit 2
  moved=no
  [ "$a" = "$b" ] || moved=yes
  while IFS=$'\t' read -r key was now; do
    h=$(hashOf "$key")
    adm=$(grep -E "^$h (relock den-hoag-[a-z0-9.]+|correction .+)\$" <<<"$trailers" | head -1 || true)
    if [ -z "$adm" ]; then
      echo "REFUSED $label $h $was -> $now $key (no Modules-Sh-Decrease: $h trailer in $*)"
      refused=$((refused + 1))
    elif [[ "$adm" == "$h relock "* && "$moved" == no ]]; then
      echo "REFUSED $label $h $was -> $now $key (a relock admission, but nixpkgs did not move in ${old:0:9}..${new:0:9})"
      refused=$((refused + 1))
    else
      echo "admitted $label $h $was -> $now ($adm)"
    fi
  done <<<"$fallen"
}
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
echo "modules-sh-ratchet: ${#revs[@]} revisions of $reg, $checked changes read, $refused refused"
[ "$refused" -eq 0 ] || exit 1
