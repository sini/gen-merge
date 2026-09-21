#!/usr/bin/env bash
# The foreign self-merge sweep: an EXIT-CODE instrument, because the thing being measured is an abort
# no in-language assertion can observe.
#
#   ./ci/bench/selfmerge-totality.sh   -> per-arm readings, then TOTAL | NOT-TOTAL | INVALID
#
# Nine arms of ONE construction (`selfmerge-totality.nix`), differing only in which `importedMerge`
# the arm carries and which type it self-merges. What each must do:
#
#   guarded-json         exit 0, "NULL"           — the shipped boundary declines the call
#   unguarded-json       NON-ZERO exit            — the WHOLE prior state: `a.typeMerge b.functor`
#                                                   with nothing asked first, on a self-referential
#                                                   type, whose interpreter error escapes tryEval
#   tryguard-json        exit 0, success=true     — the shipped answer is CONTAINABLE by a consumer
#   tryunguarded-json    NON-ZERO exit            — the identical tryEval does NOT contain the prior
#                                                   construction; this is the whole point of the file
#   guarded-number       exit 0, MERGED           — POSITIVE CONTROL: a decidable foreign pair still
#                                                   merges, so `guarded-json`'s NULL is not a
#                                                   boundary that stopped merging anything
#   unguarded-number     exit 0, MERGED           — the prior construction is not merely broken, and
#                                                   the two agree wherever both answer
#   tryunguarded-number  exit 0, success=true     — the catcher works on the PRIOR construction too
#   catchControl         exit 0, success=false    — the catcher's own control: a `throw` IS caught
#   declaration-guarded  exit 0, success=false    — the PUBLISHED surface: an ordinary redeclaration
#                                                   now throws catchably instead of aborting
#
# The controls matter as much as the subject: without `guarded-number` a `NULL` from the guard would
# be consistent with refusing everything, without `tryunguarded-number` and `catchControl` the two
# non-zero exits could be a broken `tryEval` rather than an escaping abort, and without
# `unguarded-number` `unguarded-json`'s red would prove only that a hand-built merge is wrong. An arm
# that does not read as stated makes the sweep INVALID, never a quieter pass.
#
# `nix eval --file` is not usable: it does not auto-call a function-headed file. Every arm is
# `nix-instantiate --eval --strict --json` with an explicit `--argstr`, and the exit code is read
# IMMEDIATELY — `$?` after a pipe reads the pipe's last stage and is a false green.
set -u
cd "$(dirname "$0")/../.." || exit 99

# COULD NOT MEASURE is a different answer from NOT TOTAL, and without this the difference is only
# legible by inference: with the fixture gone every arm reads `exit=1 <no value>`, and the two arms
# that EXPECT a non-zero exit pass vacuously — so the sweep still refuses, but it refuses while
# naming the wrong seven arms. Measured, with the file moved aside: `INVALID (7 arms …)`.
[ -f ./ci/bench/selfmerge-totality.nix ] || {
  echo "INVALID: ./ci/bench/selfmerge-totality.nix is missing — nothing was measured" >&2
  exit 99
}

arm() {
  nix-instantiate --eval --strict --json --argstr arm "$1" ./ci/bench/selfmerge-totality.nix 2>/dev/null
}

fail=0
check() { # check <arm> <expect-exit> <expect-substring-or-->
  out=$(arm "$1")
  rc=$?
  printf '%-21s exit=%d %s\n' "$1" "$rc" "${out:-<no value>}"
  if [ "$rc" -ne "$2" ]; then
    fail=$((fail + 1))
    return
  fi
  if [ "$3" != "-" ] && [[ "$out" != *"$3"* ]]; then
    fail=$((fail + 1))
  fi
}

# The shipped boundary declines the undecidable call and answers `null`, and that answer is
# containable by a consumer.
check guarded-json 0 '"merged":"NULL"'
check tryguard-json 0 '"success":true'
# The pre-guard merge on the SAME type: no JSON to read, the exit code is the whole reading — and
# the identical tryEval does not contain it either.
check unguarded-json 1 -
check tryunguarded-json 1 -
# POSITIVE CONTROLS: a decidable foreign pair merges under both constructions, to the same value.
check guarded-number 0 '"merged":"MERGED name=either"'
check unguarded-number 0 '"merged":"MERGED name=either"'
# The catcher works in this evaluation and on the prior construction, so the two exits above are
# aborts escaping it.
check tryunguarded-number 0 '"success":true'
check catchControl 0 '"success":false'
# The published surface: the ordinary redeclaration refuses catchably rather than aborting.
check declaration-guarded 0 '"success":false'

echo
if [ "$fail" -eq 0 ]; then
  echo "TOTAL"
else
  echo "INVALID ($fail arms did not read as stated)"
  exit 1
fi
