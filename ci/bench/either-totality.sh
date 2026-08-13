#!/usr/bin/env bash
# The union-totality sweep: an EXIT-CODE instrument, because the thing being measured is an abort no
# in-language assertion can observe.
#
#   ./ci/bench/either-totality.sh   -> per-arm readings, then TOTAL | NOT-TOTAL | INVALID
#
# Seven arms of ONE construction (`either-totality.nix`), differing only in which merge the union
# carries, what its members answer about membership, and which definitions it is given. What each
# must do:
#
#   shipped             exit 0, caught=true          — the mixed set refuses BY THROW, so it is catchable
#   shippedListLast     exit 0, caught=true          — the same set authored the other way round
#   pre                 NON-ZERO exit                — the WHOLE prior state (old dispatch, members
#                                                      answering as they did), whose interpreter error
#                                                      escapes tryEval
#   preCurrentChecks    NON-ZERO exit                — old dispatch, members answering honestly: the
#                                                      abort is still reachable, so the dispatch change
#                                                      is load-bearing and not carried by the checks
#   shippedHomogeneous  exit 0, ["b","a"]            — POSITIVE CONTROL: a set one member takes whole
#                                                      still merges, and to the same bytes
#   preHomogeneous      exit 0, ["b","a"]            — the pre-remediation construction is not merely
#                                                      broken, and the two agree wherever both answer
#   catchControl        exit 0, caught=true          — the catcher's own control
#
# The last three matter as much as the first: without `preHomogeneous` a red `pre` would prove only
# that something in a hand-built type is wrong, without `catchControl` its non-zero exit could be a
# broken `tryEval` rather than an escaping abort, and without `preCurrentChecks` the sweep would be
# consistent with only half the rule doing any work. An arm that does not read as stated makes the
# sweep INVALID, never a quieter pass.
#
# `nix eval --file` is not usable: it does not auto-call a function-headed file. Every arm is
# `nix-instantiate --eval --strict --json` with an explicit `--argstr`, and the exit code is read
# IMMEDIATELY — `$?` after a pipe reads the pipe's last stage and is a false green.
set -u
cd "$(dirname "$0")/../.." || exit 99

arm() {
  nix-instantiate --eval --strict --json --argstr arm "$1" ./ci/bench/either-totality.nix 2>/dev/null
}

fail=0
check() { # check <arm> <expect-exit> <expect-substring-or-->
  out=$(arm "$1")
  rc=$?
  printf '%-19s exit=%d %s\n' "$1" "$rc" "${out:-<no value>}"
  if [ "$rc" -ne "$2" ]; then
    fail=$((fail + 1))
    return
  fi
  if [ "$3" != "-" ] && [[ "$out" != *"$3"* ]]; then
    fail=$((fail + 1))
  fi
}

# The remediated union refuses the mixed set by name, whichever module wrote last, and the refusal
# is catchable.
check shipped 0 '"caught":true'
check shippedListLast 0 '"caught":true'
# The pre-remediation merge on the SAME set: no JSON to read, the exit code is the whole reading.
check pre 1 -
check preCurrentChecks 1 -
# POSITIVE CONTROLS: a set one member takes whole merges under both constructions, to the same value.
check shippedHomogeneous 0 '"value":["b","a"]'
check preHomogeneous 0 '"value":["b","a"]'
# The catcher works in this evaluation, so `pre`'s exit is an abort escaping it.
check catchControl 0 '"caught":true'

echo
if [ "$fail" -eq 0 ]; then
  echo "TOTAL"
else
  echo "INVALID ($fail arms did not read as stated)"
  exit 1
fi
