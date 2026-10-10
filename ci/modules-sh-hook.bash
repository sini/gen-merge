# Sourced by the copied `modules.sh` just before its first assertion (the one line added to it).
# modules.sh's own check functions stay the verdict: each is renamed `orig_*` and called unchanged,
# and this records one JSON line per assertion — its key (kind, the env flags modules.sh reads, argv),
# its modules.sh line, the verdict, and the FIRST evaluation's exit status and stderr (reportFailure
# re-evaluates on a failure; that second run is not recorded).
for f in checkConfigOutput checkConfigError checkExpression local-nix-instantiate; do
  eval "orig_$(declare -f "$f")"
done

# modules.sh's reportFailure prints a failure by evaluating it a second time; the record already holds
# the first evaluation, so only its count is kept.
reportFailure() { ((++fail)); }

# Every evaluation is bounded: modules.sh's `--timeout 1` is a build setting and bounds no evaluation,
# so a non-terminating fixture would hold the column to the job limit. Its exit 124 is neither 0 nor 1,
# so the run fails CONTROL FAILED, never as a verdict. The slowest measured assertion takes 21 s on a
# loaded host. This bounds one evaluation, not the run (~410 x 120 s is past GitHub's 360-minute job
# limit); the runner's whole-run deadline (`modules-sh.nix`) bounds the run. The binary is the one path the runner resolved, never a PATH search: `timeout` would
# otherwise search PATH on every call, and a vanished evaluator would be answered by the next one.
nix-instantiate() { timeout 120 "$MODULES_SH_NIX_INSTANTIATE" "$@"; }

local-nix-instantiate() {
  local rc=0
  orig_local-nix-instantiate "$@" >|"$MODULES_SH_CAP.out" 2>|"$MODULES_SH_CAP.err" || rc=$?
  if [[ -z "${captured:-}" ]]; then
    cp "$MODULES_SH_CAP.err" "$MODULES_SH_CAP.first.err"
    echo "$rc" >|"$MODULES_SH_CAP.first.rc"
    captured=1
  fi
  cat "$MODULES_SH_CAP.out"
  cat "$MODULES_SH_CAP.err" >&2
  return $rc
}

wrap() {
  local kind=$1 line=$2
  shift 2
  local before=$fail t0
  captured=
  t0=$(date +%s%N)
  "orig_$kind" "$@" || true
  jq -cn --arg kind "$kind" --argjson line "$line" \
    --arg verdict "$([[ $fail == "$before" ]] && echo PASS || echo FAIL)" \
    --arg env "$(echo ${ABORT_ON_WARN:+ABORT_ON_WARN} ${STRICT_EVAL:+STRICT_EVAL} ${REQUIRE_INFINITE_RECURSION_HINT:+RIRH})" \
    --argjson rc "$(cat "$MODULES_SH_CAP.first.rc")" --argjson ms "$((($(date +%s%N) - t0) / 1000000))" --rawfile err "$MODULES_SH_CAP.first.err" \
    '{key:{kind:$kind,env:$env,argv:$ARGS.positional},line:$line,verdict:$verdict,rc:$rc,ms:$ms,err:$err}' \
    --args "$@" >>"$MODULES_SH_RECORDS"
}
checkConfigOutput() { wrap checkConfigOutput "$(caller 0 | cut -d' ' -f1)" "$@"; }
checkConfigError() { wrap checkConfigError "$(caller 0 | cut -d' ' -f1)" "$@"; }
checkExpression() { wrap checkExpression "$(caller 0 | cut -d' ' -f1)" "$@"; }
