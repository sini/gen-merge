# THE REPLACEMENT BAR, STAGE 1 (den-hoag-06toi): nixpkgs' own module-system suite, `lib/tests/modules.sh`,
# run against gen-merge's `evalModuleTree` and scored against a committed per-assertion baseline
# (`modules-sh-baseline.jsonl`). It is a PROCESS-PLANE program for the reason `tests-process.nix` gives:
# each assertion is one `nix-instantiate` process whose verdict is evidence only for the evaluator that
# computed it, so it calls the `nix-instantiate` on PATH and carries none in its closure.
#
# nixpkgs is this flake's own `nixpkgs` input, the same reference the equivalence oracle reads, so the
# suite moves with it at a relock. The tree is that input's `lib/` with ONE file substituted
# (`modules-sh-lib.nix`) and ONE line added to `modules.sh` (sourcing `modules-sh-hook.bash`); no
# fixture is touched and modules.sh's own check functions give every verdict.
#
#   modules-sh                     run and score; exit 1 on any disagreement with the baseline
#   modules-sh --write-baseline F  run and write the baseline to F (the ratchet; review its diff)
#
# COST: the process-plane step's budget is 20 minutes per column. Exceeding it is not a red: a gated
# cost bound counts thunks and allocation, never CPU time (ADR-0032), and runner wall is noise. It opens
# a unit against this arm, whose remedy is sharding the run inside the process plane.
{ pkgs, inputs }:
let
  libDefault = pkgs.writeText "default.nix" ''
    import ${./modules-sh-lib.nix} {
      orig = import ./default-orig.nix;
      libSrc = ${../lib};
      genPreludeSrc = ${inputs.gen-prelude};
      genIdentitySrc = ${inputs.gen-scope.inputs.gen-identity};
      genGraphSrc = ${inputs.gen-scope.inputs.gen-graph};
      genTypesSrc = ${inputs.gen-types};
      genAlgebraSrc = ${inputs.gen-types.inputs.gen-algebra};
      genMemoSrc = ${inputs.gen-memo};
      genScopeSrc = ${inputs.gen-scope};
    }
  '';
  tree = pkgs.runCommand "modules-sh-tree" { } ''
    cp -r ${inputs.nixpkgs}/lib $out
    chmod -R u+w $out
    mv $out/default.nix $out/default-orig.nix
    cp ${libDefault} $out/default.nix
    # The one added line, before the first assertion. A modules.sh without the anchor refuses here.
    n=$(grep -n '^# Shorthand meta attribute' $out/tests/modules.sh | cut -d: -f1)
    [ -n "$n" ] || { echo "modules.sh has no '# Shorthand meta attribute' anchor" >&2; exit 1; }
    sed -i "''${n}i source ${./modules-sh-hook.bash}" $out/tests/modules.sh
  '';
in
pkgs.writeShellApplication {
  name = "modules-sh";
  # Never an evaluator: modules.sh's assertions call the column's `nix-instantiate`, from PATH.
  runtimeInputs = [
    pkgs.bash
    pkgs.coreutils
    pkgs.gnugrep
    pkgs.gnused
    pkgs.jq
  ];
  text = ''
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT
    export MODULES_SH_RECORDS=$tmp/records.jsonl MODULES_SH_CAP=$tmp/cap
    # THE EVALUATOR IS RESOLVED ONCE, and never falls back. Every assertion calls this one path (the hook),
    # so an evaluator that vanishes mid-run exits 127 into the rc control below instead of letting a later
    # PATH entry answer for it. A caller naming its column pins it: MODULES_SH_EVALUATOR is the bin
    # directory that must provide `nix-instantiate`, MODULES_SH_EVALUATOR_VERSION the first line of its
    # `--version`. Either one unmet is CONTROL FAILED, before any evaluation.
    ni=$(command -v nix-instantiate) || { echo "modules-sh: CONTROL FAILED: no nix-instantiate on PATH" >&2; exit 2; }
    if [ -n "''${MODULES_SH_EVALUATOR:-}" ] && [ "$ni" != "$MODULES_SH_EVALUATOR/nix-instantiate" ]; then
      echo "modules-sh: CONTROL FAILED: the evaluator is pinned to $MODULES_SH_EVALUATOR, but nix-instantiate resolves to $ni" >&2
      exit 2
    fi
    line=$("$ni" --version | sed -n 1p)
    if [ -n "''${MODULES_SH_EVALUATOR_VERSION:-}" ] && [ "$line" != "$MODULES_SH_EVALUATOR_VERSION" ]; then
      echo "modules-sh: CONTROL FAILED: the evaluator is pinned to '$MODULES_SH_EVALUATOR_VERSION', but $ni reports '$line'" >&2
      exit 2
    fi
    export MODULES_SH_NIX_INSTANTIATE=$ni
    echo "modules-sh: evaluator $line ($ni), nixpkgs lib ${
      inputs.nixpkgs.rev or inputs.nixpkgs.narHash
    }"
    # modules.sh exits non-zero whenever any assertion fails, which the baseline expects; it must
    # still have run to its end, which its summary line says.
    # The whole run has a deadline: the per-evaluation bound alone allows ~410 x 120 s, past GitHub's
    # 360-minute job limit, which would cancel the run without saying why. 60 minutes is three times
    # the 20-minute budget, so a run over budget is still not a red, and well inside the job limit.
    # MODULES_SH_DEADLINE (seconds) exists for the cell that plants a global hang.
    deadline=''${MODULES_SH_DEADLINE:-3600}
    runRc=0
    timeout -k 10 "$deadline" bash ${tree}/tests/modules.sh >"$tmp/log" 2>&1 || runRc=$?
    if [ "$runRc" -eq 124 ] || [ "$runRc" -eq 137 ]; then
      done_=0
      if [ -e "$MODULES_SH_RECORDS" ]; then done_=$(wc -l <"$MODULES_SH_RECORDS"); fi
      echo "modules-sh: CONTROL FAILED: the run passed its $deadline s deadline with $done_ assertions completed" >&2
      exit 2
    fi
    grep -q '^====== module tests ======$' "$tmp/log" || {
      echo "modules-sh: CONTROL FAILED: modules.sh did not run to its summary line" >&2
      tail -20 "$tmp/log" >&2
      exit 2
    }
    [ -s "$MODULES_SH_RECORDS" ] || { echo "modules-sh: CONTROL FAILED: no assertion was recorded" >&2; exit 2; }
    # A verdict is read only off an evaluation that ran: modules.sh's evaluations exit 0 or 1, and any
    # other status (127 no evaluator on PATH, 137 killed) is a broken instrument, never a FAIL.
    bad=$(jq -r 'select(.rc != 0 and .rc != 1) | "L\(.line) rc=\(.rc)"' "$MODULES_SH_RECORDS")
    if [ -n "$bad" ]; then
      echo "modules-sh: CONTROL FAILED: $(wc -l <<<"$bad") evaluations exited neither 0 nor 1:" >&2
      head -5 <<<"$bad" >&2
      exit 2
    fi
    base=${./modules-sh-baseline.jsonl}
    if [ "''${1:-}" = --write-baseline ]; then
      jq -rs --arg mode write --slurpfile base "$base" -f ${./modules-sh-compare.jq} "$MODULES_SH_RECORDS" >"$2"
      echo "modules-sh: wrote $(wc -l <"$2") rows to $2"
      # What `ci/modules-sh-ratchet.sh` will ask to be admitted, with the hash its trailer names.
      jq -rn --slurpfile old "$base" --slurpfile new "$2" -f ${./modules-sh-ratchet.jq} |
        while IFS=$'\t' read -r key was now; do
          echo "LOWERED $(printf '%s' "$key" | sha256sum | cut -c1-12) $was -> $now $key"
        done
      exit 0
    fi
    jq -rs --arg mode check --slurpfile base "$base" -f ${./modules-sh-compare.jq} "$MODULES_SH_RECORDS" >"$tmp/report"
    cat "$tmp/report"
    tail -1 "$tmp/report" | grep -q '; 0 disagreements$'
  '';
}
