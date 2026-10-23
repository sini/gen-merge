# THE REPLACEMENT BAR, STAGE 1 (den-hoag-06toi): nixpkgs' own module-system suite, `lib/tests/modules.sh`,
# run against gen-merge's `evalModuleTree` and scored against a committed per-assertion baseline
# (`modules-sh-baseline.jsonl`). It is a PROCESS-PLANE program for the reason `tests-process.nix` gives:
# each assertion is one `nix-instantiate` process whose verdict is evidence only for the evaluator that
# computed it, so it calls the `nix-instantiate` on PATH and carries none in its closure.
#
# nixpkgs is this flake's own `nixpkgs` input, the same reference the equivalence oracle reads, so the
# suite moves with it at a relock. The GEN tree is that input's `lib/` with ONE file substituted
# (`modules-sh-lib.nix`) and ONE line added to `modules.sh` (sourcing `modules-sh-hook.bash`); no
# fixture is touched and modules.sh's own check functions give every verdict. The REFERENCE tree is the
# same copy with the hook line only: nixpkgs' own lib running nixpkgs' own suite. It runs first, so a
# broken reference stops the run before the gen run is paid for (`nixos-bar.bash`'s docsWalk order).
# Both trees are named `lib`, the upstream layout the suite's own text assumes: its L481 assertion reads
# `.*lib/tests/modules/deferred-module-error.nix`, which nixpkgs' lib FAILS from a tree of another name.
#
# PERF, per assertion on the rows where nixpkgs serves (`checkConfigOutput`, `checkExpression`), from the
# process that gave the verdict: both trees' `nrThunks` and attributed bytes (`envs + list + sets + values
# + symbols`), an EXACT bound on gen's (ADR-0032), keyed by the evaluator's `--version` line, and wall `ms`,
# never compared (`modules-sh-compare.jq`). A row above its reference is the bar's perf criterion NOT MET,
# even where CI is green because the ratchet admitted its rise: admitted is not approved.
#
#   modules-sh                     run and score; exit 1 on any disagreement with the baseline
#   modules-sh --write-baseline F  run and write the baseline to F, this evaluator's perf merged in (the
#                                  ratchet; review its diff and the LOWERED / RISE lines it prints)
#   modules-sh --fold F LOG...     no evaluation: the baseline with the `PERF modules-sh` lines of LOG...
#                                  (CI's three column logs) merged in, written to F; the register's perf
#                                  is written from CI's columns this way, as stage 2's is
#
# EXIT: 0 no disagreement · 1 a disagreement · 2 CONTROL FAILED, a broken instrument, never a verdict.
#
# COST: the process-plane step's budget is 20 minutes per column. Exceeding it is not a red: a gated
# cost bound counts thunks and allocation, never CPU time (ADR-0032), and runner wall is noise. It opens
# a unit against this arm. The reference run costs at most about 0.83x the gen run's wall (measured
# locally); the remedies are running the two runs concurrently, then sharding the run inside the process
# plane.
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
  # One builder, so the two trees cannot differ in name (the name is allocated into gen's bytes).
  mkTree =
    substitute:
    pkgs.runCommand "lib" { } ''
      cp -r ${inputs.nixpkgs}/lib $out
      chmod -R u+w $out
      ${substitute}
      # The one added line, before the first assertion. A modules.sh without the anchor refuses here.
      n=$(grep -n '^# Shorthand meta attribute' $out/tests/modules.sh | cut -d: -f1)
      [ -n "$n" ] || { echo "modules.sh has no '# Shorthand meta attribute' anchor" >&2; exit 1; }
      sed -i "''${n}i source ${./modules-sh-hook.bash}" $out/tests/modules.sh
    '';
  genTree = mkTree ''
    mv $out/default.nix $out/default-orig.nix
    cp ${libDefault} $out/default.nix
  '';
  refTree = mkTree "";
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
    control() {
      echo "modules-sh: CONTROL FAILED: $*" >&2
      exit 2
    }
    base=${./modules-sh-baseline.jsonl}

    # admissions <new register>: what `ci/modules-sh-ratchet.sh` will ask to have admitted against the
    # committed register, with the hash each trailer names (`nixos-bar.bash`'s, over this register's id).
    admissions() {
      jq -rn --slurpfile old "$base" --slurpfile new "$1" -f ${./modules-sh-ratchet.jq} |
        while IFS=$'\t' read -r key was now; do
          echo "LOWERED $(printf '%s' "$key" | sha256sum | cut -c1-12) $was -> $now $key"
        done
      jq -rn --arg part rise --slurpfile old "$base" --slurpfile new "$1" -f ${./modules-sh-ratchet.jq} |
        while IFS=$'\t' read -r key e was now par above setmv; do
          echo "RISE $(printf '%s\t%s' "$key" "$e" | sha256sum | cut -c1-12) $was -> $now parity-now=$par above-at-anchor=$above set-moved=$setmv $key $e"
        done
    }

    # --fold F LOG...: `nixos-bar.bash`'s fold. A log with no `PERF modules-sh` line is a column that did not
    # run the arm (or a wrong file), never "no perf"; a line naming a row the register lacks is refused.
    if [ "''${1:-}" = --fold ]; then
      [ $# -ge 3 ] || control "usage: modules-sh --fold F LOG..."
      out=$2
      shift 2
      for log in "$@"; do
        [ -r "$log" ] || control "cannot read $log"
        n=$(grep -c "PERF modules-sh {" "$log" || true)
        [ "$n" -gt 0 ] || control "$log carries no PERF modules-sh line"
        grep -o "PERF modules-sh {.*}\$" "$log" | sed "s/^PERF modules-sh //" >>"$tmp/perf.jsonl"
        echo "modules-sh: $log: $n PERF lines"
      done
      jq -rn --arg mode fold --slurpfile base "$base" --slurpfile perf "$tmp/perf.jsonl" \
        -f ${./modules-sh-compare.jq} >"$out"
      echo "modules-sh: wrote $(wc -l <"$out") rows to $out"
      admissions "$out"
      exit 0
    fi

    # THE EVALUATOR IS RESOLVED ONCE, and never falls back. Every assertion calls this one path (the hook),
    # so an evaluator that vanishes mid-run exits 127 into the rc control below instead of letting a later
    # PATH entry answer for it. A caller naming its column pins it: MODULES_SH_EVALUATOR is the bin
    # directory that must provide `nix-instantiate`, MODULES_SH_EVALUATOR_VERSION the first line of its
    # `--version`. Either one unmet is CONTROL FAILED, before any evaluation.
    ni=$(command -v nix-instantiate) || control "no nix-instantiate on PATH"
    if [ -n "''${MODULES_SH_EVALUATOR:-}" ] && [ "$ni" != "$MODULES_SH_EVALUATOR/nix-instantiate" ]; then
      control "the evaluator is pinned to $MODULES_SH_EVALUATOR, but nix-instantiate resolves to $ni"
    fi
    line=$("$ni" --version | sed -n 1p)
    if [ -n "''${MODULES_SH_EVALUATOR_VERSION:-}" ] && [ "$line" != "$MODULES_SH_EVALUATOR_VERSION" ]; then
      control "the evaluator is pinned to '$MODULES_SH_EVALUATOR_VERSION', but $ni reports '$line'"
    fi
    export MODULES_SH_NIX_INSTANTIATE=$ni
    echo "modules-sh: evaluator $line ($ni), nixpkgs lib ${
      inputs.nixpkgs.rev or inputs.nixpkgs.narHash
    }"

    # THE GEN TREE RUNS GEN: gen-merge's evaluation answers a field nixpkgs' does not (stage 2's control).
    # Read-write as modules.sh's own evaluations are: the gen tree's sources are copied at evaluation, which
    # a read-only evaluation cannot do on a store that lacks the copy.
    engine() {
      NIX_PATH="" "$ni" --eval --read-write-mode -E "builtins.hasAttr \"deprecations\" ((import $1/default.nix).evalModules { modules = [ ]; })" \
        2>"$tmp/engine.err" || true
    }
    got=$(engine ${genTree})
    [ "$got" = true ] || control "the gen tree did not run gen (deprecations answered '$got') $(tail -1 "$tmp/engine.err")"
    got=$(engine ${refTree})
    [ "$got" = false ] || control "the reference tree did not run nixpkgs (deprecations answered '$got') $(tail -1 "$tmp/engine.err")"

    # modules.sh exits non-zero whenever any assertion fails, which the baseline expects; it must
    # still have run to its end, which its summary line says.
    # The whole run, both trees, has a deadline: the per-evaluation bound alone allows ~410 x 120 s, past
    # GitHub's 360-minute job limit, which would cancel the run without saying why. 60 minutes is three
    # times the 20-minute budget, so a run over budget is still not a red, and well inside the job limit.
    # MODULES_SH_DEADLINE (seconds) exists for the cell that plants a global hang.
    deadline=''${MODULES_SH_DEADLINE:-3600}
    end=$(($(date +%s) + deadline))
    # arm <name> <tree>: one modules.sh run over <tree>, its records in $tmp/<name>.jsonl.
    arm() {
      local name=$1 tree=$2 left runRc=0 done_=0 bad
      export MODULES_SH_RECORDS=$tmp/$name.jsonl MODULES_SH_CAP=$tmp/$name-cap
      left=$((end - $(date +%s)))
      [ "$left" -gt 0 ] || control "the run passed its $deadline s deadline before the $name run"
      timeout -k 10 "$left" bash "$tree/tests/modules.sh" >"$tmp/$name.log" 2>&1 || runRc=$?
      if [ "$runRc" -eq 124 ] || [ "$runRc" -eq 137 ]; then
        if [ -e "$MODULES_SH_RECORDS" ]; then done_=$(wc -l <"$MODULES_SH_RECORDS"); fi
        control "the run passed its $deadline s deadline with $done_ assertions of the $name run completed"
      fi
      grep -q '^====== module tests ======$' "$tmp/$name.log" || {
        tail -20 "$tmp/$name.log" >&2
        control "modules.sh did not run to its summary line ($name)"
      }
      [ -s "$MODULES_SH_RECORDS" ] || control "no assertion was recorded ($name)"
      # A verdict is read only off an evaluation that ran: modules.sh's evaluations exit 0 or 1, and any
      # other status (127 no evaluator on PATH, 137 killed) is a broken instrument, never a FAIL.
      bad=$(jq -r 'select(.rc != 0 and .rc != 1) | "L\(.line) rc=\(.rc)"' "$MODULES_SH_RECORDS")
      [ -z "$bad" ] || control "$(wc -l <<<"$bad") evaluations of the $name run exited neither 0 nor 1: $(head -5 <<<"$bad" | tr '\n' ' ')"
      # SERVED MEANS MEASURED (`evalArm`'s rule): an evaluation that exited 0 wrote non-zero counters.
      bad=$(jq -r 'select(.rc == 0 and (.perf == null or .perf.thunks <= 0 or .perf.bytes <= 0)) | "L\(.line)"' "$MODULES_SH_RECORDS")
      [ -z "$bad" ] || control "$(wc -l <<<"$bad") evaluations of the $name run exited 0 but wrote no stats file or a zero counter: $(head -5 <<<"$bad" | tr '\n' ' ')"
    }
    arm ref ${refTree}
    # THE REFERENCE SERVES ITS OWN SUITE: a reference that fails nixpkgs' own assertion is not the
    # reference for that row, so no row has a verdict to read.
    bad=$(jq -r 'select(.verdict != "PASS") | "L\(.line)"' "$tmp/ref.jsonl")
    [ -z "$bad" ] || control "the reference run failed $(wc -l <<<"$bad") of nixpkgs' own assertions: $(head -5 <<<"$bad" | tr '\n' ' ')"
    arm gen ${genTree}
    # SAME ASSERTIONS: both runs recorded one id set.
    ids() { jq -c '[.key.kind, .key.env, .key.argv]' "$1" | sort; }
    cmp -s <(ids "$tmp/ref.jsonl") <(ids "$tmp/gen.jsonl") || control "the two runs recorded different assertions"
    # gen's records, each with the reference run's {rc, verdict, perf} joined by id.
    jq -c --slurpfile ref "$tmp/ref.jsonl" \
      '($ref | map({ key: (.key | [.kind, .env, .argv] | tojson), value: { rc, verdict, perf } }) | from_entries) as $R
      | . + { ref: $R[.key | [.kind, .env, .argv] | tojson] }' "$tmp/gen.jsonl" >"$tmp/records.jsonl"

    jq -rs --arg mode perf --arg ev "$line" --slurpfile base "$base" -f ${./modules-sh-compare.jq} "$tmp/records.jsonl"
    if [ "''${1:-}" = --write-baseline ]; then
      [ $# -ge 2 ] || control "usage: modules-sh --write-baseline F"
      jq -rs --arg mode write --arg ev "$line" --slurpfile base "$base" -f ${./modules-sh-compare.jq} "$tmp/records.jsonl" >"$2"
      echo "modules-sh: wrote $(wc -l <"$2") rows to $2"
      admissions "$2"
      exit 0
    fi
    jq -rs --arg mode check --arg ev "$line" --slurpfile base "$base" -f ${./modules-sh-compare.jq} "$tmp/records.jsonl" >"$tmp/report"
    cat "$tmp/report"
    tail -1 "$tmp/report" | grep -q '; 0 disagreements$'
  '';
}
