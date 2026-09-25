# THE PER-PROCESS RUNNER — a program that evaluates each cell in `tests-process-cells.nix` in its
# OWN evaluator process and asserts on the EXIT STATUS, the channel a death is on, and the printed
# value. gen-scope's `ci/tests-process.nix` is the precedent and the reasons are the same: the
# verdict is a process predicate, so it is not a nix-unit output; and it is evidence only for the
# evaluator that computed it, so it is not a sandboxed check, where the evaluator is a derivation
# input identical in every CI column (den-hoag-jutgv). As `apps.<system>.tests-process` its cells
# call the `nix-instantiate` on PATH, and gen-harness's `ci --tests-process` runs it in every column
# of `evaluators.yml`, refusing a program whose closure carries an evaluator. Locally:
#   nix develop ./ci --command ci --tests-process
#
# gen-graph and gen-identity are not inputs of this flake; they are read off gen-scope's own inputs,
# the edges `flake.lock` already records for it.
{ inputs, ... }:
{
  perSystem =
    { pkgs, ... }:
    {
      apps.tests-process.program = pkgs.writeShellScriptBin "tests-process" (
        ''
          set -e
          # The tools the body calls, declared rather than ambient — and never an evaluator.
          export PATH=${
            pkgs.lib.makeBinPath [
              pkgs.coreutils
              pkgs.gnugrep
              pkgs.gnused
            ]
          }:$PATH
          export cells=${./tests-process-cells.nix} libSrc=${../lib}
          export genPreludeSrc=${inputs.gen-prelude} genIdentitySrc=${inputs.gen-scope.inputs.gen-identity}
          export genGraphSrc=${inputs.gen-scope.inputs.gen-graph} genTypesSrc=${inputs.gen-types}
          export genMemoSrc=${inputs.gen-memo} genScopeSrc=${inputs.gen-scope}
          # A fresh working directory per run, as gen-scope's runner needs (den-hoag-jutgv).
          TMPDIR=$(mktemp -d) out=$(mktemp)
          export TMPDIR out
          trap 'rm -rf "$TMPDIR" "$out"' EXIT
          cd "$TMPDIR"
          # The evaluator the cells run under, from this process and the binary they call.
          echo "evaluator: $(nix-instantiate --version | sed -n 1p)"
        ''
        + ''
          export NIX_STATE_DIR=$TMPDIR/nix-state NIX_LOG_DIR=$TMPDIR/nix-log
          ran=0
          die() {
            echo "tests-process: FAILED at cell $1: $2" >&2
            exit 1
          }
          # evalArm <arm>: runs one cell in its own process; leaves rc/val set. The value variable
          # is `val`, never `out` — `out` is the derivation's own output path.
          evalArm() {
            rc=0
            val=$(nix-instantiate --eval --strict --readonly-mode \
              --argstr arm "$1" \
              --argstr libSrc "$libSrc" \
              --argstr genPreludeSrc "$genPreludeSrc" \
              --argstr genIdentitySrc "$genIdentitySrc" \
              --argstr genGraphSrc "$genGraphSrc" \
              --argstr genTypesSrc "$genTypesSrc" \
              --argstr genMemoSrc "$genMemoSrc" \
              --argstr genScopeSrc "$genScopeSrc" \
              "$cells" 2> "$TMPDIR/err") || rc=$?
            ran=$((ran + 1))
          }

          # den-hoag-xzchx C3 — the outer fixpoint reading the evaluation's own `options` from a
          # plain attrset DIVERGES: non-zero exit, the infinite-recursion channel, no value. An
          # admission that skips the declaration guard for a formal-free module answers here.
          evalArm outer-options-read
          [ "$rc" -ne 0 ] || die outer-options-read "expected a death, got exit 0 with '$val'"
          grep -q 'infinite recursion encountered' "$TMPDIR/err" || die outer-options-read "death is not the infinite-recursion channel"
          # Its live controls, same runner, same wiring: the in-module form refuses BY NAME (the
          # guard is live), and a stratum-2 read of the same fixpoint answers (the wiring evaluates).
          evalArm in-module-options-read
          [ "$rc" -ne 0 ] || die in-module-options-read "expected a by-name refusal, got exit 0 with '$val'"
          grep -Fq "gen-merge: a module read \`options' while its own declarations were being folded" "$TMPDIR/err" || die in-module-options-read "refusal is not the declaration guard's named refusal"
          evalArm outer-default-read
          [ "$rc" -eq 0 ] || die outer-default-read "expected exit 0, got $rc"
          [ "$val" = '"on"' ] || die outer-default-read "expected value \"on\", got '$val'"

          # 0/0 is a false pass: the runner must have executed every cell above.
          [ "$ran" = "3" ] || die runner "expected 3 evaluations, ran $ran"
          echo "tests-process: 3 cells, every exit read unpiped, every death on its named channel" > $out
        ''
        + ''
          cat "$out"
        ''
      );
    };
}
