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
          # nixpkgs as a VALUE, for the one cell folding a stock nixpkgs container (never a lib dep).
          export nixpkgsSrc=${inputs.nixpkgs}
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
          # The spy's trace label, generated fresh per run and never written down, so no text a cell
          # or a document carries can be mistaken for a firing.
          label="spy-$(head -c 12 /dev/urandom | od -An -tx1 | tr -d ' \n')"
          # traced <arm>: the number of lines on stderr carrying this run's label.
          traced() {
            grep -c "trace: $label\$" "$TMPDIR/err" || true
          }
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
              --argstr label "$label" \
              --argstr nixpkgsSrc "$nixpkgsSrc" \
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

          # den-hoag-n6dh7 U2-g: ONE gen-scope evaluation per `evalModuleTree`, however many nested
          # trees its value holds. The spy counts `scope.eval` calls; its live control reads 2.
          for arm in one-eval-flat one-eval-sub-one one-eval-attrs-two one-eval-list-two one-eval-sub-empty one-eval-deep one-eval-np-attrs; do
            evalArm "$arm"
            [ "$rc" -eq 0 ] || die "$arm" "expected exit 0, got $rc"
            n=$(traced)
            [ "$n" = "1" ] || die "$arm" "expected 1 evaluation, the spy counted $n"
          done
          evalArm one-eval-control-two-roots
          [ "$rc" -eq 0 ] || die one-eval-control-two-roots "expected exit 0, got $rc"
          [ "$val" = "3" ] || die one-eval-control-two-roots "expected value 3, got '$val'"
          n=$(traced)
          [ "$n" = "2" ] || die one-eval-control-two-roots "the spy's control expected 2 evaluations, counted $n"

          # den-hoag-n6dh7 U2-l (gate O1): a candidate's `result` refuses before its member's modules
          # are applied — the traced module is applied 0 times — and a selected child applies it.
          evalArm candidate-modules
          [ "$rc" -eq 0 ] || die candidate-modules "expected exit 0, got $rc"
          [ "$val" = "false" ] || die candidate-modules "expected the candidate's result to refuse, got '$val'"
          n=$(traced)
          [ "$n" = "0" ] || die candidate-modules "expected 0 applications of the candidate member's modules, counted $n"
          evalArm candidate-modules-control
          [ "$rc" -eq 0 ] || die candidate-modules-control "expected exit 0, got $rc"
          [ "$val" = "1" ] || die candidate-modules-control "expected value 1, got '$val'"
          n=$(traced)
          [ "$n" -ge 1 ] || die candidate-modules-control "expected the selected child to apply the module, counted $n"

          # 0/0 is a false pass: the runner must have executed every cell above.
          [ "$ran" = "13" ] || die runner "expected 13 evaluations, ran $ran"
          echo "tests-process: 13 cells, every exit read unpiped, every death on its named channel, every count read" > $out
        ''
        + ''
          cat "$out"
        ''
      );
    };
}
