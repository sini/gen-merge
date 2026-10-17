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
#
# den-hoag-3jyxf's two nta-* cells relocated to gen-aspects' own runner (den-hoag-n6dh7 SCC build,
# ADR-0037) — see `tests-process-cells.nix`'s header for why.
{ inputs, ... }:
{
  perSystem =
    { pkgs, ... }:
    let
      # den-hoag-06toi stage 1: nixpkgs' modules.sh against this engine, scored against its baseline.
      modulesSh = import ./modules-sh.nix { inherit pkgs inputs; };
    in
    {
      apps.modules-sh.program = "${modulesSh}/bin/modules-sh";
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
          export genAlgebraSrc=${inputs.gen-types.inputs.gen-algebra}
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
          # den-hoag-06toi stage 1 runs FIRST and its status is held to the end, so a red cell below
          # (which stops this runner) never hides its report, nor its report the cells.
          modulesRc=0
          ${modulesSh}/bin/modules-sh || modulesRc=$?
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
              --argstr genAlgebraSrc "$genAlgebraSrc" \
              --argstr genMemoSrc "$genMemoSrc" \
              --argstr genScopeSrc "$genScopeSrc" \
              --argstr label "$label" \
              --argstr nixpkgsSrc "$nixpkgsSrc" \
              "$cells" 2> "$TMPDIR/err") || rc=$?
            ran=$((ran + 1))
          }
          # callsOf <arm>: runs one cell with the evaluator's statistics on, requires exit 0, and
          # leaves the process's own nrFunctionCalls in `calls`. A stats file with no count is a
          # broken instrument and dies as one, never a zero.
          callsOf() {
            export NIX_SHOW_STATS=1 NIX_SHOW_STATS_PATH="$TMPDIR/stats"
            rm -f "$TMPDIR/stats"
            evalArm "$1"
            unset NIX_SHOW_STATS NIX_SHOW_STATS_PATH
            [ "$rc" -eq 0 ] || die "$1" "expected exit 0, got $rc"
            calls=$(tr -d ' \n' < "$TMPDIR/stats" | grep -o '"nrFunctionCalls":[0-9]*' | cut -d: -f2 || true)
            [ -n "$calls" ] || die "$1" "the evaluator wrote no nrFunctionCalls to $TMPDIR/stats: cannot measure"
          }

          # thunksOf <arm>: as callsOf, leaving the process's own nrThunks in `thunks`.
          thunksOf() {
            export NIX_SHOW_STATS=1 NIX_SHOW_STATS_PATH="$TMPDIR/stats"
            rm -f "$TMPDIR/stats"
            evalArm "$1"
            unset NIX_SHOW_STATS NIX_SHOW_STATS_PATH
            [ "$rc" -eq 0 ] || die "$1" "expected exit 0, got $rc"
            thunks=$(tr -d ' \n' < "$TMPDIR/stats" | grep -o '"nrThunks":[0-9]*' | cut -d: -f2 || true)
            [ -n "$thunks" ] || die "$1" "the evaluator wrote no nrThunks to $TMPDIR/stats: cannot measure"
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

          # den-hoag-9oc7y: a rename cycle dies on the guard's named channel under the staged passes;
          # a declaration reading a field its target lacks dies as nixpkgs does, and a module catching
          # a stamped-view refusal reaches the recursion abort (the stated prices).
          evalArm rename-cycle-read
          [ "$rc" -ne 0 ] || die rename-cycle-read "expected a by-name refusal, got exit 0 with '$val'"
          grep -Fq "gen-merge: a module read \`options' while its own declarations were being folded" "$TMPDIR/err" || die rename-cycle-read "refusal is not the declaration guard's named refusal"
          evalArm leaf-reads-absent-field
          [ "$rc" -ne 0 ] || die leaf-reads-absent-field "expected a death, got exit 0 with '$val'"
          grep -q "attribute 'example' missing" "$TMPDIR/err" || die leaf-reads-absent-field "death is not the missing-attribute channel"
          evalArm catch-group
          [ "$rc" -ne 0 ] || die catch-group "expected a death, got exit 0 with '$val'"
          grep -q 'infinite recursion encountered' "$TMPDIR/err" || die catch-group "death is not the infinite-recursion channel"

          # den-hoag-n6dh7 U2-g: ONE gen-scope evaluation per `evalModuleTree`, however many nested
          # trees its value holds. The spy counts `scope.eval` calls; its live control reads 2.
          for arm in one-eval-flat one-eval-sub-one one-eval-attrs-two one-eval-list-two one-eval-sub-empty one-eval-deep one-eval-np-attrs; do
            evalArm "$arm"
            [ "$rc" -eq 0 ] || die "$arm" "expected exit 0, got $rc"
            n=$(traced)
            [ "$n" = "1" ] || die "$arm" "expected 1 evaluation, the spy counted $n"
          done
          # den-hoag-olrmz G3: one `verify` copy of a nesting container declared twice reads 1 and serves.
          evalArm one-eval-verify-shared
          [ "$rc" -eq 0 ] || die one-eval-verify-shared "expected exit 0, got $rc"
          [ "$val" = "1" ] || die one-eval-verify-shared "expected value 1, got '$val'"
          n=$(traced)
          [ "$n" = "1" ] || die one-eval-verify-shared "expected 1 evaluation, the spy counted $n"
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

          # den-hoag-type-description-parity-5k1l1: a cycle closed through a foreign record's
          # `description` dies in the infinite-recursion channel (the argued exception), and the same
          # shapes over an acyclic foreign member answer nixpkgs' phrase.
          for arm in phrase-cycle-gen-through-foreign phrase-cycle-foreign-under-gen phrase-cycle-stated-from-base; do
            evalArm "$arm"
            [ "$rc" -ne 0 ] || die "$arm" "expected a death, got exit 0 with '$val'"
            grep -q 'infinite recursion encountered' "$TMPDIR/err" || die "$arm" "death is not the infinite-recursion channel"
          done
          evalArm phrase-cycle-stated-from-base-control
          [ "$rc" -eq 0 ] || die phrase-cycle-stated-from-base-control "expected exit 0, got $rc"
          [ "$val" = '"signed integer or list of (signed intege"' ] || die phrase-cycle-stated-from-base-control "expected the base's phrase, got '$val'"
          evalArm phrase-cycle-control
          [ "$rc" -eq 0 ] || die phrase-cycle-control "expected exit 0, got $rc"
          [ "$val" = '"null or (list of signed integer) | list of (null or string)"' ] || die phrase-cycle-control "expected nixpkgs' phrases, got '$val'"

          # den-hoag-23dqs: a foreign knot closed through a gen door dies in the infinite-recursion
          # channel at construction (the argued exception); crossed once, the same knot answers.
          for arm in foreign-knot-mkoptiontype foreign-knot-derivetype; do
            evalArm "$arm"
            [ "$rc" -ne 0 ] || die "$arm" "expected a death, got exit 0 with '$val'"
            grep -q 'infinite recursion encountered' "$TMPDIR/err" || die "$arm" "death is not the infinite-recursion channel"
          done
          evalArm foreign-knot-crossed-once
          [ "$rc" -eq 0 ] || die foreign-knot-crossed-once "expected exit 0, got $rc"
          [ "$val" = '[ 1 [ 2 ] ]' ] || die foreign-knot-crossed-once "expected [ 1 [ 2 ] ], got '$val'"

          # den-hoag-fpxsd: a submodule module whose `_module.args` key set reads `name` dies in the
          # infinite-recursion channel, as nixpkgs' `submoduleWith` does; a value reading it answers.
          evalArm name-keyset-reads-name
          [ "$rc" -ne 0 ] || die name-keyset-reads-name "expected a death, got exit 0 with '$val'"
          grep -q 'infinite recursion encountered' "$TMPDIR/err" || die name-keyset-reads-name "death is not the infinite-recursion channel"
          evalArm name-keyset-control
          [ "$rc" -eq 0 ] || die name-keyset-control "expected exit 0, got $rc"
          [ "$val" = '"x:x"' ] || die name-keyset-control "expected value \"x:x\", got '$val'"

          # den-hoag-iaram: a type that is its own derivation dies at construction in the
          # infinite-recursion channel, and an unguarded cycle's out-of-domain check in the call-depth
          # channel (the argued exceptions); a guarded cycle through a derivation answers.
          evalArm cyclic-derive-self
          [ "$rc" -ne 0 ] || die cyclic-derive-self "expected a death, got exit 0 with '$val'"
          grep -q 'infinite recursion encountered' "$TMPDIR/err" || die cyclic-derive-self "death is not the infinite-recursion channel"
          evalArm cyclic-unguarded
          [ "$rc" -ne 0 ] || die cyclic-unguarded "expected a death, got exit 0 with '$val'"
          grep -q 'max-call-depth exceeded' "$TMPDIR/err" || die cyclic-unguarded "death is not the call-depth channel"
          evalArm cyclic-guarded-control
          [ "$rc" -eq 0 ] || die cyclic-guarded-control "expected exit 0, got $rc"
          [ "$val" = '[ true false ]' ] || die cyclic-guarded-control "expected [ true false ], got '$val'"

          # den-hoag-qbrq9: an over-approximately keyed position's walk is linear in its definitions:
          # one position of n definitions, each with its own key, at n = 100, 400, 1600. Linear growth
          # makes the second difference in function calls 4x the first; it must stay under 5x. A
          # per-key scan of the definitions read 13.9x (547500 then 7590000 calls on Nix 2.34.8).
          for n in 100 400 1600; do
            callsOf "key-walk-wide-$n"
            [ "$val" = "$n" ] || die "key-walk-wide-$n" "expected value $n, got '$val'"
            eval "kw$n=$calls"
          done
          [ $((kw1600 - kw400)) -lt $((5 * (kw400 - kw100))) ] || die key-walk-wide-1600 "function calls grow faster than linear in the definitions: $kw100 / $kw400 / $kw1600"

          # den-hoag-hnd82 (ADR-0032): the cost of a met record, as thunks per option between n = 100 and
          # 200, n options each declared twice and defined. The bounds are the landed figures, in THUNKS: they
          # read the same on Nix, Determinate and Lix, while allocated bytes move with the loading route. An
          # optimization lowers its bound in the same change. This row was above its nixpkgs reference at the
          # anchor, so under ADR-0032 a rise is authorized only after a minimality attempt, and is re-anchored
          # in the landing commit that makes it. den-hoag-5f99v re-anchored -1 / -2 / +1 / +1: the meet reading a gen
          # copy's replaced `verify` once on the merged value (ADR-0039's converse), after its minimality attempt,
          # with the replaced-`verify` stamp tested by comparison, which allocates nothing. den-hoag-410ri lowered
          # each by 2: a level's key grouping binds a pushed definition's fields as formals. den-hoag-1yqkr lowered
          # s3 by 1: a held record's operands are kept without a filter. den-hoag-c922w lowered box by 28: a
          # property-free definition list is folded without the passes, and a container root over a leaf chain
          # is not walked. den-hoag-k4f4g lowered s2 and s3 by 10: a met record over a foreign join lays no
          # mint fields.
          for bound in val:347 box:698 s2:869 s3:462; do
            mode=''${bound%%:*} max=''${bound#*:}
            thunksOf "met-cost-$mode-100"
            [ "$val" = "100" ] || die "met-cost-$mode-100" "expected value 100, got '$val'"
            t100=$thunks
            thunksOf "met-cost-$mode-200"
            [ "$val" = "200" ] || die "met-cost-$mode-200" "expected value 200, got '$val'"
            per=$(((thunks - t100) / 100))
            [ "$per" -le "$max" ] || die "met-cost-$mode-200" "a met record ($mode) costs $per thunks per option, over its bound $max; ADR-0032: this row is above its reference, so a rise is authorized only after a minimality attempt, re-anchored in the landing commit"
            echo "met-cost $mode: $per thunks per option (bound $max)"
          done

          # den-hoag-y4w78 (ADR-0032): the spine's cost over a chain of `listOf` over a submodule, as the thunks to read
          # its module set at depth 30 over depth 1. A gen container answers its own `getSubModules = null` once the rest
          # of its chain bottoms out, and for a container stating none of its own that field is its own walk of the rest,
          # so the cost is quadratic in the depth and bounded by the walk's fuel (32). The bound is the landed figure, in
          # THUNKS; an optimization lowers it in the same change, and a rise needs an owner reading.
          thunksOf spine-cost-1
          [ "$val" = "1" ] || die spine-cost-1 "expected value 1, got '$val'"
          t1=$thunks
          thunksOf spine-cost-30
          [ "$val" = "1" ] || die spine-cost-30 "expected value 1, got '$val'"
          per=$((thunks - t1))
          [ "$per" -le "4466" ] || die spine-cost-30 "the spine costs $per thunks from depth 1 to 30, over its bound 4466"
          echo "spine-cost: $per thunks from depth 1 to 30 (bound 4466)"

          # den-hoag-8tmd5 (ADR-0032): the staged declaration passes' cost, as the thunks a rename's alias adds over
          # the same option defined directly. The passes are tried once at a constant depth and an earlier pass is
          # built only when a later pass reads it, so the cost does not grow with that depth: a pass that forced the
          # pass below it would add a constant per pass, nearly three times this bound at the landed depth. The bound
          # is the landed figure under the evaluator reading highest (Lix), in THUNKS; an optimization lowers it in the
          # same change.
          thunksOf staged-cost-plain
          [ "$val" = "3" ] || die staged-cost-plain "expected value 3, got '$val'"
          t0=$thunks
          thunksOf staged-cost-rename
          [ "$val" = "3" ] || die staged-cost-rename "expected value 3, got '$val'"
          per=$((thunks - t0))
          [ "$per" -le "1406" ] || die staged-cost-rename "a rename adds $per thunks over a direct definition, over its bound 1406; ADR-0032: a rise is authorized only after a minimality attempt, re-anchored in the landing commit"
          echo "staged-cost: $per thunks for a rename over a direct definition (bound 1406)"

          # den-hoag-7o7i9 (ADR-0032): a module graph read, as thunks per module between n = 100 and 400, every
          # node's `disabled` forced. With no removal the bound is the figure before removal existed (gen-merge
          # e3e1305), so a per-node re-walk of the closure (x92 at n = 400) reds it; with one removal the marking
          # is one walk of the tree. The bounds are the landed figures, in THUNKS.
          for bound in graph-cost:16 graph-cost-removal:69; do
            cell=''${bound%%:*} max=''${bound#*:} want=0
            [ "$cell" = graph-cost ] || want=1
            thunksOf "$cell-100"
            [ "$val" = "$want" ] || die "$cell-100" "expected value $want, got '$val'"
            t100=$thunks
            thunksOf "$cell-400"
            [ "$val" = "$want" ] || die "$cell-400" "expected value $want, got '$val'"
            per=$(((thunks - t100) / 300))
            [ "$per" -le "$max" ] || die "$cell-400" "a module graph read costs $per thunks per module, over its bound $max"
            echo "$cell: $per thunks per module (bound $max)"
          done

          # 0/0 is a false pass: the runner must have executed every cell above.
          [ "$ran" = "49" ] || die runner "expected 49 evaluations, ran $ran"
          echo "tests-process: 49 cells, every exit read unpiped, every death on its named channel, every count read" > $out
        ''
        + ''
          cat "$out"
          exit "$modulesRc"
        ''
      );
    };
}
