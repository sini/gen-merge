# THE SECOND TEST OUTPUT — cells whose subject is an ERROR, and the runner that reads them.
#
# The engine refuses several shapes BY NAME: an undeclared key names the option path it could not
# place, a leaf/group collision names the colliding option. That each refuses is a boolean and
# `builtins.tryEval` can assert it — the suites under ./tests do exactly that in a dozen places.
# WHICH option a refusal named is a claim about the message, and `tryEval` discards the message
# (`{ success = false; value = false; }`). The only assertion available for it is nix-unit's
# `expectedError`.
#
# ★ WHY A SECOND OUTPUT RATHER THAN A SECOND SUITE. `gen-harness.lib.mkCi` builds `checks.default`
# from a homegrown asserter that evaluates `t.expr == t.expected` UNCONDITIONALLY, and it
# quantifies over `config.flake.tests` and nothing else (`gen-harness/flakeModule.nix`). A cell
# with no `expected` and a throwing `expr` therefore CRASHES that batch gate rather than failing
# it — measured here, not adopted: with the first cell below moved into `flake.tests`,
# `nix flake check ./ci` died carrying this file's own refusal message rather than reporting a
# failed cell. Hosting these cells on `flake.testsError` puts them outside the asserter's
# quantifier while keeping them live on the nix-unit path.
#
# ★ AND THE SPLIT IS STRUCTURAL, NOT CONVENTIONAL. This file is NOT under `./tests`, which is the
# whole of `testModules`, so which cells land in which output depends on no filter predicate and
# no ignore convention that a dependency bump could redefine. It reaches the flake through
# `mkCi`'s `extraModules`.
#
# BOTH OUTPUTS NEED RUNNING, so both get a hook. The wrapper `gen-harness`'s `ci` hook builds
# bakes `./ci#tests` into its own text and cannot be pointed at this one; the `ci-error` hook
# below is its counterpart, declared through the same `pre-commit.settings.hooks` surface under a
# distinct id so the two merge rather than collide.
#
#   nix-unit --flake ./ci#tests        # the suites
#   nix-unit --flake ./ci#testsError   # these cells
{
  lib,
  name,
  genMerge,
  genInputs,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  cfg = args: (gm.evalModuleTree args).config;
  # `deepSeq` is the forcing idiom the ./tests suites use: the refusals below fire while the
  # config tree is realized, so a shallow force would not reach them.
  realize = args: builtins.deepSeq (cfg args) null;

  # ── the refusal pair and its control share one skeleton ────────────────────────────────────
  # `rack.slot` is declared; `rack.stray` is not. The three fixtures differ in exactly one module,
  # so what separates refusal from absorption is that module and nothing else.
  skeleton = {
    options.rack.slot = gm.mkOption {
      type = t.str;
      default = "s";
    };
  };
  stray = {
    rack.stray = 1;
  };
  # Declaring `thing` as a leaf in one module and as an option-group in another: the decl merge
  # cannot `//` these together without emitting wrong bytes, so it refuses.
  collision = {
    modules = [
      {
        options.thing = gm.mkOption {
          type = t.str;
          default = "x";
        };
      }
      {
        options.thing.sub = gm.mkOption {
          type = t.str;
          default = "y";
        };
      }
    ];
  };
in
{
  # Same type as `flake.tests` (`gen-harness/flakeModule.nix`), because it is the same kind of
  # thing read by the same runner — only the assertion the cells carry differs.
  options.flake.testsError = lib.mkOption {
    type = lib.types.lazyAttrsOf (lib.types.lazyAttrsOf lib.types.raw);
    default = { };
    description = "Test suites whose cells assert an ERROR: { suite.test = { expr; expectedError; }; }. Read by `nix-unit --flake ./ci#testsError`; deliberately outside `flake.tests`, which the batch asserter quantifies over.";
  };

  config = {
    flake.testsError.refusal-messages = {
      # The message NAMES THE FULL PATH of the key it could not place — `rack.stray`, not `rack`
      # and not a count. A refusal that only said "undeclared key" would leave the caller to
      # re-derive which one, over a tree the engine has already walked.
      test-undeclared-key-refusal-names-the-full-path = {
        expr = realize {
          modules = [
            skeleton
            stray
          ];
        };
        expectedError = {
          type = "ThrownError";
          msg = ".*option `rack\\.stray' does not exist \\(no freeformType to absorb it\\).*";
        };
      };
      # The collision refusal names the option that collided, which is the one piece of the
      # module set the author has to go edit.
      test-leaf-group-collision-refusal-names-the-option = {
        expr = realize collision;
        expectedError = {
          type = "ThrownError";
          msg = ".*option `thing' is declared both as an option and as an option-group \\(leaf/group collision\\).*";
        };
      };
      # LIVE CONTROL, same run: the same skeleton and the same stray key, plus a `freeformType`
      # to absorb it, evaluates — and the declared sibling survives alongside the absorbed key.
      # Without it the two cells above are consistent with a surface that refuses everything. It
      # is an `expected` cell in an `expectedError` output on purpose: a control has to run in
      # the same invocation as the thing it controls, or it controls nothing.
      test-freeform-absorbs-the-same-key-control = {
        expr = cfg {
          modules = [
            skeleton
            stray
            { freeformType = t.lazyAttrsOf t.raw; }
          ];
        };
        expected = {
          rack = {
            slot = "s";
            stray = 1;
          };
        };
      };
    };

    # THE SECOND HOOK. A second output that nothing runs is a second output that rots.
    perSystem =
      { pkgs, system, ... }:
      {
        pre-commit.settings.hooks.ci-error = {
          enable = true;
          name = "ci-error";
          description = "Run nix-unit error-assertion tests";
          entry = "${
            pkgs.writeShellApplication {
              name = "${name}-ci-nix-unit-error";
              runtimeInputs = [ genInputs.nix-unit.packages.${system}.default ];
              text = ''
                exec nix-unit --flake ./ci#testsError "$@"
              '';
            }
          }/bin/${name}-ci-nix-unit-error";
          files = "\\.nix$";
          pass_filenames = false;
        };
      };
  };
}
