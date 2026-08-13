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
  # ── the sub-protocol refusal and its control share one skeleton ─────────────────────────────
  # A type carrying an ELEMENT TYPE owes the three sub-protocol answers. These three fixtures are
  # the same hand-built type differing in exactly which of them it supplies, so what separates
  # refusal from construction is that and nothing else — not the hand-building, which the control
  # below does identically and which succeeds.
  rackOf =
    extra:
    gm.mkOptionType (
      {
        name = "rackOf";
        elemType = t.str;
        getSubOptions = _prefix: { };
        getSubModules = null;
      }
      // extra
    );

  # ── the declaration-merge refusal and its control share one skeleton ────────────────────────
  # One option, declared in two named files, each declaration carrying a type and nothing else.
  # The three fixtures below differ in exactly which types those are, so what separates refusal
  # from merge is the type algebra's answer about the pair and nothing else.
  declaredTwice =
    aType: bType:
    (gm.evalModuleTree {
      modules = [
        {
          _file = "a.nix";
          options.x = gm.mkOption { type = aType; };
        }
        {
          _file = "b.nix";
          options.x = gm.mkOption { type = bType; };
        }
      ];
    }).options.x.type.name;

  # The same redeclaration one level down, inside a `submodule` — the nested eval carries a
  # non-empty `prefix`. `sub-a.nix` always declares `str`; the second type and its default are the
  # only things that vary between the refusal and its control.
  subHost = bType: bDefault: {
    modules = [
      {
        _file = "outer.nix";
        options.host = gm.mkOption {
          type = t.submodule [
            {
              _file = "sub-a.nix";
              options.inner = gm.mkOption {
                type = t.str;
                default = "A";
              };
            }
            {
              _file = "sub-b.nix";
              options.inner = gm.mkOption {
                type = bType;
                default = bDefault;
              };
            }
          ];
          default = { };
        };
      }
    ];
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
          msg = "^gen-merge: option `rack\\.stray' does not exist \\(no freeformType to absorb it\\)$";
        };
      };
      # The collision refusal names the option that collided, which is the one piece of the
      # module set the author has to go edit.
      test-leaf-group-collision-refusal-names-the-option = {
        expr = realize collision;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `thing' is declared both as an option and as an option-group \\(leaf/group collision\\)$";
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

    # A redeclared option whose two types do not merge is refused BY NAME. The message is the whole
    # of what the author gets — there is no bad intermediate to inspect, because the point of the
    # rule is that one is never built.
    #
    # ★ EVERY PATTERN HERE IS ANCHORED `^…$`, for the reason stated below the sub-protocol cells.
    # These messages DO carry ERE metacharacters — the parenthesised type pair, and the `.` in every
    # file name — so each is escaped and the anchors are left to carry only the ends.
    flake.testsError.declaration-merge = {
      # The message names the option, the two types that could not be combined, and the files that
      # declared them: an author who is told only "types do not merge" still has to find both.
      test-unmergeable-redeclaration-refused-by-name = {
        expr = declaredTwice t.str t.int;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(`string' and `int'\\); declared in a\\.nix, b\\.nix$";
        };
      };
      # THE PARAMETRIC ARM. A gen-types parametric leaf refuses `typeMerge` by construction — its
      # parameters sit behind the checker closures, so there is no payload to compare and "same
      # name" would be a wrong answer, not a cheap one. Two `enum "e"` declarations over DIFFERENT
      # value sets therefore refuse, and the message shows the two names matching while the pair
      # still does not merge — which is exactly what distinguishes this arm from the one above.
      test-parametric-redeclaration-refused-though-names-match = {
        expr = declaredTwice (t.enum "e" [ "a" ]) (t.enum "e" [ "b" ]);
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(`e' and `e'\\); declared in a\\.nix, b\\.nix$";
        };
      };
      # The path is the FULL option path, and the file list is EVERY declaring file rather than the
      # two the merge happened to be holding: `a.nix` and `b.nix` merge with each other before
      # `c.nix` refuses, and a message naming only the pair at the point of refusal would send the
      # author to two of the three modules they have to reconcile.
      test-refusal-names-the-full-path-and-every-declaring-file = {
        expr =
          (gm.evalModuleTree {
            modules = [
              {
                _file = "a.nix";
                options.rack.slot = gm.mkOption { type = t.str; };
              }
              {
                _file = "b.nix";
                options.rack.slot = gm.mkOption { type = t.str; };
              }
              {
                _file = "c.nix";
                options.rack.slot = gm.mkOption { type = t.int; };
              }
            ];
          }).options.rack.slot.type.name;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `rack\\.slot' is declared with types that do not merge \\(`string' and `int'\\); declared in a\\.nix, b\\.nix, c\\.nix$";
        };
      };
      # INSIDE A SUBMODULE the engine runs with a non-empty `prefix`, so the loc the merge reports
      # is prefixed while the modules it is looking the declaration up in are not. The message has
      # to name the OUTER path and the INNER files: `host.inner`, declared in the submodule's own
      # two modules and not in the one that declared `host`. Mismatch the two and the path survives
      # while the file list comes back empty, which is a refusal that names half of what it needs.
      test-refusal-inside-a-submodule-names-outer-path-and-inner-files = {
        expr = realize (subHost t.int 7);
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `host\\.inner' is declared with types that do not merge \\(`string' and `int'\\); declared in sub-a\\.nix, sub-b\\.nix$";
        };
      };
      # LIVE CONTROLS, same run, same skeletons: a pair the algebra DOES merge is not refused — at
      # the root, where the merged declaration answers with the algebra's type, and inside the
      # submodule, where it evaluates to a value. Without them the cells above are consistent with a
      # declaration path that refuses every redeclaration.
      test-mergeable-redeclaration-is-not-refused-control = {
        expr = declaredTwice t.str t.str;
        expected = "string";
      };
      test-mergeable-redeclaration-in-a-submodule-control = {
        expr = cfg (subHost t.str "B");
        expected = {
          host = {
            inner = "B";
          };
        };
      };
    };

    # The sub-protocol refusal fires at CONSTRUCTION, so there is no bad intermediate to inspect and
    # nothing to assert about a value — only the message. These cells are why the second output
    # exists.
    #
    # ★ EVERY PATTERN HERE IS ANCHORED `^…$`. nix-unit SEARCHES `expectedError.msg` rather than
    # matching it whole, so an unanchored pattern pins a SUBSTRING: it would keep passing if the
    # message grew a wrong clause on either side, which is most of what a message assertion is for.
    # Neither message below contains an ERE metacharacter, so nothing needs escaping and the anchors
    # carry the whole of the exactness.
    flake.testsError.structural-sub-protocol = {
      # The refusal names the TYPE and the field it did not supply — the two things the author has
      # to know. A refusal saying only "incomplete type" would leave both to be re-derived.
      test-element-carrier-missing-one-field-refused-by-name = {
        expr = rackOf { };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the structural type `rackOf' carries an element type but does not supply `substSubModules'; a structural type may not inherit a leaf's protocol answer$";
        };
      };
      # A MODULE-SET carrier is in the domain by the other arm, and the message names EVERY missing
      # field in protocol order rather than stopping at the first.
      test-module-set-carrier-names-every-missing-field = {
        expr = gm.mkOptionType {
          name = "slotOf";
          getSubModules = [ skeleton ];
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the structural type `slotOf' carries a module set but does not supply `getSubOptions', `substSubModules'; a structural type may not inherit a leaf's protocol answer$";
        };
      };
      # LIVE CONTROL, same run, same skeleton: supply the third field and the SAME hand-built type
      # constructs and answers. Without it both cells above are consistent with a surface that
      # refuses every hand-built type carrying an element.
      test-element-carrier-supplying-all-three-constructs-control = {
        expr =
          let
            ty = rackOf { substSubModules = _m: null; };
          in
          {
            inherit (ty) name;
            subOptions = ty.getSubOptions [ ];
            subModules = ty.getSubModules;
          };
        expected = {
          name = "rackOf";
          subOptions = { };
          subModules = null;
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
