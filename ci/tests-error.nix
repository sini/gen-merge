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
  nixpkgsLib,
  interface,
  genMergeVocab,
  genMergeWith,
  genTypes,
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

  # ── the functor refusal's subject: a BYTE-IDENTICAL RECONSTRUCTION of a real consumer ───────
  # This is gen-aspects' `aspectsRootWith` (its `lib/types.nix`), rebuilt here field for field: a
  # container written in the nixpkgs convention, whose `functor.payload` is the element type BARE
  # rather than a `{ elemType = …; }` row, and whose `binOp` defers to the two elements' own
  # relation. The reconstruction is the subject rather than a minimal fixture because the defect
  # this refusal converts was MEASURED on it — a minimal one would leave open whether the shape a
  # consumer actually ships is the shape that fires.
  mergeElemTypes = a: b: if a ? typeMerge && b ? functor then a.typeMerge b.functor else null;
  aspectsRootWith =
    elemType:
    gm.mkOptionType {
      name = "aspectsRoot";
      inherit elemType;
      nestedTypes = { inherit elemType; };
      functor = {
        name = "aspectsRoot";
        payload = elemType;
        binOp = a: b: if b == null then null else mergeElemTypes a b;
        type = aspectsRootWith;
      };
      getSubOptions = prefix: elemType.getSubOptions (prefix ++ [ "<name>" ]);
      getSubModules = elemType.getSubModules or null;
      substSubModules =
        m: aspectsRootWith (if elemType ? substSubModules then elemType.substSubModules m else elemType);
      merge = _loc: defs: (builtins.head defs).value;
    };

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

  # ── the union refusal and its controls share one skeleton ───────────────────────────────────
  # `x` is `either (listOf str) str`, whose two members accept exactly what the other rejects, and
  # every fixture below declares it in `decl.nix` and defines it from named files. They differ in
  # the DEFINITIONS and in nothing else, so what separates a refusal from a merge is the definition
  # set — not the type, not the declaration, and not which file declared it.
  unionOf =
    loc: defs:
    (gm.evalModuleTree {
      modules = [
        {
          _file = "decl.nix";
          options = lib.setAttrByPath loc (gm.mkOption { type = t.either (t.listOf t.str) t.str; });
        }
      ]
      ++ map (d: {
        _file = d.file;
        config = lib.setAttrByPath loc d.value;
      }) defs;
    }).config;

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
      # THE PARAMETRIC ARM, post-k1uv (43adfdc). A gen-types parametric leaf's `typeMergeRel` decides
      # by MINTED CONSTRUCTION, not by name — so "same name" would still be a wrong answer for two
      # `enum "e"` declarations over DIFFERENT value sets, but the reason is no longer "there is
      # nothing to compare": the mint compares them fine, and says unequal. What is actually missing is
      # a channel back to their component values (an enum's `elems`, …) to attempt a value-level
      # reconciliation the way nixpkgs' own `enum` unions two differing sets — that channel does not
      # exist (den-hoag-parametric-merge-unlock-6wb87). So the pair still refuses, and the message shows
      # the two names matching while the pair still does not merge — which is exactly what distinguishes
      # this arm from the one above.
      #
      # ★ AND IT NOW SAYS WHY, WHICH IS THE HALF THAT WAS MISSING. The pinned message used to be the
      # bare pair, so this cell read as "`e' and `e' do not merge" and left the reader to work out
      # that a parametric leaf is a different case from a name mismatch — the two arms of this suite
      # were indistinguishable from their messages alone. The type-merge relation carries a REASON and
      # the declaration site reports it where one is supplied, so the arm now names itself. That
      # channel existed before and had no live producer: every type carried the foreign protocol and
      # no relation, so the site always fell back to reconstructing the pair from two names.
      test-parametric-redeclaration-refused-though-names-match = {
        expr = declaredTwice (t.enum "e" [ "a" ]) (t.enum "e" [ "b" ]);
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' is declared with types that do not merge \\(`e' and `e', which mint to different constructions and carry no readable component values to reconcile\\); declared in a\\.nix, b\\.nix$";
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

    # A UNION merges every definition through a member that accepts it, or refuses by name. These
    # cells are the only assertion available for that refusal: the shape it replaces was an
    # INTERPRETER type error — `expected a list but found a string: "b"` — which escapes
    # `builtins.tryEval`, so before the rule there was nothing for any in-language cell to observe
    # and after it there is nothing but the message. The before/after exit-code pair those cells
    # cannot carry is `ci/bench/either-totality.sh`.
    #
    # ★ EVERY PATTERN HERE IS ANCHORED `^…$`, for the reason stated below the sub-protocol cells.
    # These messages DO carry ERE metacharacters — the parenthesised member clause and the `.` in
    # every file name — so each is escaped and the anchors are left to carry only the ends.
    flake.testsError.union-merge = {
      # The definition set the interpreter used to be handed. The message names the option and, per
      # member, the files whose definitions THAT member could not take: an author told only "the
      # definitions do not agree" still has to work out which member was in play and which file
      # broke it.
      test-mixed-definitions-refused-by-name = {
        expr = builtins.deepSeq (unionOf
          [ "x" ]
          [
            {
              file = "list.nix";
              value = [ "a" ];
            }
            {
              file = "str.nix";
              value = "b";
            }
          ]
        ) null;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' has definitions no single `either' member accepts \\(`listOf' rejects str\\.nix; `string' rejects list\\.nix\\)$";
        };
      };
      # EVERY offending definition is named, not the pair a dispatch happened to be holding. Two
      # list definitions and one string: the member that takes lists rejects one file, the member
      # that takes strings rejects two, and an author reconciling only the first collision the
      # interpreter would have reported would leave a definition set that still refuses.
      #
      # ★ THE FILE LIST IS IN DEFINITION ORDER — the order the merge is handed them, which is the
      # reverse of the authored module order and is why `two.nix` precedes `one.nix` here. It is a
      # set of files to go edit and no ordering is claimed for it; the cell pins the order anyway,
      # so a fold that starts handing definitions over differently says so here rather than in a
      # consumer's diagnostics. The declaration-merge messages above name files in AUTHORED order
      # because they read a site list, which this path does not have.
      test-refusal-names-every-definition-each-member-rejects = {
        expr = builtins.deepSeq (unionOf
          [ "x" ]
          [
            {
              file = "one.nix";
              value = [ "a" ];
            }
            {
              file = "two.nix";
              value = [ "b" ];
            }
            {
              file = "three.nix";
              value = "c";
            }
          ]
        ) null;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `x' has definitions no single `either' member accepts \\(`listOf' rejects three\\.nix; `string' rejects two\\.nix, one\\.nix\\)$";
        };
      };
      # The path is the FULL option path. A union sitting under a nested option is where a message
      # can report the leaf name and read as correct, which sends the author looking for an option
      # called `slot`.
      test-refusal-names-the-full-option-path = {
        expr = builtins.deepSeq (unionOf
          [ "rack" "slot" ]
          [
            {
              file = "list.nix";
              value = [ "a" ];
            }
            {
              file = "str.nix";
              value = "b";
            }
          ]
        ) null;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: option `rack\\.slot' has definitions no single `either' member accepts \\(`listOf' rejects str\\.nix; `string' rejects list\\.nix\\)$";
        };
      };
      # LIVE CONTROLS, same run, same skeleton — and a run in which these do not pass says nothing
      # about the cells above, which are equally consistent with a union that refuses everything.
      # Definitions one member takes WHOLE still merge through it, on both members: two lists merge
      # into one list through the member that accepts lists, and a lone string merges through the
      # member that accepts strings. The list value is pinned exactly, because the obligation on
      # this rule is that a definition set which merged before merges to the same bytes.
      test-homogeneous-list-definitions-still-merge-control = {
        expr =
          unionOf
            [ "x" ]
            [
              {
                file = "one.nix";
                value = [ "a" ];
              }
              {
                file = "two.nix";
                value = [ "b" ];
              }
            ];
        expected = {
          x = [
            "b"
            "a"
          ];
        };
      };
      test-string-definition-merges-through-the-other-member-control = {
        expr =
          unionOf
            [ "x" ]
            [
              {
                file = "str.nix";
                value = "b";
              }
            ];
        expected = {
          x = "b";
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
      # `deferredModule` HAS a module set and it is empty, so it answers the sub-protocol itself —
      # including the rebuild. Over a NON-EMPTY set there is nothing it could build: the type carries
      # no static-module parameter, so the modules could only be dropped, and a rebuild that silently
      # discards what it was handed is the wrong value with no diagnostic. It refuses, naming the type
      # and what it cannot do with the set.
      test-deferredModule-rebuild-over-non-empty-set-refused-by-name = {
        expr = t.deferredModule.substSubModules [ skeleton ];
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: `deferredModule' cannot be rebuilt over a module set of 1; it carries no static modules and dropping them would lose the declarations silently$";
        };
      };
      # LIVE CONTROL, same run, same type: over its OWN empty set the rebuild returns the type. This
      # is the argument nixpkgs `fixupOptionType` actually passes on a mount, so without this row the
      # refusal above is equally consistent with a `substSubModules` that refuses everything — which
      # would break every mounted `deferredModule` option rather than only the impossible rebuild.
      test-deferredModule-rebuild-over-empty-set-returns-the-type-control = {
        expr =
          let
            ty = t.deferredModule.substSubModules [ ];
          in
          {
            inherit (ty) name;
            subModules = ty.getSubModules;
          };
        expected = {
          name = "deferredModule";
          subModules = [ ];
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

    # ── the boundary's own refusals ───────────────────────────────────────────────────────────────
    # The rule above has TWO arms, and until now only one of them was armed. A descriptor written in
    # the foreign protocol's words is refused at the IMPORT environment and the message names the
    # foreign fields, because that is the vocabulary its author wrote in. A record built in gen's own
    # words is refused at gen's own constructor and the message names the gen formals. Both are the
    # same rule; a suite that exercised only one of them would leave the other free to rot.
    flake.testsError.interface = {
      test-gen-record-carrying-a-parameter-without-a-substructure-is-refused = {
        expr = genMergeVocab.mkType {
          name = "crate";
          carries.element = t.str;
          recarry = c: c.element;
          substructure = {
            declares = _prefix: { };
            modules = null;
          };
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the structural type `crate' carries a parameter but does not supply `rebuild'; a type that carries something answers for it rather than inheriting a leaf's answers$";
        };
      };
      # THE FOURTH CARRIED-ROLE FORMAL, and the last one that was left un-total. The boundary reads
      # `recarry` UNCONDITIONALLY to rebuild a carrying type over another payload, so a record without
      # it used to construct, export, and then detonate with a bare missing-attribute error the moment
      # a foreign engine applied the functor — an interpreter abort naming neither the type nor the
      # field. Every shipped carrying type supplies it, which is exactly why nothing caught this: the
      # failure was reachable only by a future author, and by then the refusal would not exist.
      test-gen-record-declaring-a-role-without-a-rebuild-is-refused = {
        expr = genMergeVocab.mkType {
          name = "crate";
          carries.element = t.str;
          substructure = {
            declares = _prefix: { };
            modules = null;
            rebuild = _m: null;
          };
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the structural type `crate' carries a parameter but does not supply `recarry'; a type that carries something answers for it rather than inheriting a leaf's answers$";
        };
      };
      # LIVE CONTROL, same run, same record: supply all four formals and it constructs. Without it the
      # two cells above are equally consistent with a constructor that refuses every record carrying a
      # role, which would fail them for a reason that has nothing to do with the missing formal.
      test-control-gen-record-supplying-all-four-formals-constructs = {
        expr =
          (genMergeVocab.mkType {
            name = "crate";
            carries.element = t.str;
            recarry = c: c.element;
            substructure = {
              declares = _prefix: { };
              modules = null;
              rebuild = _m: null;
            };
          }).name;
        expected = "crate";
      };
      # AND `deferredModule` IS THE SCOPE CONTROL: it carries a module set through its substructure
      # WITHOUT declaring a role, so it has no payload to rebuild over and owes no `recarry` — it ships
      # without one and constructs. A `recarry` requirement scoped to carrying-in-general rather than
      # to the ROLE would have broken it, and this row is what says so.
      test-control-deferredModule-carries-a-module-set-and-owes-no-recarry = {
        expr = {
          declaresNoRole = !(t.deferredModule ? carries);
          hasNoRecarry = !(t.deferredModule ? recarry);
          constructedAnyway = t.deferredModule.name;
        };
        expected = {
          declaresNoRole = true;
          hasNoRecarry = true;
          constructedAnyway = "deferredModule";
        };
      };

      # A RELATION IS REQUIRED TO CROSS, and the refusal says why rather than producing a type whose
      # foreign type-merge pair was invented at the boundary. A default chosen here would be a merge
      # rule nobody in the vocabulary picked, answering for types whose author never said whether they
      # merge — which is the silent-decision shape this library refuses everywhere else.
      test-exporting-a-record-with-no-relation-is-refused = {
        expr = interface.exportType { name = "unrelated"; };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the type `unrelated' cannot be exported: it declares no type-merge relation, so the foreign protocol's `typeMerge'/`functor' pair has no gen datum to be derived from\\. Build it through the vocabulary's own constructor, which states the relation$";
        };
      };
      # LIVE CONTROL: the same record through the vocabulary's constructor, which states the relation,
      # exports and answers. The refusal is about the missing relation, not about hand-built records.
      test-control-the-same-record-through-the-constructor-exports = {
        expr = (interface.exportType (genMergeVocab.mkType { name = "unrelated"; })).name;
        expected = "unrelated";
      };

      # THE IMPORT ENVIRONMENT IS PARTIAL AND ITS REFUSAL IS NAMED. A value that is not a record, and
      # a record that answers neither vocabulary, are both things the boundary cannot translate — and
      # saying so is what keeps `mkOptionType` from silently constructing a type out of an attrset
      # that was never one.
      test-importing-a-non-record-is-refused = {
        expr = gm.mkOptionType [ "not a type" ];
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: cannot import an option type from a list; the boundary translates records, not values$";
        };
      };
      test-importing-a-record-that-answers-neither-vocabulary-is-refused = {
        expr = gm.mkOptionType { colour = "red"; };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: cannot import `colour' as an option type; it answers neither this library's vocabulary nor any field of the foreign protocol$";
        };
      };
      # LIVE CONTROL: a record answering ONE field of the foreign protocol is imported, so the refusal
      # above is about answering nothing rather than about being small.
      test-control-a-record-answering-one-protocol-field-imports = {
        expr =
          (gm.mkOptionType {
            name = "tiny";
            check = builtins.isString;
          }).name;
        expected = "tiny";
      };

      # ── A STATED RELATION THIS BOUNDARY CANNOT READ ──────────────────────────────────────────────
      # ★★★ THE SILENT ARM OF THE SAME RULE, AND IT WAS REACHED THROUGH THE PUBLIC DOOR. `functor` is
      # an export field, so it comes off with the rest of the protocol's names, and only the PAYLOAD
      # crosses back — in two spellings. A consumer stating its parameter the nixpkgs way, BARE, hit
      # neither spelling: payload and `binOp` were both discarded and the type fell back to merging on
      # its NAME ALONE, unconditionally accepting two operands its own `binOp` refuses. Measured on the
      # reconstruction below, differing elements merged where they had refused one revision earlier,
      # and nothing threw, no cell reddened and no warning was emitted. ADR-0025 §1 rules that every
      # operation returns a value or a NAMED refusal and that exceptions are enumerated, never silent;
      # this cell is that rule reaching the one arm of the import environment that was still silent.
      #
      # WHAT IT DOES NOT DO is decide how such a consumer should OBTAIN the parameterised relation —
      # that is a live question about the public protocol. The refusal converts a silent downgrade
      # into a loud one without answering it, which is why the message ends by naming both honest
      # exits rather than a single blessed one.
      test-importing-a-functor-stating-an-unreadable-parameter-is-refused = {
        expr = aspectsRootWith t.str;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the option type `aspectsRoot' supplies a `functor' this boundary cannot read: its parameter is stated as neither `payload\\.elemType' nor `payload\\.modules', so the parameter and the `binOp' that discriminates on it are discarded and `aspectsRoot' merges on its NAME ALONE — accepting two operands its own `binOp' refuses\\. State the parameter as `functor\\.payload\\.elemType' \\(or `\\.modules'\\), or drop the `functor' if merging on the name alone is what this type means$";
        };
      };
      # ★★ LIVE CONTROL, AND IT IS THE ONE THAT KEEPS THE REFUSAL PRECISE RATHER THAN MERELY LOUD. A
      # functor carrying a `binOp` but stating NO parameter — no payload, no `wrapped` — is what a
      # metadata decoration supplies, and gen-schema's `refined` (its `lib/refined.nix`) is exactly
      # this shape and is CORRECT as it stands: with nothing to discriminate on, the foreign
      # `defaultTypeMerge` IS name equality and so is the nullary relation, so no information is lost
      # and there is nothing to refuse. Every nullary foreign leaf arrives this way too. A predicate
      # keyed on "supplies a functor" instead of "states a parameter it then loses" would refuse all
      # of them, which is why this row is not optional.
      test-control-a-functor-with-no-parameter-to-discriminate-on-imports = {
        expr =
          (gm.mkOptionType {
            name = "plain";
            check = builtins.isString;
            functor = {
              name = "plain";
              payload = null;
              wrapped = null;
              binOp = _a: _b: null;
              type = null;
            };
          }).name;
        expected = "plain";
      };
      # ★ AND THE SECOND CONTROL SEPARATES "was not read" FROM "was not read YET". A payload stated in
      # a spelling this boundary DOES read is consumed into `carries` and the functor refusal stays
      # silent — what fires instead is the carried-role requirement above, a DIFFERENT refusal with a
      # different message, which is only reachable because the payload crossed. Asserting that message
      # here is what proves the two refusals are not one loud predicate wearing two names.
      test-control-a-payload-the-boundary-reads-reaches-the-carried-role-refusal-instead = {
        expr = gm.mkOptionType {
          name = "boxOf";
          functor = {
            name = "boxOf";
            payload.elemType = t.str;
            binOp = _a: _b: null;
          };
          getSubOptions = _p: { };
          getSubModules = null;
          substSubModules = _m: null;
        };
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the structural type `boxOf' carries a parameter but does not supply `recarry'; a type that carries something answers for it rather than inheriting a leaf's answers$";
        };
      };
      # ★ THE THIRD CONTROL IS ALREADY ABOVE AND IS NOT REPEATED HERE:
      # `test-control-a-record-answering-one-protocol-field-imports` is a descriptor with NO functor
      # at all, in this same run, and it imports. Together the three say the refusal's domain is
      # exactly "stated a parameter, and lost it".

      # ── the PUBLISH path, which is a different site from `mkOptionType` ──────────────────────────
      # ★★★ THE REFUSAL HAS TO SURVIVE THE NAMESPACE ASSEMBLY, and it did not. `lib/default.nix`
      # computed the import environment's refusal for every entry of the injected leaf vocabulary and
      # then DISCARDED it, publishing the raw record into `lib.types` — where a mounting consumer dies
      # inside the foreign engine on a missing attribute, uncatchably and naming nothing. Measured at
      # the pre-boundary tree the same roster THREW, so it was a regression rather than a standing gap:
      # a computed refusal thrown away is worse than one never computed.
      #
      # THE PATH IS REACHED ONLY THROUGH A SUPPLIED VOCABULARY. The shipped roster does not trip the
      # rule — measured, empty — so a cell over `genMerge` could not exercise this at any strength;
      # `genMergeWith` hands the assembly a roster it did not choose, which is the input class
      # `lib/default.nix` names as supported ("in compat mode a foreign one") and the one the import
      # environment exists to be total over. The two cells here are DIFFERENT from the `mkOptionType`
      # cells above: same rule, same message, a site that had its own way of losing it.
      test-publishing-a-protocol-incomplete-leaf-is-refused-by-name = {
        expr =
          (genMergeWith (
            genTypes
            // {
              rogueOf = {
                name = "rogueOf";
                elemType = genTypes.str;
              };
            }
          )).types.rogueOf;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: the structural type `rogueOf' carries an element type but does not supply `getSubOptions', `getSubModules', `substSubModules'; a structural type may not inherit a leaf's protocol answer$";
        };
      };
      # LIVE CONTROL, same roster shape, same run: the un-offending twin answers all three and
      # publishes PROTOCOL-COMPLETE, and an ordinary shipped leaf beside it still does too. Without
      # both halves the cell above is equally consistent with a namespace that refuses everything, or
      # with one poisoned wholesale by a single bad entry — and per-name laziness is exactly what makes
      # the refusal usable rather than fatal to the whole vocabulary.
      test-control-the-un-offending-twin-publishes-protocol-complete = {
        expr =
          let
            published =
              (genMergeWith (
                genTypes
                // {
                  politeOf = {
                    name = "politeOf";
                    elemType = genTypes.str;
                    getSubOptions = _p: { };
                    getSubModules = null;
                    substSubModules = _m: null;
                  };
                }
              )).types;
            protocolFields = [
              "_type"
              "name"
              "description"
              "descriptionClass"
              "deprecationMessage"
              "check"
              "merge"
              "emptyValue"
              "getSubOptions"
              "getSubModules"
              "substSubModules"
              "typeMerge"
              "nestedTypes"
              "functor"
            ];
            missing = ty: builtins.filter (f: !(ty ? ${f})) protocolFields;
          in
          {
            twinMissing = missing published.politeOf;
            shippedLeafMissing = missing published.str;
          };
        expected = {
          twinMissing = [ ];
          shippedLeafMissing = [ ];
        };
      };
    };

    # The tree-as-a-type is a NESTING SEAM, not an `optionType`, and it now says so instead of
    # letting a foreign module system walk into a missing attribute. Before the mark, a real
    # `lib.evalModules` mounting it died INSIDE nixpkgs on `attribute 'deprecationMessage' missing`
    # — an interpreter error, and one `builtins.tryEval` could not catch, so there was nothing for
    # any in-language cell to observe. These cells are the whole of what replaces it. The
    # disposition (why completing the protocol is the wrong repair) is argued at the seam in
    # lib/modules.nix; what is assertable is that the read now returns a NAMED refusal.
    #
    # ★ THE PATTERNS DIFFER IN ONE PLACE ON PURPOSE. The direct read below names the field it
    # reached for and is pinned exactly. The MOUNT cannot be: which protocol field a foreign engine
    # forces first is that engine's evaluation order, not this library's behaviour, so pinning it
    # here would pin nixpkgs' internals and go red on a bump that changed nothing about the refusal.
    # That one field name is the only part left open; every other byte of the message is anchored.
    flake.testsError.tree-type = {
      # THE BOUNDARY CELL: a real nixpkgs `lib.evalModules` mounting a tree-type is refused BY NAME,
      # by gen-merge, before the consumer can trip over what the tree does not implement.
      test-foreign-mount-refused-by-name = {
        expr =
          let
            tree = gm.evalModuleTree {
              modules = [
                {
                  options.a = gm.mkOption {
                    type = t.str;
                    default = "x";
                  };
                }
              ];
            };
          in
          builtins.deepSeq
            (nixpkgsLib.evalModules {
              modules = [
                {
                  options.x = nixpkgsLib.mkOption { type = tree.type; };
                  config.x = { };
                }
              ];
            }).config.x
            null;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: `moduleTree' is not an option type and does not answer `[a-zA-Z]+'; it is this engine's own nesting seam, and mounting it in a foreign module system is a crossing this library does not open \\(ADR-0014: the boundary is the eval; ADR-0023: what crosses is plain data\\)$";
        };
      };
      # The refusal NAMES THE FIELD the caller reached for. An author told only "this is not a type"
      # still has to work out which read they made; the per-field message tells them, and it is what
      # makes the refusal usable from any consumer rather than only from a mount.
      test-protocol-read-names-the-field = {
        expr =
          (gm.evalModuleTree {
            modules = [ { options.a = gm.mkOption { type = t.str; }; } ];
          }).type.getSubOptions
            [ ];
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: `moduleTree' is not an option type and does not answer `getSubOptions'; it is this engine's own nesting seam, and mounting it in a foreign module system is a crossing this library does not open \\(ADR-0014: the boundary is the eval; ADR-0023: what crosses is plain data\\)$";
        };
      };
      # LIVE CONTROLS, same run, and BOTH are needed — the cells above are equally consistent with a
      # change that broke ALL mounting, and with one that broke the tree's own nesting.
      #
      # (1) A protocol-COMPLETED gen-merge type still mounts in a real `lib.evalModules` and its
      # value comes back, so the refusal above is the tree-type's and not the boundary's.
      test-completed-leaf-still-mounts-control = {
        expr =
          (nixpkgsLib.evalModules {
            modules = [
              {
                options.x = nixpkgsLib.mkOption { type = t.str; };
                config.x = "ok";
              }
            ];
          }).config.x;
        expected = "ok";
      };
      # (2) The seam itself still merges: a parent tree nests a child through the child's `.type`.
      # Nothing was deleted to make the mark, and this is the row that says so.
      test-tree-still-nests-in-gen-merge-control = {
        expr =
          let
            child = gm.evalModuleTree {
              modules = [
                {
                  options.a = gm.mkOption {
                    type = t.str;
                    default = "x";
                  };
                }
              ];
            };
          in
          cfg {
            modules = [
              { options.inner = gm.mkOption { type = child.type; }; }
              {
                config.inner = {
                  a = "set";
                };
              }
            ];
          };
        expected = {
          inner = {
            a = "set";
          };
        };
      };
    };

    # The shape-directed default-merge law's terminal arm. ci/tests/parity-surface.nix asserts THAT
    # it refuses and that the refusal is catchable; only this output can assert WHAT IT SAYS, and a
    # law whose whole contract is "a value or a NAMED refusal" (ADR-0025 §1) owes the name.
    # ★ Both patterns are anchored `^…$` — nix-unit SEARCHES `expectedError.msg`, so an unanchored
    # one pins a substring and would keep passing if the message grew a wrong clause on either side.
    # Neither message carries an ERE metacharacter, so the anchors carry the whole of the exactness.
    flake.testsError.default-merge-law = {
      # DIFFERING INTS are one of exactly two inputs that reach this arm — differing bools are OR'd
      # and differing strings are concatenated, so "scalars refuse" would be the wrong reading and
      # this cell is half of what fences it.
      test-differing-ints-refuse-by-name = {
        expr =
          gm.mergeDefaultOption
            [ "svc" "port" ]
            [
              {
                file = "<a>";
                value = 1;
              }
              {
                file = "<b>";
                value = 2;
              }
            ];
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: cannot merge definitions of option `svc\\.port'$";
        };
      };
      # A TYPE-HETEROGENEOUS definition list is the other one, and it reaches the same refusal by a
      # different route — no shape predicate holds of the list at all.
      test-heterogeneous-defs-refuse-by-name = {
        expr =
          gm.mergeDefaultOption
            [ "svc" "port" ]
            [
              {
                file = "<a>";
                value = 1;
              }
              {
                file = "<b>";
                value = "two";
              }
            ];
        expectedError = {
          type = "ThrownError";
          msg = "^gen-merge: cannot merge definitions of option `svc\\.port'$";
        };
      };
      # LIVE CONTROL, same run: the same law on the same option path with definitions that DO
      # combine. Without it both cells above are consistent with a law that refuses everything —
      # and the whole point of the ruled arm is that most shapes do not refuse.
      test-control-the-same-law-combines-rather-than-refusing = {
        expr =
          gm.mergeDefaultOption
            [ "svc" "port" ]
            [
              {
                file = "<a>";
                value = [ 1 ];
              }
              {
                file = "<b>";
                value = [ 2 ];
              }
            ];
        expected = [
          1
          2
        ];
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
