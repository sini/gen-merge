# THE DOOR CHECKS (den-hoag-7gp66 P2 — `prelude.door`, R7 argument structure / R5 field closure) —
# every published step of gen-merge that takes a RECORD catches its own violations, at its own
# application, catchably.
#
# After P2 a door step is one of two kinds (spec §p2.3.1):
#   · an OPTIONS step — one closed set, first in the call: `evalModuleTree { specialArgs?; check?;
#     prefix?; coreShortCircuit?; warmFrom?; editedModules?; } modules`, `declaredOptions
#     { specialArgs?; prefix?; } modules` and `deriveType { key?; fields?; mint?; name?;
#     description?; } id base`.
# `lint modules`, `mkCoreValue digest values`, `bandedLeaves scope result` and `mergeTypes deciding
# partner` are positional (rule 4; `mergeTypes`' order is the relation's own, pinned below): their arity is structural and they carry no row. No record step sits behind an options step
# here, so no door carries `optionsStep` (G10 has no row). `types.mkValidator` is gen-types' door,
# re-exported as the identical value: its row is gen-types'.
#
# WHICH refusal fired is a claim about the message and `tryEval` yields only `success`; the byte
# goldens naming each door (R6) live in `ci/tests-error.nix`'s `flake.testsError`.
{
  genMerge,
  genTypes,
  prelude,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  # `firesAtApplication` forces the door's application to WHNF only — never `deepSeq` — so a check
  # that ran only behind a later field read reads `false` (spec §p2.5, premise 5).
  firesAtApplication = e: !(builtins.tryEval (builtins.seq e null)).success;
  answers = e: (builtins.tryEval (builtins.deepSeq e null)).success;

  declaresA = {
    options.a = gm.mkOption { default = 1; };
  };

  # The options rows: the door, its options, `apply` supplying the operands after the options step,
  # and one non-default option whose value the door's own result carries (G3), read by `observe`.
  optionsRows = {
    evalModuleTree = {
      optional = [
        "specialArgs"
        "check"
        "prefix"
        "coreShortCircuit"
        "warmFrom"
        "editedModules"
      ];
      apply = f: f [ declaresA ];
      observe = r: r.options.a.loc;
      opt.prefix = [ "under" ];
    };
    declaredOptions = {
      optional = [
        "specialArgs"
        "prefix"
      ];
      # The declaration reads the `prefix` the stratum binds, so the option reaches the fold itself,
      # not only the stamp on the declared record.
      apply = f: f [ ({ prefix, ... }: { options.a = gm.mkOption { default = prefix; }; }) ];
      observe = r: r.a.default;
      opt.prefix = [ "under" ];
    };
    deriveType = {
      optional = [
        "key"
        "fields"
        "mint"
        "name"
        "description"
      ];
      apply = f: f "tagged" t.str;
      observe = r: r.description;
      opt.description = "a tagged string";
    };
  };

  # A field name no door declares, generated per evaluation from the door names themselves, so it is
  # never a name any contract below lists.
  stranger = "not-a-field-of-" + builtins.concatStringsSep "-" (builtins.attrNames optionsRows);

  perOptions = f: builtins.mapAttrs f optionsRows;

  # Every published value that is a door (a functor carrying `__contract`), at the top level and in
  # `types`, less gen-types' own doors the vocabulary re-exports.
  doorsOf =
    lib:
    builtins.attrNames (
      prelude.filterAttrs (_: v: builtins.isAttrs v && v ? __functor && v ? __contract) lib
    );
  surfaceDoors = doorsOf gm;
  ownTypesDoors = builtins.filter (n: !(genTypes ? ${n})) (doorsOf t);
in
{
  flake.tests.door-checks = {
    # ── LIVE CONTROLS, first: the predicates are not dead ──
    test-control-firesAtApplication-is-true-for-an-ordinary-throw = {
      expr = firesAtApplication (throw "control probe, not this suite's subject");
      expected = true;
    };
    test-control-firesAtApplication-is-false-for-a-throw-behind-an-unread-field = {
      expr = firesAtApplication { culprit = throw "control probe, not this suite's subject"; };
      expected = false;
    };

    # ── THE TABLE IS THE SURFACE ──
    # Every published door has a row and every row is a published door, so a door added without a
    # row — or a row whose door reverted to a lambda — reds here.
    test-the-door-table-equals-the-surface-doors = {
      expr = surfaceDoors;
      expected = builtins.sort (a: b: a < b) (builtins.attrNames optionsRows);
    };
    # `types` holds gen-merge's own `deriveType` (the same value) and gen-types' doors, re-exported.
    test-the-vocabulary-holds-no-other-own-door = {
      expr = ownTypesDoors;
      expected = [ "deriveType" ];
    };
    test-the-vocabulary-re-exports-gen-types-mkValidator-unchanged = {
      expr = t.mkValidator.__contract == genTypes.mkValidator.__contract;
      expected = true;
    };
    test-the-positional-entries-are-plain-lambdas = {
      expr = map (n: builtins.isFunction gm.${n}) [
        "lint"
        "mkCoreValue"
        "bandedLeaves"
        "mergeTypes"
      ];
      expected = [
        true
        true
        true
        true
      ];
    };
    test-control-the-positional-entries-answer = {
      expr = {
        lint = gm.lint [ { } ];
        core = gm.mkCoreValue "d" { };
        banded = gm.bandedLeaves "s" (gm.evalModuleTree { } [ ]);
      };
      expected = {
        lint = [ ];
        core = {
          __coreValue = true;
          digest = "d";
          values = { };
        };
        banded = { };
      };
    };

    # ── OPTIONS STEPS ──
    # G1/G4: an unknown option is refused at `f opts`'s WHNF, before any operand.
    test-an-unknown-option-is-refused-at-the-options-application = {
      expr = perOptions (n: _: firesAtApplication (gm.${n} { ${stranger} = 1; }));
      expected = perOptions (_: _: true);
    };
    test-a-non-set-options-argument-is-refused-at-the-application = {
      expr = perOptions (n: _: firesAtApplication (gm.${n} 1));
      expected = perOptions (_: _: true);
    };
    # The old one-record shape is refused by name at its first application: `modules` is not an
    # option of either module-tree door.
    test-the-old-one-record-shape-is-refused-at-the-application = {
      expr = map (n: firesAtApplication (gm.${n} { modules = [ ]; })) [
        "evalModuleTree"
        "declaredOptions"
      ];
      expected = [
        true
        true
      ];
    };
    # The live control: `{ }` forms the door and the operands answer.
    test-control-the-empty-options-answer = {
      expr = perOptions (n: r: answers (r.observe (r.apply (gm.${n} { }))));
      expected = perOptions (_: _: true);
    };
    # Every option of each door is admitted, together.
    test-every-option-is-admitted = {
      expr = perOptions (n: r: !firesAtApplication (gm.${n} (prelude.genAttrs r.optional (_: null))));
      expected = perOptions (_: _: true);
    };
    # D3: the published contract and the functor-aware reader agree with the row.
    test-each-options-door-publishes-its-contract = {
      expr = perOptions (
        n: _: {
          inherit (gm.${n}.__contract) optional open required;
          args = prelude.functionArgs gm.${n};
        }
      );
      expected = perOptions (
        _: r: {
          inherit (r) optional;
          open = false;
          required = [ ];
          args = builtins.listToAttrs (map (f: prelude.nameValuePair f true) r.optional);
        }
      );
    };
    # G3: a non-default option reaches the result (`differ`, against `{ }`), and the partially
    # applied door agrees with the full call (`agree`), each read from its own evaluation.
    test-a-non-default-option-reaches-the-result = {
      expr = perOptions (
        n: r:
        let
          f1 = gm.${n} r.opt;
        in
        {
          agree = r.observe (r.apply f1) == r.observe (r.apply (gm.${n} r.opt));
          differ = r.observe (r.apply f1) != r.observe (r.apply (gm.${n} { }));
        }
      );
      expected = perOptions (
        _: _: {
          agree = true;
          differ = true;
        }
      );
    };
    # Composition: `evalModuleTree opts` is a value mapped over module lists.
    test-a-partially-applied-door-maps-over-module-lists = {
      expr =
        let
          evalWith = gm.evalModuleTree { specialArgs.seen = "mapped"; };
        in
        map (ms: (evalWith ms).config.a) [
          [ ({ seen, ... }: declaresA // { config.a = seen; }) ]
          [ declaresA ]
        ];
      expected = [
        "mapped"
        1
      ];
    };
    # The type vocabulary publishes `deriveType` once, under both paths.
    test-deriveType-is-one-door-at-both-paths = {
      expr = gm.deriveType.__contract == t.deriveType.__contract;
      expected = true;
    };

    # ── mergeTypes: TWO POSITIONAL OPERANDS, IN ORDER ──
    # The relation is asked of the FIRST operand. `greedy` is a gen type whose own relation merges with
    # anything, so it answers where it comes first; second, `int`'s relation decides, and refuses. A
    # door that swapped or ignored the order reads the same answer both ways. The `int`/`int` pair is
    # the live control that the door answers at all.
    test-swapping-the-operands-changes-the-answer = {
      expr =
        let
          greedy = t.defineType (
            t.str
            // {
              name = "greedy";
              typeMergeRel = _: { merged = t.str; };
            }
          );
        in
        {
          control = (gm.mergeTypes t.int t.int).name;
          greedyFirst = (gm.mergeTypes greedy t.int).name;
          intFirst = gm.mergeTypes t.int greedy;
        };
      expected = {
        control = t.int.name;
        greedyFirst = t.str.name;
        intFirst = null;
      };
    };
  };
}
