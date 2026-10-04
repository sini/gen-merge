# THE DOOR CHECKS (den-hoag-7gp66 P2 — `prelude.door`, R7 argument structure / R5 field closure) —
# every published step of gen-merge that takes a RECORD catches its own violations, at its own
# application, catchably.
#
# After P2 a door step is one of two kinds (spec §p2.3.1):
#   · an OPTIONS step — one closed set, first in the call: `evalModuleTree { specialArgs?; check?;
#     prefix?; coreShortCircuit?; warmFrom?; editedModules?; } modules`, `declaredOptions
#     { specialArgs?; prefix?; } modules` and `deriveType { key?; fields?; mint?; name?;
#     description?; } id base`;
#   · a RECORD by R7 (b) — open (R5), every field required, two operands of one sort:
#     `mergeTypes { deciding; partner; }`.
# `lint modules`, `mkCoreValue digest values` and `bandedLeaves scope result` are positional (rule
# 4): their arity is structural and they carry no row. No record step sits behind an options step
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
      apply = f: f [ declaresA ];
      observe = r: r.a.loc;
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

  # The record rows: the door, its required fields, and a `good` record that answers (each row's
  # live control, so a refusal below is the check firing, not a broken fixture).
  recordRows = {
    mergeTypes = {
      required = [
        "deciding"
        "partner"
      ];
      good = {
        deciding = t.str;
        partner = t.str;
      };
    };
  };

  # A field name no door declares, generated per evaluation from the door names themselves, so it is
  # never a name any contract below lists.
  stranger =
    "not-a-field-of-"
    + builtins.concatStringsSep "-" (builtins.attrNames optionsRows ++ builtins.attrNames recordRows);

  perOptions = f: builtins.mapAttrs f optionsRows;
  perRecord = f: builtins.mapAttrs f recordRows;
  allTrue = rows: builtins.all (x: x) (builtins.attrValues rows);

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
      expected = builtins.sort (a: b: a < b) (
        builtins.attrNames optionsRows ++ builtins.attrNames recordRows
      );
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
      ];
      expected = [
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

    # ── RECORDS BY R7 (b) ──
    test-control-each-good-record-answers = {
      expr = perRecord (n: r: answers (gm.${n} r.good).name);
      expected = perRecord (_: _: true);
    };
    # D2: EVERY required field, dropped alone, is refused at the application.
    test-each-missing-field-is-refused-at-the-application = {
      expr = perRecord (
        n: r:
        allTrue (prelude.genAttrs r.required (f: firesAtApplication (gm.${n} (removeAttrs r.good [ f ]))))
      );
      expected = perRecord (_: _: true);
    };
    test-a-non-set-record-is-refused-at-the-application = {
      expr = perRecord (n: _: firesAtApplication (gm.${n} 1));
      expected = perRecord (_: _: true);
    };
    # G2: R5's price — an extra field is admitted, and the answer is unchanged.
    test-an-extra-field-is-admitted = {
      expr = perRecord (n: r: (gm.${n} (r.good // { ${stranger} = 1; })).name == (gm.${n} r.good).name);
      expected = perRecord (_: _: true);
    };
    # The roles are read by name: the relation is asked of `deciding`. A gen type deciding over a
    # partner it refuses answers `null` in either place, and a merge answers in both.
    test-the-record-reads-its-operands-by-role = {
      expr = {
        same =
          (gm.mergeTypes {
            deciding = t.int;
            partner = t.int;
          }).name;
        refusedOneWay = gm.mergeTypes {
          deciding = t.int;
          partner = t.str;
        };
        refusedOtherWay = gm.mergeTypes {
          deciding = t.str;
          partner = t.int;
        };
      };
      expected = {
        same = t.int.name;
        refusedOneWay = null;
        refusedOtherWay = null;
      };
    };
    # D3.
    test-each-record-door-publishes-its-contract = {
      expr = perRecord (
        n: _: {
          inherit (gm.${n}.__contract) required optional open;
          args = prelude.functionArgs gm.${n};
        }
      );
      expected = perRecord (
        _: r: {
          inherit (r) required;
          optional = [ ];
          open = true;
          args = builtins.listToAttrs (map (f: prelude.nameValuePair f false) r.required);
        }
      );
    };
  };
}
