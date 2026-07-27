# nixpkgs optionType PROTOCOL completion — gen-merge types mount inside a REAL nixpkgs `lib.evalModules`.
#
# The FORWARD boundary (compat-nixpkgs-types.nix pins the REVERSE: nixpkgs types run INSIDE gen-merge).
# This is the ship-gate seam: gen-schema injects gen-merge-typed options — mkIdentityModule's `id_hash`
# (`types.str`), mkStrictModule's freeform (`attrsOf anything`) — into an instance submodule that a
# consumer (nix-config's `mkInstanceRegistry` in flake-parts) evaluates with NIXPKGS. Before the protocol
# completion those types carried only the merge half, so nixpkgs' module system threw
# `error: attribute 'deprecationMessage' missing` reading the type. gen-merge now stamps the full
# nixpkgs optionType shape (purely, no nixpkgs import) so the SAME type value serves both engines.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gmT = genMerge.types;
  prefixed = k: builtins.substring 0 1 k == "_";

  # Mount a gen-merge-typed option in a REAL nixpkgs `lib.evalModules` (the exact corpus path: a nixpkgs
  # option whose `type` is a gen-merge type), read back the resolved config value.
  mount =
    type: def:
    (nixpkgsLib.evalModules {
      modules = [
        { options.x = nixpkgsLib.mkOption { inherit type; }; }
        { config.x = def; }
      ];
    }).config.x;

  # The 14-field nixpkgs `mkOptionType` protocol (lib/types.nix at the corpus pin).
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
  hasAll = t: builtins.all (f: t ? ${f}) protocolFields;

  strMod = {
    options.y = nixpkgsLib.mkOption { type = gmT.str; };
  };

  # Render a type as its NAME plus the names of the types it is parameterised BY, recursively. Pinning
  # this string pins the merged type's CONTENTS: a `typeMerge` that returns the right container over the
  # wrong element reads differently from one that returns the right container over the right element,
  # where a bare `!= null` or a name-only check would call both green.
  describe =
    t:
    let
      nested = t.nestedTypes or { };
    in
    if t == null then
      "<not-mergeable>"
    else if nested ? elemType then
      "${t.name} of ${describe nested.elemType}"
    else if nested ? left then
      "${t.name} of ${describe nested.left} | ${describe nested.right}"
    else
      t.name;

  # Declare ONE option TWICE, with a type each — the exact site nixpkgs `mergeOptionDecls` reaches for
  # `type.typeMerge`. Callers pass element types the definition `"s"` satisfies on BOTH sides, so an
  # ACCEPTED result can only mean the two declarations were reconciled, never that the surviving
  # declaration's type happened to reject the value.
  declTwice =
    t1: t2:
    (nixpkgsLib.evalModules {
      modules = [
        { options.x = nixpkgsLib.mkOption { type = t1; }; }
        { options.x = nixpkgsLib.mkOption { type = t2; }; }
        { config.x.k = "s"; }
      ];
    }).config.x;
  resolves = e: (builtins.tryEval (builtins.deepSeq e e)).success;

  subA = gmT.submodule { options.a = genMerge.mkOption { type = gmT.str; }; };
  subB = gmT.submodule { options.b = genMerge.mkOption { type = gmT.str; }; };
in
{
  flake.tests.nixpkgs-protocol = {
    # every completed type carries the full protocol — leaf (gen-types-injected), structural values, and
    # the results of the structural constructors.
    test-protocol-complete = {
      expr = {
        str = hasAll gmT.str;
        submodule = hasAll (gmT.submodule { });
        listOf = hasAll (gmT.listOf gmT.str);
        attrsOf = hasAll (gmT.attrsOf gmT.str);
        raw = hasAll gmT.raw;
        anything = hasAll gmT.anything;
      };
      expected = {
        str = true;
        submodule = true;
        listOf = true;
        attrsOf = true;
        raw = true;
        anything = true;
      };
    };

    # THE DEFINITIVE WITNESS — a gen-merge leaf mounts in nixpkgs `evalModules` (the corpus's
    # deprecationMessage crash is gone) and resolves its value.
    test-leaf-mounts-in-nixpkgs = {
      expr = mount gmT.str "hi";
      expected = "hi";
    };
    # structural types mount + merge faithfully through nixpkgs (attrsOf per-key, listOf concat) — and a
    # SUBMODULE mount exercises `getSubModules`/`substSubModules` (modules.nix:1477) end to end, with a
    # gen-merge `str` nested inside it.
    test-attrsOf-mounts = {
      expr = mount (gmT.attrsOf gmT.str) { a = "x"; };
      expected = {
        a = "x";
      };
    };
    test-listOf-mounts = {
      expr = mount (gmT.listOf gmT.str) [
        "a"
        "b"
      ];
      expected = [
        "a"
        "b"
      ];
    };
    test-submodule-mounts = {
      expr = mount (gmT.submodule strMod) { y = "v"; };
      expected = {
        y = "v";
      };
    };

    # `getSubOptions` — the INTROSPECTION half of the protocol, previously stubbed `_prefix: { }` on every
    # type. A consumer that reads a registry's DECLARED instance surface off the option type (rather than
    # off an instance VALUE) got an empty set and could conclude nothing about it. Now a submodule reports
    # what it declares, and the containers descend to their element type.
    #
    # The key sets are pinned EXACTLY, not merely asserted non-empty: `builtins.attrNames { }` is `[ ]`,
    # so a membership-only or all-of check would pass vacuously against the very regression this guards.
    test-getSubOptions-submodule = {
      expr = builtins.attrNames ((gmT.submodule strMod).getSubOptions [ ]);
      expected = [ "y" ];
    };
    # attrsOf/listOf descend to the element type under the nixpkgs placeholder segments, so an
    # `attrsOf (submodule …)` registry exposes its per-instance option surface.
    test-getSubOptions-containers-descend = {
      expr = {
        attrs = builtins.attrNames ((gmT.attrsOf (gmT.submodule strMod)).getSubOptions [ ]);
        list = builtins.attrNames ((gmT.listOf (gmT.submodule strMod)).getSubOptions [ ]);
      };
      expected = {
        attrs = [ "y" ];
        list = [ "y" ];
      };
    };
    # The FAIL-FOR-ITS-OWN-REASON control: a container over a LEAF element still reports no sub-options,
    # so a green result above is the submodule descent working, not the walk returning something constant.
    test-getSubOptions-leaf-stays-empty = {
      expr = {
        leaf = (gmT.attrsOf gmT.str).getSubOptions [ ];
        str = gmT.str.getSubOptions [ ];
        nullOrLeaf = (gmT.nullOr gmT.str).getSubOptions [ ];
        # `deferredModule` reports nothing because it HAS nothing: nixpkgs' sub-options for this type are
        # its `staticModules`, and gen-merge ships no `deferredModuleWith`/`staticModules` parameter, so
        # the static module set is empty by construction. nixpkgs' plain `deferredModule` likewise
        # declares only its synthesized `_module`. This is the correct answer, not the `_prefix: { }`
        # stub — recorded here so it is not "fixed" into something wrong later.
        deferredModule = gmT.deferredModule.getSubOptions [ ];
        # a PARAMETRIC gen-types leaf is never protocol-completed and carries no `getSubOptions` of its
        # own; wrapping one must report "declares nothing", not abort on a missing attribute.
        nullOrParametricLeaf = (gmT.nullOr (gmT.enum "e" [ "a" ])).getSubOptions [ ];
      };
      expected = {
        leaf = { };
        str = { };
        nullOrLeaf = { };
        deferredModule = { };
        nullOrParametricLeaf = { };
      };
    };

    # The two halves of the protocol must agree about what a `deferredModule` IS. `check` decides which
    # DEFINITIONS are admissible (a path, a function, a `__functor` attrset, a plain attrset);
    # `getSubOptions` reports what the TYPE declares with no value in hand. They agree by saying
    # different things about different questions: accepting a module-shaped VALUE does not make the type
    # DECLARE that module's options, because a definition is not a static module. gen-merge ships no
    # `deferredModuleWith`/`staticModules`, so the declared set is empty however many modules are later
    # defined into it.
    #
    # The control is the load-bearing row: a `submodule` over the SAME module DOES declare `y`, so the
    # `{ }` above is `deferredModule`'s own answer rather than the walk returning something constant.
    # Without it, an accidental `getSubOptions = _: { }` on every type would satisfy this test.
    test-deferredModule-check-and-getSubOptions-agree = {
      expr =
        let
          m = {
            options.y = genMerge.mkOption { type = gmT.str; };
          };
        in
        {
          checkAcceptsModule = gmT.deferredModule.check m;
          checkRejectsNonModule = gmT.deferredModule.check 3;
          declaresNothing = gmT.deferredModule.getSubOptions [ ];
          # the accepted module still rides through to the value, unexamined and unforced
          mergedImportsCount = builtins.length (mount gmT.deferredModule m).imports;
          submoduleOverSameModuleDeclares = builtins.attrNames ((gmT.submodule m).getSubOptions [ ]);
        };
      expected = {
        checkAcceptsModule = true;
        checkRejectsNonModule = false;
        declaresNothing = { };
        mergedImportsCount = 1;
        submoduleOverSameModuleDeclares = [ "y" ];
      };
    };

    # `nullOr` was the last STRUCTURAL type left on the `_prefix: { }` default, so a `nullOr`-wrapped
    # registry reported "declares nothing" — indistinguishable from one that genuinely declares nothing,
    # the same fail-closed shape the containers had. It passes straight through to its element.
    #
    # Each read is guarded (`or "<no y>"`) rather than selected bare: a regression that stops descending
    # yields a readable diff instead of `attribute 'y' missing`, which would take the whole asserter down
    # instead of failing this one test.
    test-getSubOptions-nullOr-descends = {
      expr = {
        submodule = builtins.attrNames ((gmT.nullOr (gmT.submodule strMod)).getSubOptions [ ]);
        throughContainer = builtins.attrNames (
          (gmT.nullOr (gmT.attrsOf (gmT.submodule strMod))).getSubOptions [ ]
        );
        nested = builtins.attrNames ((gmT.nullOr (gmT.nullOr (gmT.submodule strMod))).getSubOptions [ ]);
      };
      expected = {
        submodule = [ "y" ];
        throughContainer = [ "y" ];
        nested = [ "y" ];
      };
    };

    # WHICH prefix segment each constructor contributes, pinned by CONTENTS. A nullable introduces no
    # path level, so it must pass the caller's prefix through UNCHANGED — the containers do not. gen-merge
    # option records carry no `loc`, so the observable is the submodule's `name` special-arg, which
    # `getSubOptions` binds from the last prefix segment: `attrsOf` contributes `<name>`, `listOf`
    # contributes `*`, and `submodule`/`nullOr` contribute nothing and so both report the caller's own
    # last segment. This discriminates all four from each other — a `nullOr` that wrongly added a segment
    # reads differently from one that adds none, where a key-set check would call both green.
    test-getSubOptions-prefix-segments = {
      expr =
        let
          nameMod =
            { name, ... }:
            {
              options.y = genMerge.mkOption {
                type = gmT.str;
                default = name;
              };
            };
          seg = t: ((t.getSubOptions [ "root" ]).y.default or "<no y>");
        in
        {
          submodule = seg (gmT.submodule nameMod);
          nullOr = seg (gmT.nullOr (gmT.submodule nameMod));
          attrsOf = seg (gmT.attrsOf (gmT.submodule nameMod));
          listOf = seg (gmT.listOf (gmT.submodule nameMod));
          nullOrAtRoot = ((gmT.nullOr (gmT.submodule nameMod)).getSubOptions [ ]).y.default or "<no y>";
        };
      expected = {
        submodule = "root";
        nullOr = "root";
        attrsOf = "<name>";
        listOf = "*";
        nullOrAtRoot = "";
      };
    };

    # `_type` marks a nixpkgs option type; `deprecationMessage` is present-and-null (the field that threw).
    test-type-tag = {
      expr = {
        t = gmT.str._type;
        dep = gmT.str.deprecationMessage;
      };
      expected = {
        t = "option-type";
        dep = null;
      };
    };
    # SEMANTIC (ecosystem-owes-it, though the corpus declares these once): a leaf `typeMerge` self-merges
    # (same functor name → the type), and returns null across names ("not mergeable").
    test-typeMerge-leaf = {
      expr = {
        self = (gmT.str.typeMerge gmT.str.functor) != null;
        cross = gmT.str.typeMerge gmT.anything.functor;
      };
      expected = {
        self = true;
        cross = null;
      };
    };

    # gen-types exports NULLARY leaves as attrsets and PARAMETRIC ones as constructors. Only the first
    # shape was protocol-completed, so `enum`/`struct`/`union`/`tuple`/`refined`/`optionalAttr` returned a
    # bare gen-types record — no `deprecationMessage`, no `functor`, no `getSubOptions`. Mounting one in a
    # nixpkgs `evalModules` reproduced the exact crash the protocol completion exists to prevent.
    #
    # Both halves are asserted: the completed set carries the full protocol AND the nullary leaves are
    # unchanged, so a regression that completes nothing and one that over-completes both redden.
    test-parametric-leaf-protocol-complete = {
      expr = {
        enum = builtins.filter (f: !((gmT.enum "e" [ "a" ]) ? ${f})) protocolFields;
        struct = builtins.filter (f: !((gmT.struct "s" { a = gmT.str; }) ? ${f})) protocolFields;
        refined = builtins.filter (f: !((gmT.refined gmT.str [ ]) ? ${f})) protocolFields;
        optionalAttr = builtins.filter (f: !((gmT.optionalAttr gmT.str) ? ${f})) protocolFields;
        nullaryStillComplete = builtins.filter (f: !(gmT.str ? ${f})) protocolFields;
      };
      expected = {
        enum = [ ];
        struct = [ ];
        refined = [ ];
        optionalAttr = [ ];
        nullaryStillComplete = [ ];
      };
    };

    # THE WITNESS: a parametric leaf mounts in a REAL nixpkgs `lib.evalModules` and still CHECKS. The
    # rejecting row is the one that proves the mount did not simply stop validating on the way through.
    test-parametric-leaf-mounts-in-nixpkgs = {
      expr = {
        accepts = mount (gmT.enum "e" [
          "a"
          "b"
        ]) "a";
        rejectsResolves = resolves (
          mount (gmT.enum "e" [
            "a"
            "b"
          ]) "zzz"
        );
        structAccepts = mount (gmT.struct "s" { a = gmT.str; }) { a = "v"; };
      };
      expected = {
        accepts = "a";
        rejectsResolves = false;
        structAccepts = {
          a = "v";
        };
      };
    };

    # A parametric leaf's `typeMerge` REFUSES, deliberately. Its parameters are not introspectable, and
    # neither substitute works: gen-types' `__id` is NAME-only, so `enum "e" [ "a" ]` and
    # `enum "e" [ "b" ]` share one; and value equality is pointer-based over the closures, so two
    # IDENTICAL constructions compare unequal. Left on the nullary default, `pureTypeMerge` would answer
    # "mergeable" for any same-named partner and silently discard one declaration's allowed values.
    #
    # The nullary rows are the control and they must NOT refuse: a type with no parameters has nothing to
    # compare, so its self-merge is correct. A completion that stamped the refusal onto every leaf would
    # redden here.
    test-parametric-leaf-typeMerge-refuses = {
      expr = {
        enumSelf = (gmT.enum "e" [ "a" ]).typeMerge (gmT.enum "e" [ "a" ]).functor;
        enumDiffering = (gmT.enum "e" [ "a" ]).typeMerge (gmT.enum "e" [ "b" ]).functor;
        structSelf = (gmT.struct "s" { a = gmT.str; }).typeMerge (gmT.struct "s" { a = gmT.str; }).functor;
        nullaryLeafStillSelfMerges = (gmT.str.typeMerge gmT.str.functor) != null;
        nullaryLeafCrossName = gmT.str.typeMerge gmT.int.functor;
      };
      expected = {
        enumSelf = null;
        enumDiffering = null;
        structSelf = null;
        nullaryLeafStillSelfMerges = true;
        nullaryLeafCrossName = null;
      };
    };

    # gen-types HELPERS must pass through uncompleted. `mkValidator name pred message` returns
    # `{ message; name; pred; }` — it carries `name` but NOT `verify`, so a completion keyed on the
    # top-level rule (`? verify || ? name`) would stamp `_type = "option-type"` onto a validator and make
    # `isOptionType` lie about it. The parametric arm keys on `verify` alone for exactly this reason.
    test-parametric-completion-skips-helpers = {
      expr = {
        mkValidatorKeys = builtins.attrNames (gmT.mkValidator "n" (_: true) "msg");
        mkValidatorIsNotAType = (gmT.mkValidator "n" (_: true) "msg") ? _type;
        formatErrorsType = builtins.typeOf (gmT.formatErrors [ ]);
        refinementsKeys = builtins.attrNames gmT.refinements;
      };
      expected = {
        mkValidatorKeys = [
          "message"
          "name"
          "pred"
        ];
        mkValidatorIsNotAType = false;
        formatErrorsType = "string";
        refinementsKeys = [
          "nonEmpty"
          "positive"
          "tcpPort"
        ];
      };
    };

    # `emptyValue` — the field that decides whether "no surviving definition" is a legitimate empty
    # container or an error. It was `{ }` (no `value` attr) on every type, which reads as "this type
    # declares no empty value" and made every undefined option an error. Pinned as the full table
    # against nixpkgs rather than for the four that changed: the types that must declare NONE are the
    # other half of the contract, and a regression that hands every type an `emptyValue.value` would
    # pass a four-row test.
    test-emptyValue-matches-nixpkgs = {
      expr =
        let
          e = t: if t.emptyValue ? value then t.emptyValue.value else "<declares none>";
          row = T: {
            attrsOf = e (T.attrsOf T.str);
            lazyAttrsOf = e (T.lazyAttrsOf T.str);
            listOf = e (T.listOf T.str);
            nullOr = e (T.nullOr T.str);
            submodule = e (T.submodule { });
            deferredModule = e T.deferredModule;
            either = e (T.either T.str T.int);
            raw = e T.raw;
            anything = e T.anything;
          };
        in
        {
          gen = row gmT;
          matchesNixpkgs = row gmT == row nixpkgsLib.types;
        };
      expected = {
        gen = {
          attrsOf = { };
          lazyAttrsOf = { };
          listOf = [ ];
          nullOr = null;
          submodule = { };
          deferredModule = "<declares none>";
          either = "<declares none>";
          raw = "<declares none>";
          anything = "<declares none>";
        };
        matchesNixpkgs = true;
      };
    };

    # `deferredModule.check` — a check that CANNOT FAIL is not a check. `completeType` defaults a type
    # carrying neither `verify` nor `check` to `_: true`, which is right for a type whose merge accepts
    # any value; `deferredModule`'s does not. Its merge wraps each def into an `imports` list, and the
    # engine's `callM` applies only a path, a function, a `__functor` attrset or a plain attrset — so a
    # wrong-shaped definition was accepted here and detonated later, at whoever imported it, carrying no
    # option path and no definition file.
    #
    # BOTH halves of the table are populated on purpose: a regression to `_: true` reddens the rejected
    # rows, an over-strict check reddens the accepted ones. No constant satisfies it.
    test-deferredModule-check-shapes = {
      expr = builtins.mapAttrs (_: gmT.deferredModule.check) {
        attrs = { };
        fn = _: { };
        functorAttrs = {
          __functor = _self: (_: { });
        };
        path = ./nixpkgs-protocol.nix;
        int = 3;
        str = "hi";
        list = [ { } ];
        isNull = null;
        bool = true;
        # DELIBERATE divergence from nixpkgs, pinned so it stays deliberate: nixpkgs reuses
        # `types.path.check`, which admits a STRING beginning with `/` as a module. `callM` dispatches on
        # `builtins.isPath`, so gen-merge would carry such a string through as a module VALUE — admitting
        # it here would re-create the silent acceptance this check exists to close.
        absolutePathString = "/abs/path.nix";
      };
      expected = {
        attrs = true;
        fn = true;
        functorAttrs = true;
        path = true;
        int = false;
        str = false;
        list = false;
        isNull = false;
        bool = false;
        absolutePathString = false;
      };
    };

    # END TO END: a wrong-shaped definition is REFUSED through nixpkgs' own located path
    # (`A definition for option 'x' is not of type 'deferredModule'. Definition values: - In '…': 3`)
    # instead of resolving to a structurally invalid module value. The well-formed def is pinned by
    # VALUE, and additionally shown byte-identical to nixpkgs', so neither row can go green by the
    # option failing — or succeeding — for an unrelated reason.
    test-deferredModule-rejects-in-nixpkgs = {
      expr = {
        wrongShapeResolves = resolves (mount gmT.deferredModule 3);
        nixpkgsWrongShapeResolves = resolves (mount nixpkgsLib.types.deferredModule 3);
        okResolves = resolves (mount gmT.deferredModule (_: { }));
        ok = mount gmT.deferredModule { imports = [ ]; };
        okMatchesNixpkgs =
          (mount gmT.deferredModule { imports = [ ]; })
          == (mount nixpkgsLib.types.deferredModule { imports = [ ]; });
      };
      expected = {
        wrongShapeResolves = false;
        nixpkgsWrongShapeResolves = false;
        okResolves = true;
        ok = {
          imports = [
            {
              _file = "<unknown-file>, via option x";
              imports = [ { imports = [ ]; } ];
            }
          ];
        };
        okMatchesNixpkgs = true;
      };
    };

    # `typeMerge` on a PARAMETERISED type must compare the PARAMETERS, not the container name alone. The
    # nullary default functor carries `payload = null`, which sends `pureTypeMerge` down its "no payload"
    # arm and answers the receiver's own type for ANY same-named partner — so an option declared in two
    # modules as `attrsOf` over DIFFERENT element types reported "mergeable", one declaration was dropped,
    # and nothing was raised. Each container now carries an `elemTypeFunctor`, so the two merge iff their
    # elements do, recursively.
    #
    # Every divergent case is paired with its own same-shape agreeing case: a regression that returned
    # `<not-mergeable>` for everything would redden the `*Same` half, and one that merged everything would
    # redden the `*Diff` half. The `attrsOfVsLazy` row is the pre-existing name discrimination, held.
    test-typeMerge-container-elements = {
      expr = {
        attrsOfSame = describe ((gmT.attrsOf gmT.str).typeMerge (gmT.attrsOf gmT.str).functor);
        attrsOfDiff = describe ((gmT.attrsOf gmT.str).typeMerge (gmT.attrsOf gmT.int).functor);
        lazyAttrsOfSame = describe ((gmT.lazyAttrsOf gmT.str).typeMerge (gmT.lazyAttrsOf gmT.str).functor);
        lazyAttrsOfDiff = describe ((gmT.lazyAttrsOf gmT.str).typeMerge (gmT.lazyAttrsOf gmT.int).functor);
        listOfSame = describe ((gmT.listOf gmT.str).typeMerge (gmT.listOf gmT.str).functor);
        listOfDiff = describe ((gmT.listOf gmT.str).typeMerge (gmT.listOf gmT.int).functor);
        nullOrSame = describe ((gmT.nullOr gmT.str).typeMerge (gmT.nullOr gmT.str).functor);
        nullOrDiff = describe ((gmT.nullOr gmT.str).typeMerge (gmT.nullOr gmT.int).functor);
        # `either`'s payload is the member PAIR, positional: swapping the arms is a different type.
        eitherSame = describe ((gmT.either gmT.str gmT.int).typeMerge (gmT.either gmT.str gmT.int).functor);
        eitherDiff = describe (
          (gmT.either gmT.str gmT.int).typeMerge (gmT.either gmT.bool gmT.path).functor
        );
        eitherSwapped = describe (
          (gmT.either gmT.str gmT.int).typeMerge (gmT.either gmT.int gmT.str).functor
        );
        # the element merge RECURSES — a container over a container compares the innermost type.
        nestedSame = describe (
          (gmT.attrsOf (gmT.listOf gmT.str)).typeMerge (gmT.attrsOf (gmT.listOf gmT.str)).functor
        );
        nestedDiff = describe (
          (gmT.attrsOf (gmT.listOf gmT.str)).typeMerge (gmT.attrsOf (gmT.listOf gmT.int)).functor
        );
        attrsOfVsLazy = describe ((gmT.attrsOf gmT.str).typeMerge (gmT.lazyAttrsOf gmT.str).functor);
      };
      expected = {
        attrsOfSame = "attrsOf of string";
        attrsOfDiff = "<not-mergeable>";
        lazyAttrsOfSame = "lazyAttrsOf of string";
        lazyAttrsOfDiff = "<not-mergeable>";
        listOfSame = "listOf of string";
        listOfDiff = "<not-mergeable>";
        nullOrSame = "nullOr of string";
        nullOrDiff = "<not-mergeable>";
        eitherSame = "either of string | int";
        eitherDiff = "<not-mergeable>";
        eitherSwapped = "<not-mergeable>";
        nestedSame = "attrsOf of listOf of string";
        nestedDiff = "<not-mergeable>";
        attrsOfVsLazy = "<not-mergeable>";
      };
    };

    # A submodule's parameter is its MODULE LIST, so nixpkgs `submoduleWith`'s functor concatenates the
    # two declarations' modules and the merged type declares the UNION of what they declare. Blind on the
    # nullary functor, the merged type declares only the receiver's half. The sub-option names are pinned
    # exactly — `builtins.attrNames { }` is `[ ]`, so a membership check would pass against the very
    # regression this guards.
    test-typeMerge-submodule-unions-declarations = {
      expr =
        let
          merged = subA.typeMerge subB.functor;
        in
        {
          name = merged.name;
          subOptions = builtins.attrNames (merged.getSubOptions [ ]);
          # control on the same instrument: each half alone declares only its own.
          left = builtins.attrNames (subA.getSubOptions [ ]);
          right = builtins.attrNames (subB.getSubOptions [ ]);
        };
      expected = {
        name = "submodule";
        subOptions = [
          "a"
          "b"
        ];
        left = [ "a" ];
        right = [ "b" ];
      };
    };

    # THE ARMING CONTROL for the group above: a NULLARY type has no parameters to compare, so the
    # payload-free functor is correct for it and self-merge must still answer the type. A fix that turned
    # `typeMerge` into a constant `null` would redden here and nowhere else.
    test-typeMerge-nullary-self-merges = {
      expr = {
        raw = describe (gmT.raw.typeMerge gmT.raw.functor);
        deferredModule = describe (gmT.deferredModule.typeMerge gmT.deferredModule.functor);
        anything = describe (gmT.anything.typeMerge gmT.anything.functor);
        leaf = describe (gmT.str.typeMerge gmT.str.functor);
        crossName = describe (gmT.raw.typeMerge gmT.anything.functor);
      };
      expected = {
        raw = "raw";
        deferredModule = "deferredModule";
        anything = "anything";
        leaf = "string";
        crossName = "<not-mergeable>";
      };
    };

    # FOREIGN functors. nixpkgs asserts payload-presence symmetry because every functor it meets is its
    # own; gen-merge meets nixpkgs' by construction (a gen type mounted in `lib.evalModules`, where the
    # same option may also be declared with a nixpkgs type). Each row would otherwise abort on a missing
    # attribute or silently rebuild a gen container from a payload it does not understand:
    #   listOf   — names agree and payload shapes agree, so the ELEMENTS are compared; gen-types names its
    #              string type `string` and nixpkgs names it `str`, so they do not merge.
    #   submodule— names agree, payload SHAPES do not (nixpkgs `submoduleWith` carries `class`/
    #              `specialArgs`/… beside `modules`); truncating that into a gen-merge submodule would
    #              drop them silently, so the answer is "not mergeable".
    #   enumElem — a gen-types PARAMETRIC leaf IS protocol-completed, so it has a `functor`; its
    #              `typeMerge` REFUSES, because its parameters live behind the checker closures and are
    #              not introspectable. The container inherits that refusal through `mergeElemTypes`.
    #              This row is where the completion and the element guard are pinned to AGREE: the guard
    #              handles a missing half, the completion removes the missing half, and the answer for
    #              this element is "not mergeable" either way — for a stated reason, not by accident.
    test-typeMerge-foreign-functor = {
      expr = {
        listOf = describe (
          (gmT.listOf gmT.str).typeMerge (nixpkgsLib.types.listOf nixpkgsLib.types.str).functor
        );
        submodule = describe (subA.typeMerge (nixpkgsLib.types.submodule { }).functor);
        enumElem = describe (
          (gmT.attrsOf (gmT.enum "e" [ "a" ])).typeMerge (gmT.attrsOf (gmT.enum "e" [ "a" ])).functor
        );
        # control: the SAME probe over an element that IS protocol-complete does merge.
        completeElem = describe ((gmT.attrsOf gmT.str).typeMerge (gmT.attrsOf gmT.str).functor);
      };
      expected = {
        listOf = "<not-mergeable>";
        submodule = "<not-mergeable>";
        enumElem = "<not-mergeable>";
        completeElem = "attrsOf of string";
      };
    };

    # END TO END, inside a REAL nixpkgs `lib.evalModules`: one option, two declarations. Agreeing element
    # types reconcile and the option RESOLVES — the value is pinned, not a boolean — while disagreeing
    # element types are refused by nixpkgs' own already-declared path instead of one declaration being
    # dropped and the survivor deciding the option's type.
    #
    # The clash is `str` against `either str int` DELIBERATELY: the definition `"s"` is valid under BOTH
    # element types, so a blind container merge ACCEPTS and this row reddens. A clash whose definition
    # only type-checks on one side (`str` vs `int`) would abort under the blind merge too — for the
    # value's reason, not the type's — and could not tell the two behaviours apart.
    test-typeMerge-two-declarations-in-nixpkgs = {
      expr = {
        agree = declTwice (gmT.attrsOf gmT.str) (gmT.attrsOf gmT.str);
        clashResolves = resolves (
          declTwice (gmT.attrsOf gmT.str) (gmT.attrsOf (gmT.either gmT.str gmT.int))
        );
        # control: the same shape under NIXPKGS types answers identically, so the rows above are the
        # protocol being reproduced rather than gen-merge failing for an unrelated reason.
        nixpkgsAgree = declTwice (nixpkgsLib.types.attrsOf nixpkgsLib.types.str) (
          nixpkgsLib.types.attrsOf nixpkgsLib.types.str
        );
        nixpkgsClashResolves = resolves (
          declTwice (nixpkgsLib.types.attrsOf nixpkgsLib.types.str) (
            nixpkgsLib.types.attrsOf (nixpkgsLib.types.either nixpkgsLib.types.str nixpkgsLib.types.int)
          )
        );
      };
      expected = {
        agree = {
          k = "s";
        };
        clashResolves = false;
        nixpkgsAgree = {
          k = "s";
        };
        nixpkgsClashResolves = false;
      };
    };
    # BOUNDARY REGRESSION (den's `den.schema._kindNames`): a gen-merge submodule whose base module sets a
    # `readOnly` config value, mounted in a nixpkgs `evalModules`. nixpkgs `fixupOptionType`
    # (modules.nix:1477) round-trips the type's OWN `getSubModules` (relocated) back through
    # `substSubModules`. A CONCAT (`mods ++ m`) duplicates the base module → the readOnly config is emitted
    # twice → "read-only … defined 2 times". `substSubModules` must REPLACE (nixpkgs `submoduleWith`), so
    # the base runs exactly once and the readOnly value resolves.
    test-readonly-base-single-eval = {
      expr =
        let
          roMod =
            { config, ... }:
            {
              freeformType = gmT.lazyAttrsOf gmT.str;
              options._keys = genMerge.mkOption {
                type = gmT.listOf gmT.str;
                internal = true;
                readOnly = true;
              };
              config._keys = builtins.filter (k: !prefixed k) (builtins.attrNames config);
            };
          sub = mount (gmT.submodule roMod) {
            a = "x";
            b = "y";
          };
        in
        {
          keys = sub._keys;
          a = sub.a;
        };
      expected = {
        keys = [
          "a"
          "b"
        ];
        a = "x";
      };
    };

    # SEMANTIC: `submodule.substSubModules` rebuilds a submodule type extended with the option's modules.
    test-substSubModules-rebuilds = {
      expr =
        let
          rebuilt = (gmT.submodule { }).substSubModules [ strMod ];
        in
        {
          name = rebuilt.name;
          isType = rebuilt._type or "<none>";
        };
      expected = {
        name = "submodule";
        isType = "option-type";
      };
    };
  };
}
