# DECLARATION MERGE — one option loc declared by more than one module.
#
# The value side of the rule; the refusal MESSAGES are cells on the second output
# (`../tests-error.nix`), since `tryEval` discards the text. Three things are asserted here:
#
#   1. the ROUTING — a redeclared leaf's type is `typeMerge`'s answer about the declared-type list
#      (bracketed as nixpkgs brackets it; a pair is the one-step case), and the
#      library's own algebra is what decides it (the same table, read directly, sits beside the
#      routed one so a passing routing row cannot be read as the algebra having been bypassed);
#   2. the DISCRIMINATION — pairs that merge still evaluate, and a module that layers a field onto
#      an earlier typed leaf without declaring a type of its own is not a redeclaration at all;
#   3. RECOVERABILITY — where the ordered fold biases a non-type field, what it shadowed is still
#      reachable. Before this rule the overridden declaration was reachable from NOWHERE on the
#      result: sweeping every surface of a two-declaration eval for the losing default matched
#      nothing, with the winner's own default matching in the same sweep as the live control.
{
  evalRequest,
  genMerge,
  nixpkgsLib,
  interface,
  ...
}:
let
  inherit (genMerge) evalModuleTree mkOption;
  t = genMerge.types;
  np = nixpkgsLib;

  # THE ALGEBRA, read directly: `a.typeMerge b.functor` on a pair of types.
  algebra =
    a: b:
    let
      r = builtins.tryEval (a.typeMerge b.functor);
    in
    if !r.success then
      "ABORT"
    else if r.value == null then
      "NULL-REFUSE"
    else
      "MERGED:" + (r.value.name or "<unnamed>");

  # THE ROUTING: the same pair as two DECLARATIONS of one option, through the engine. Neither
  # declaration carries a default and nothing defines `x`, so this reads the declaration merge and
  # only the declaration merge — no value is realized.
  routed =
    a: b:
    let
      r =
        builtins.tryEval
          (evalModuleTree { } [
            {
              _file = "a.nix";
              options.x = mkOption { type = a; };
            }
            {
              _file = "b.nix";
              options.x = mkOption { type = b; };
            }
          ]).options.x.type.name;
    in
    if r.success then "MERGED:" + r.value else "REFUSED";

  # Two declarations that both carry a `default` and a `description` — the ordered fold's bias, and
  # what it shadows. `str`/`str` merge, so this arm is about the bias rather than about the refusal.
  shadowing = {
    modules = [
      {
        _file = "a.nix";
        options.x = mkOption {
          type = t.str;
          default = "from-A";
          description = "desc-A";
        };
      }
      {
        _file = "b.nix";
        options.x = mkOption {
          type = t.str;
          default = "from-B";
          description = "desc-B";
        };
      }
    ];
  };
  # The gen-schema ref-binding shape: a second module layers `apply` onto an earlier typed leaf and
  # declares no type of its own. It restates nothing, so nothing is shadowed.
  layering = {
    modules = [
      {
        _file = "a.nix";
        options.x = mkOption {
          type = t.str;
          default = "from-A";
        };
      }
      {
        _file = "b.nix";
        options.x = mkOption { apply = v: v + "!"; };
      }
    ];
  };
  loserOf = o: {
    inherit (o) file;
    inherit (o.declaration) default;
  };
in
{
  flake.tests.decl-merge = {

    # e07bf: a redeclared option's TYPE is the nixpkgs bracketing of its declaration list,
    # [a,b,c] = (c > b) > a, and an earlier gen-native relation's refusal is never overruled.
    # Two engines, one table; `ref` is nixpkgs live, so a dead reference cannot pass silently.
    test-redeclaration-type-follows-the-nixpkgs-bracketing =
      let
        B = np.types.attrsOf np.types.int;
        tagged = tag: B // { typeMerge = _f: B // { description = tag; }; };
        Fint = np.types.int // {
          typeMerge = _: np.types.str;
        };
        Fx = np.types.str // {
          typeMerge = _: np.types.int;
        };
        fOver = B // {
          functor = B.functor // {
            name = "other";
          };
        };
        # a prefix that refuses and a whole list that merges, with a relation that keeps every name
        # it is handed: `[fOver, B]` refuses (B's relation declines fOver's functor), and `Fk`'s answer
        # is an `attrsOf int` whose own relation admits anything
        Fk = B // {
          typeMerge = _: B // { typeMerge = _: B; };
        };
        tmNull = B // {
          typeMerge = _: null;
        };
        read =
          ev: mk: Ts: rd:
          let
            r = builtins.tryEval (
              let
                v = rd (ev { modules = map (T: { options.p = mk { type = T; }; }) Ts; }).options.p.type;
              in
              builtins.deepSeq v v
            );
          in
          if r.success then r.value else "REFUSE";
        d = ty: ty.description;
        el = ty: ty.nestedTypes.elemType.description;
        n = ty: ty.name;
        table = ev: mk: {
          pair-decider-12 = read ev mk [ (tagged "first") (tagged "second") ] d;
          pair-decider-21 = read ev mk [ (tagged "second") (tagged "first") ] d;
          pair-typeMerge-null-12 = read ev mk [ tmNull B ] n;
          pair-typeMerge-null-21 = read ev mk [ B tmNull ] n;
          pair-functor-override-12 = read ev mk [ fOver B ] n;
          pair-functor-override-21 = read ev mk [ B fOver ] n;
          pair-nested-decider-12 = read ev mk [
            (np.types.listOf (tagged "first"))
            (np.types.listOf (tagged "second"))
          ] el;
          three-tagged = read ev mk [ (tagged "first") (tagged "second") (tagged "third") ] d;
          three-int-Fint-str = read ev mk [ np.types.int Fint np.types.str ] n;
          three-Fint-int-str = read ev mk [ Fint np.types.int np.types.str ] n;
          three-fo-B-Fk = read ev mk [ fOver B Fk ] n;
          four-int-int-Fint-str = read ev mk [ np.types.int np.types.int Fint np.types.str ] n;
          four-int-Fint-int-int = read ev mk [ np.types.int Fint np.types.int np.types.int ] n;
          ctl-int-int-int = read ev mk [ np.types.int np.types.int np.types.int ] n;
          ctl-int-int-str = read ev mk [ np.types.int np.types.int np.types.str ] n;
        };
        expected = {
          pair-decider-12 = "second";
          pair-decider-21 = "first";
          pair-typeMerge-null-12 = "attrsOf";
          pair-typeMerge-null-21 = "REFUSE";
          pair-functor-override-12 = "REFUSE";
          pair-functor-override-21 = "attrsOf";
          pair-nested-decider-12 = "second";
          three-tagged = "attribute set of signed integer";
          three-int-Fint-str = "REFUSE";
          three-Fint-int-str = "REFUSE";
          three-fo-B-Fk = "attrsOf";
          four-int-int-Fint-str = "REFUSE";
          four-int-Fint-int-int = "int";
          ctl-int-int-int = "int";
          ctl-int-int-str = "REFUSE";
        };
      in
      {
        expr = {
          gm = table evalRequest mkOption;
          ref = table np.evalModules np.mkOption;
          # the gen-native veto across a fold step it is not adjacent to by position
          gen-first-int-Fint-str = read evalRequest mkOption [ t.int Fint np.types.str ] n;
          # the one departure, by refusing: `Fx`'s relation answers `int` for `str`, which keeps
          # neither operand's name (nixpkgs answers `int`)
          renaming-int-str-Fx = read evalRequest mkOption [ np.types.int np.types.str Fx ] n;
        };
        expected = {
          gm = expected;
          ref = expected;
          gen-first-int-Fint-str = "REFUSE";
          renaming-int-str-Fx = "REFUSE";
        };
      };
    # e07bf, the FREEFORM twin: the winner list folds the same way, `[A, fo, B]` included (A's
    # relation answers an `attrsOf int` whose element folds to 42, `fo` renames the functor, B is
    # `attrsOf int`: nixpkgs refuses, and a left fold with the later operand deciding would accept).
    # `ref` is nixpkgs live. A relation that renames is the one departure, by refusing.
    test-freeform-type-follows-the-nixpkgs-bracketing =
      let
        B = np.types.attrsOf np.types.int;
        A = B // {
          typeMerge = _f: np.types.attrsOf (np.types.int // { merge = _loc: _defs: 42; });
        };
        Ar = B // {
          typeMerge = _f: np.types.attrsOf np.types.str;
        };
        Bf = B // {
          typeMerge = _f: np.types.attrsOf np.types.int;
        };
        fOver = B // {
          functor = B.functor // {
            name = "other";
          };
        };
        tmNull = B // {
          typeMerge = _: null;
        };
        read =
          ev: Ts: V:
          let
            r = builtins.tryEval (
              let
                v = (ev { modules = map (T: { freeformType = T; }) Ts ++ [ { x = V; } ]; }).config.x;
              in
              builtins.deepSeq v v
            );
          in
          if r.success then r.value else "REFUSE";
        table = ev: {
          ff-decider-12 = read ev [ A Bf ] 1;
          ff-decider-21 = read ev [ Bf A ] 1;
          ff-functor-override-12 = read ev [ fOver B ] 1;
          ff-functor-override-21 = read ev [ B fOver ] 1;
          ff-typeMerge-null-12 = read ev [ tmNull B ] 1;
          ff-typeMerge-null-21 = read ev [ B tmNull ] 1;
          ff-three-A-fo-B = read ev [ A fOver B ] 1;
          ff-ctl = read ev [ B B ] 1;
          ff-ctl-bad = read ev [ B B ] "s";
        };
        expected = {
          ff-decider-12 = 1;
          ff-decider-21 = 42;
          ff-functor-override-12 = "REFUSE";
          ff-functor-override-21 = 1;
          ff-typeMerge-null-12 = 1;
          ff-typeMerge-null-21 = "REFUSE";
          ff-three-A-fo-B = "REFUSE";
          ff-ctl = 1;
          ff-ctl-bad = "REFUSE";
        };
      in
      {
        expr = {
          gm = table evalRequest;
          ref = table np.evalModules;
          ff-renaming-21 = read evalRequest [ Bf Ar ] "s";
        };
        expected = {
          gm = expected;
          ref = expected;
          ff-renaming-21 = "REFUSE";
        };
      };

    # e07bf: two `submodule` declarations merge to a submodule over the union of their modules, in
    # AUTHORED order, as nixpkgs unions them. The partner of the deciding (later) declaration is the
    # earlier one, so the relation puts the partner's modules first; this is the only pin on that
    # line of `mkSubmodule`'s relation. `ref` is nixpkgs live over the same records.
    test-submodule-redeclaration-unions-in-authored-order =
      let
        first = t.submodule {
          options.l = mkOption { type = t.listOf t.str; };
          config.l = [ "first-listed" ];
        };
        second = t.submodule { config.l = [ "second-listed" ]; };
        nFirst = t.attrsOf first;
        nSecond = t.attrsOf second;
        read =
          ev: mk: Ts: V: rd:
          rd (ev { modules = map (T: { options.p = mk { type = T; }; }) Ts ++ [ { p = V; } ]; }).config.p;
        table = ev: mk: {
          o12 = read ev mk [ first second ] { } (p: p.l);
          o21 = read ev mk [ second first ] { } (p: p.l);
          nested-o12 = read ev mk [ nFirst nSecond ] { k = { }; } (p: p.k.l);
          nested-o21 = read ev mk [ nSecond nFirst ] { k = { }; } (p: p.k.l);
        };
        expected = {
          o12 = [
            "second-listed"
            "first-listed"
          ];
          o21 = [
            "first-listed"
            "second-listed"
          ];
          nested-o12 = [
            "second-listed"
            "first-listed"
          ];
          nested-o21 = [
            "first-listed"
            "second-listed"
          ];
        };
      in
      {
        expr = {
          gm = table evalRequest mkOption;
          ref = table np.evalModules np.mkOption;
        };
        expected = {
          gm = expected;
          ref = expected;
        };
      };

    # zvidt: ONE option declared by a nixpkgs container and a gen container has ONE declared-type spine
    # whichever declaration comes first, under either engine: nixpkgs' own. `sig` asks `? typeMergeRel`,
    # which every gen record states (a `? carries` test never reads a gen leaf: den-hoag-x4j3w). The partner's relation
    # decides the record at every container level (`interface.joinCarriedInStatedRelation`), so no
    # gen record survives into the declared type. `sig` reads whose record each level of the merged
    # spine is, through `nestedTypes`; `ref` is the same table with the gen side replaced by its
    # nixpkgs twin, live. `u8` pins the refusal the rule must not widen: a join that drops a wrapper's
    # check is not taken (ADR-0025 item 1): gen's engine refuses `u8` beside `int` natively, so the mixed
    # pair refuses too, and a rule that dropped the witness would serve it. `lazyList` is a raw foreign
    # container named like gen's `listOf` whose payload names MORE than the element (`attrsWith`'s
    # shape): gen does not read it whole, so the pair is not joined and answers as it did before the
    # rule, in both orders under both engines. Its removal serves the gen-first gm pair.
    test-mixed-container-redeclaration-outer-record-is-order-independent =
      let
        engines = {
          np = {
            ev = np.evalModules;
            mk = np.mkOption;
          };
          gm = {
            ev = evalRequest;
            mk = mkOption;
          };
        };
        sub = lib': lib'.submodule { options.y = np.mkOption { type = np.types.int; }; };
        shapes = {
          leaf = lib': lib'.listOf lib'.int;
          null-leaf = lib': lib'.nullOr lib'.int;
          list-list = lib': lib'.listOf (lib'.listOf lib'.int);
          null-list = lib': lib'.nullOr (lib'.listOf lib'.int);
          null-null = lib': lib'.nullOr (lib'.nullOr lib'.int);
          list-sub = lib': lib'.listOf (sub lib');
        };
        sig =
          fuel: ty:
          (if ty ? typeMergeRel then "G" else "N")
          + (
            if fuel == 0 || !(ty ? nestedTypes) then
              ""
            else
              "("
              + builtins.concatStringsSep "," (
                map (k: sig (fuel - 1) ty.nestedTypes.${k}) (builtins.attrNames ty.nestedTypes)
              )
              + ")"
          );
        read =
          eng: Ts:
          let
            r = engines.${eng}.ev {
              modules = map (T: { options.x = engines.${eng}.mk { type = T; }; }) Ts;
            };
            tried = builtins.tryEval (sig 4 r.options.x.type);
          in
          if tried.success then tried.value else "REFUSED";
        table =
          twin:
          builtins.listToAttrs (
            builtins.concatMap
              (
                eng:
                builtins.concatMap (
                  k:
                  let
                    a = shapes.${k} np.types;
                    b = shapes.${k} (if twin then np.types else t);
                  in
                  [
                    {
                      name = "${eng}-${k}-o12";
                      value = read eng [
                        a
                        b
                      ];
                    }
                    {
                      name = "${eng}-${k}-o21";
                      value = read eng [
                        b
                        a
                      ];
                    }
                  ]
                ) (builtins.attrNames shapes)
              )
              [
                "np"
                "gm"
              ]
          );
        lazyList =
          let
            lazyList = np.mkOptionType {
              name = "listOf";
              description = "lazyList";
              check = builtins.isList;
              merge = (np.types.listOf np.types.int).merge;
              functor = {
                name = "listOf";
                wrapped = null;
                payload = {
                  elemType = np.types.int;
                  lazy = true;
                };
                type =
                  p:
                  np.mkOptionType {
                    name = "listOf";
                    description = if p.lazy then "lazy" else "strict";
                    check = builtins.isList;
                    merge = (np.types.listOf np.types.int).merge;
                    functor = lazyList.functor // {
                      payload = p;
                    };
                    nestedTypes.elemType = p.elemType;
                  };
                binOp =
                  a: b:
                  let
                    m = a.elemType.typeMerge b.elemType.functor;
                  in
                  if m == null then
                    null
                  else
                    {
                      elemType = m;
                      lazy = a.lazy;
                    };
              };
              nestedTypes.elemType = np.types.int;
            };
            L = t.listOf t.int;
            readD =
              eng: Ts:
              let
                r = engines.${eng}.ev {
                  modules = map (T: { options.x = engines.${eng}.mk { type = T; }; }) Ts;
                };
                tried = builtins.tryEval r.options.x.type.description;
              in
              if tried.success then tried.value else "REFUSED";
          in
          {
            np-o12 = readD "np" [
              lazyList
              L
            ];
            np-o21 = readD "np" [
              L
              lazyList
            ];
            gm-o12 = readD "gm" [
              lazyList
              L
            ];
            gm-o21 = readD "gm" [
              L
              lazyList
            ];
          };
        u8 = {
          ref = (
            read "gm" [
              (np.types.listOf np.types.ints.u8)
              (np.types.listOf np.types.int)
            ]
          );
          mixed = (
            read "gm" [
              (np.types.listOf np.types.ints.u8)
              (t.listOf t.int)
            ]
          );
        };
      in
      {
        expr = {
          mixed = table false;
          ref = table true;
          inherit u8 lazyList;
        };
        expected = {
          mixed = table true;
          ref = table true;
          lazyList = {
            np-o12 = "REFUSED";
            np-o21 = "lazy";
            gm-o12 = "REFUSED";
            gm-o21 = "REFUSED";
          };
          u8 = {
            ref = "REFUSED";
            mixed = "REFUSED";
          };
        };
      };

    # x4j3w: ONE option declared by a nixpkgs LEAF and by its gen twin has ONE declared-type record
    # whichever declaration comes first, under either engine: nixpkgs'. `sig` asks `? typeMergeRel`, which
    # EVERY gen record states and no nixpkgs record does; the zvidt cell above asked `? carries`, which a
    # gen leaf never states, so it could not read a gen record at a leaf. The domain is the leaves whose
    # functor name and payload agree with their nixpkgs twin's (`str`, `path` and `pathLike` publish
    # nixpkgs' under an embedding, the next cell; `number` is not nixpkgs' `either`; `attrs` is a stated
    # divergence, not a defect: gen's `attrs` fold refuses a same-key collision and nixpkgs' `//` takes the
    # last, so a foreign `attrs` stays refused, owner-ruled in den-hoag-241d7, specs/2026-09-16-gen-attrs-empty-value-spec.md §4.1). `expected` is a LITERAL spine, and `ref` (the gen
    # side replaced by its nixpkgs twin, live) must equal the same literal, so a `ref` broken in step with
    # `mixed` cannot pass. `gg` is the control that the predicate sees a gen record at all.
    test-mixed-leaf-redeclaration-record-is-order-independent =
      let
        engines = {
          np = {
            ev = np.evalModules;
            mk = np.mkOption;
          };
          gm = {
            ev = evalRequest;
            mk = mkOption;
          };
        };
        leaves = {
          anything = 1;
          bool = true;
          float = 1.5;
          int = 1;
          raw = 1;
        };
        shapes = {
          bare = {
            wrap = lib': ty: ty;
            def = v: v;
            lit = rec': "${rec'}";
          };
          list = {
            wrap = lib': ty: lib'.listOf ty;
            def = v: [ v ];
            lit = rec': "${rec'}(${rec'})";
          };
          null = {
            wrap = lib': ty: lib'.nullOr ty;
            def = v: v;
            lit = rec': "${rec'}(${rec'})";
          };
        };
        sig =
          ty:
          (if ty ? typeMergeRel then "G" else "N")
          + (if ty ? nestedTypes.elemType then "(${sig ty.nestedTypes.elemType})" else "");
        read =
          eng: Ts: def:
          let
            r = engines.${eng}.ev {
              modules = map (T: { options.x = engines.${eng}.mk { type = T; }; }) Ts ++ [ { x = def; } ];
            };
            tried = builtins.tryEval (
              builtins.deepSeq r.config.x "${sig r.options.x.type} v=${builtins.toJSON r.config.x}"
            );
          in
          if tried.success then tried.value else "REFUSED";
        table =
          side: lit: lit':
          builtins.listToAttrs (
            builtins.concatMap
              (
                eng:
                builtins.concatMap (
                  leaf:
                  builtins.concatMap (
                    shape:
                    let
                      s = shapes.${shape};
                      aLib = if side == "gg" then t else np.types;
                      bLib = if side == "nn" then np.types else t;
                      a' = s.wrap aLib aLib.${leaf};
                      b = s.wrap bLib bLib.${leaf};
                      v = " v=${builtins.toJSON (s.def leaves.${leaf})}";
                      want = (s.lit (if side == "gg" then "G" else "N")) + v;
                    in
                    [
                      {
                        name = "${eng}-${leaf}-${shape}-o12";
                        value = [
                          (read eng [ a' b ] (s.def leaves.${leaf}))
                          want
                        ];
                      }
                      {
                        name = "${eng}-${leaf}-${shape}-o21";
                        value = [
                          (read eng [ b a' ] (s.def leaves.${leaf}))
                          want
                        ];
                      }
                    ]
                  ) (builtins.attrNames shapes)
                ) (builtins.attrNames leaves)
              )
              [
                "np"
                "gm"
              ]
          );
        pairs = tbl: builtins.mapAttrs (_: v: builtins.elemAt v 0) tbl;
        wants = tbl: builtins.mapAttrs (_: v: builtins.elemAt v 1) tbl;
        mixed = table "mixed" null null;
        ref = table "nn" null null;
        gg = table "gg" null null;
        # PIN OF THE PARTNER'S OWN DIVERGENCE, not of a gen property: the partner's `typeMerge` refuses
        # where its functor's relation serves. A partner whose own `typeMerge` disagrees with the relation its functor states: where gen
        # decides it gets the FUNCTOR's relation (4v489), never the partner's own `typeMerge`. Where the
        # partner decides it refuses, as it does beside nixpkgs' own `int`, so that order stays refused.
        hand = np.types.int // {
          typeMerge = _: null;
        };
        # A STATED DIVERGENCE (ADR-0025 item 1), not a gen defect: a partner named like the leaf whose
        # functor republishes a differently named type. The join renames it, so it is not taken and the
        # pair answers as it did before (`joinRenames`). Where nixpkgs' twin serves it (`np-o12`), it
        # serves the partner's record, dropping a stricter check the partner might carry: gen cannot
        # compare check closures, so serving this partner would serve its strict sibling silently.
        alias = np.types.mkOptionType {
          name = "int";
          description = "alias";
          check = builtins.isInt;
          merge = np.types.int.merge;
          functor = np.types.int.functor // {
            type = np.types.str;
          };
        };
        # A raw foreign leaf whose functor omits `type`: the protocol's default would abort reading it,
        # so the join is not taken and gen's own relation answers, as it did before (C1). Where nixpkgs'
        # twin serves it (`np-o12`) gen refuses, a STATED DIVERGENCE (ADR-0025 item 1): gen cannot compare
        # check closures, so serving this partner would serve its strict sibling silently.
        notype = np.types.int // {
          functor = builtins.removeAttrs np.types.int.functor [ "type" ];
        };
        # The same pair at TWO definitions. The join hands the partner's record to the merge, so a pair
        # nixpkgs refuses at two definitions is refused np-first too, where gen's own record served it:
        # `raw` at two equal definitions or two list definitions, `anything` at two unequal list
        # definitions, bare and under `nullOr`, in both engines (12 rows moved from served to REFUSED).
        # That is nixpkgs' answer in the order where it decides, and `ref` reads it live.
        twoCases = {
          int = [ "eq2" ];
          raw = [
            "eq2"
            "lst2"
          ];
          anything = [
            "eq2"
            "lst2"
            "lst2b"
          ];
        };
        twoDefs =
          side:
          let
            defsOf = v: {
              eq2 = [
                v
                v
              ];
              lst2 = [
                [ v ]
                [ v ]
              ];
              lst2b = [
                [ v ]
                [
                  v
                  v
                ]
              ];
            };
          in
          builtins.listToAttrs (
            builtins.concatMap
              (
                eng:
                builtins.concatMap (
                  leaf:
                  builtins.concatMap (
                    ds:
                    builtins.concatMap
                      (
                        shape:
                        let
                          s = shapes.${shape};
                          aLib = if side == "nn" then np.types else t;
                          a' = s.wrap aLib aLib.${leaf};
                          b = s.wrap np.types np.types.${leaf};
                          rd =
                            Ts:
                            let
                              r = engines.${eng}.ev {
                                modules =
                                  map (T: { options.x = engines.${eng}.mk { type = T; }; }) Ts
                                  ++ map (d: { x = d; }) (defsOf leaves.${leaf}).${ds};
                              };
                              tried = builtins.tryEval (builtins.deepSeq r.config.x "served");
                            in
                            if tried.success then tried.value else "REFUSED";
                        in
                        [
                          {
                            name = "${eng}-${leaf}-${ds}-${shape}-o12";
                            value = rd [
                              a'
                              b
                            ];
                          }
                          {
                            name = "${eng}-${leaf}-${ds}-${shape}-o21";
                            value = rd [
                              b
                              a'
                            ];
                          }
                        ]
                      )
                      [
                        "bare"
                        "null"
                      ]
                  ) twoCases.${leaf}
                ) (builtins.attrNames twoCases)
              )
              [
                "np"
                "gm"
              ]
          );
        twoWant = builtins.mapAttrs (
          k: _:
          let
            parts = builtins.match "(np|gm)-([a-z]+)-([a-z0-9]+)-(bare|null)-(o12|o21)" k;
            leaf = builtins.elemAt parts 1;
            ds = builtins.elemAt parts 2;
          in
          if leaf == "raw" || (leaf == "anything" && ds == "lst2b") then "REFUSED" else "served"
        ) (twoDefs "nn");
        partnerRows =
          p:
          builtins.listToAttrs (
            builtins.concatMap
              (eng: [
                {
                  name = "${eng}-o12";
                  value = read eng [ p t.int ] 1;
                }
                {
                  name = "${eng}-o21";
                  value = read eng [ t.int p ] 1;
                }
              ])
              [
                "np"
                "gm"
              ]
          );
      in
      {
        expr = {
          mixed = pairs mixed;
          ref = pairs ref;
          gg = pairs gg;
          hand = partnerRows hand;
          alias = partnerRows alias;
          notype = partnerRows notype;
          two = twoDefs "mixed";
          twoRef = twoDefs "nn";
        };
        expected = {
          mixed = wants mixed;
          ref = wants ref;
          gg = wants gg;
          hand = {
            np-o12 = "N v=1";
            np-o21 = "REFUSED";
            gm-o12 = "N v=1";
            gm-o21 = "REFUSED";
          };
          notype = {
            np-o12 = "REFUSED";
            np-o21 = "N v=1";
            gm-o12 = "G v=1";
            gm-o21 = "N v=1";
          };
          two = twoWant;
          twoRef = twoWant;
          alias = {
            np-o12 = "REFUSED";
            np-o21 = "REFUSED";
            gm-o12 = "G v=1";
            gm-o21 = "REFUSED";
          };
        };
      };

    # 1t2p5: a gen leaf beside a SAME-KEYED raw partner that STATES A PAYLOAD (`interface.statesPayload`).
    # nixpkgs asks only the LATER declaration's relation, so the mixed pair has the twin's answer in each
    # order, as the leaf relation's payload refusal decides without vetoing (`vetoes = false`):
    #  - `pay`: a partner on nixpkgs' default relation, which asserts two leaves agree on a payload. The
    #    twin refuses it in both orders and both engines, and so does the mixed pair. At 1cc1b25 the
    #    partner-first rows served `v` (gen's engine every shape, nixpkgs' under a container), the
    #    partner's check dropped unsaid (ADR-0025 item 1).
    #  - `acc`: a partner whose OWN relation joins a payload-free leaf of its name, keeping itself. Gen
    #    declared first, that relation decides and serves (the twin serves, keeping the partner's check);
    #    partner first, gen decides as its twin does and refuses. A refusal there vetoing served nothing
    #    in the gen-first order (spec v0's arm B).
    #  - `control`: the same partner as `pay` stating no payload, served as the twin serves it, so a
    #    relation refusing every declined same-key join cannot pass.
    #  - `genOnly`: the gen leaves no nixpkgs leaf twins, beside a `pay` partner of their name: refused in
    #    every row (no twin; ADR-0025 item 1 alone).
    #  - `accRejected`: the `acc` partner over a value the GEN leaf's check rejects, gen's engine, gen
    #    declared first. The partner's relation decides and keeps itself, so the gen leaf's check is
    #    dropped and the value is served, as the twin serves it. That is nixpkgs' own later-operand drop,
    #    NOT correct behaviour: it is pinned as parity, and the meet (den-hoag-l1j4q) turns these rows
    #    into named refusals.
    # `expected` is a LITERAL, and every `*Ref` (the gen side replaced by its nixpkgs twin, live) must
    # equal it.
    test-mixed-leaf-payload-partner-has-the-twin-answer =
      let
        engines = {
          np = {
            ev = np.evalModules;
            mk = np.mkOption;
          };
          gm = {
            ev = evalRequest;
            mk = mkOption;
          };
        };
        leaves = {
          anything = 1;
          bool = true;
          float = 1.5;
          int = 7;
          raw = 1;
        };
        genOnly = {
          any = 1;
          list = [ 1 ];
          never = null;
          null = null;
        };
        shapes = {
          bare = {
            wrap = lib': ty: ty;
            def = v: v;
          };
          list = {
            wrap = lib': ty: lib'.listOf ty;
            def = v: [ v ];
          };
          null = {
            wrap = lib': ty: lib'.nullOr ty;
            def = v: v;
          };
          attrs = {
            wrap = lib': ty: lib'.attrsOf ty;
            def = v: { k = v; };
          };
        };
        partners = {
          pay =
            leaf: v:
            np.mkOptionType {
              name = leaf;
              check = x: x != v;
              merge = np.options.mergeEqualOption;
              functor = np.types.defaultFunctor leaf // {
                payload.strict = true;
                binOp = _a: _b: null;
              };
            };
          control =
            leaf: v:
            np.mkOptionType {
              name = leaf;
              check = x: x != v;
              merge = np.options.mergeEqualOption;
              functor = np.types.defaultFunctor leaf;
            };
          acc =
            leaf: _v:
            let
              self = np.mkOptionType {
                name = leaf;
                check = _: true;
                merge = np.options.mergeEqualOption;
                functor = np.types.defaultFunctor leaf // {
                  type = _: self;
                  payload.refined = true;
                  binOp = a: _b: a;
                };
                typeMerge =
                  f':
                  if f'.name == leaf && (f'.payload == null || f'.payload == { refined = true; }) then self else null;
              };
            in
            self;
        };
        read =
          eng: Ts: def:
          let
            r = engines.${eng}.ev {
              modules = map (T: { options.x = engines.${eng}.mk { type = T; }; }) Ts ++ [ { x = def; } ];
            };
            tried = builtins.tryEval (builtins.deepSeq r.config.x "served");
          in
          if tried.success then tried.value else "REFUSED";
        table =
          lib': kind: subjects: shapeNames:
          builtins.listToAttrs (
            builtins.concatMap
              (
                eng:
                builtins.concatMap (
                  leaf:
                  builtins.concatMap (
                    shape:
                    let
                      s = shapes.${shape};
                      v = subjects.${leaf};
                      g = s.wrap lib' lib'.${leaf};
                      p = s.wrap np.types (partners.${kind} leaf v);
                      d = s.def v;
                    in
                    [
                      {
                        name = "${eng}-${leaf}-${shape}-genFirst";
                        value = read eng [
                          g
                          p
                        ] d;
                      }
                      {
                        name = "${eng}-${leaf}-${shape}-partnerFirst";
                        value = read eng [
                          p
                          g
                        ] d;
                      }
                    ]
                  ) shapeNames
                ) (builtins.attrNames subjects)
              )
              [
                "np"
                "gm"
              ]
          );
        all = builtins.attrNames shapes;
        literal = f: tbl: builtins.mapAttrs (k: _: f k) tbl;
        refused = literal (_: "REFUSED");
        served = literal (_: "served");
        byOrder = literal (k: if builtins.match ".*-genFirst" k != null then "served" else "REFUSED");
        rejected = {
          int = "s";
          bool = 1;
          float = "s";
        };
        gmGenFirst = np.filterAttrs (k: _: builtins.match "gm-.*-genFirst" k != null);
      in
      {
        expr = {
          pay = table t "pay" leaves all;
          payRef = table np.types "pay" leaves all;
          acc = table t "acc" leaves all;
          accRef = table np.types "acc" leaves all;
          control = table t "control" leaves all;
          controlRef = table np.types "control" leaves all;
          genOnly = table t "pay" genOnly [ "bare" ];
          accRejected = gmGenFirst (table t "acc" rejected all);
          accRejectedRef = gmGenFirst (table np.types "acc" rejected all);
        };
        expected = {
          pay = refused (table np.types "pay" leaves all);
          payRef = refused (table np.types "pay" leaves all);
          acc = byOrder (table np.types "acc" leaves all);
          accRef = byOrder (table np.types "acc" leaves all);
          control = served (table np.types "control" leaves all);
          controlRef = served (table np.types "control" leaves all);
          genOnly = refused (table t "pay" genOnly [ "bare" ]);
          accRejected = served (gmGenFirst (table np.types "acc" rejected all));
          accRejectedRef = served (gmGenFirst (table np.types "acc" rejected all));
        };
      };

    # n8cpq: an embedding row is reached by the CONSTRUCTION it stands for, never by a caller-chosen
    # name. A gen type NAMED like a row (`enum "path"`, `struct "path"`, `typedef "string"`, a
    # `mkOptionType` descriptor, a `defineType` record) beside the nixpkgs type that row stands for is refused in both
    # orders, as its nixpkgs twin is: keyed on the name, the order where nixpkgs' relation decides
    # served the partner's record with the gen check dropped, and `enum "attrsOf"` aborted. Live
    # control: gen-types' own `string` beside `str` serves, so the leaf rows still fire; the
    # container rows' liveness is pinned by caxcw's and 46zga's cells below, which red when a
    # constructor stops stating its row.
    test-embedding-row-is-keyed-on-construction =
      let
        engines = {
          np = {
            ev = np.evalModules;
            mk = np.mkOption;
          };
          gm = {
            ev = evalRequest;
            mk = mkOption;
          };
        };
        read =
          eng: Ts: def:
          let
            r = engines.${eng}.ev {
              modules = map (T: { options.x = engines.${eng}.mk { type = T; }; }) Ts ++ [ { x = def; } ];
            };
            tried = builtins.tryEval (builtins.deepSeq r.config.x "served");
          in
          if tried.success then tried.value else "REFUSED";
        desc =
          name: check:
          genMerge.mkOptionType {
            inherit name check;
            merge = np.options.mergeEqualOption;
          };
        cases = {
          enumString = {
            g = t.enum "string" [ "a" ];
            p = np.types.str;
            v = "zz";
          };
          enumPath = {
            g = t.enum "path" [ "/a" ];
            p = np.types.path;
            v = "/zz";
          };
          enumPathLike = {
            g = t.enum "pathLike" [ "/a" ];
            p = np.types.pathWith { };
            v = "/zz";
          };
          enumAttrsOf = {
            g = t.enum "attrsOf" [ "a" ];
            p = np.types.attrsOf np.types.int;
            v = { };
          };
          enumDeferredModule = {
            g = t.enum "deferredModule" [ "a" ];
            p = np.types.deferredModule;
            v = { };
          };
          structPath = {
            g = t.struct "path" { };
            p = np.types.path;
            v = "/zz";
          };
          typedefString = {
            g = t.typedef "string" (x: x == "a");
            p = np.types.str;
            v = "zz";
          };
          descPath = {
            g = desc "path" (x: x == "/a");
            p = np.types.path;
            v = "/zz";
          };
          descDeferredModule = {
            g = desc "deferredModule" (x: x == "a");
            p = np.types.deferredModule;
            v = { };
          };
          # the published construction door takes a caller's name too
          definedString = {
            g = t.defineType {
              name = "string";
              verify = x: if x == "a" then null else "not a";
            };
            p = np.types.str;
            v = "zz";
          };
          definedPath = {
            g = t.defineType {
              name = "path";
              verify = x: if x == "/a" then null else "not /a";
            };
            p = np.types.path;
            v = "/zz";
          };
          definedAttrsOf = {
            g = t.defineType {
              name = "attrsOf";
              verify = x: if x == "a" then null else "not a";
            };
            p = np.types.attrsOf np.types.int;
            v = { };
          };
          control = {
            g = t.enum "e" [ "a" ];
            p = np.types.str;
            v = "zz";
          };
          # the KEY forged rather than collided: gen-types `string`'s or `path`'s mint written onto an
          # enum by `//`, through the published construction door and through the import door,
          # neither of which hands the export a row.
          mintStringDefined = {
            g = t.defineType (t.enum "e" [ "a" ] // { inherit (t.string) __mint __payload __sealed; });
            p = np.types.str;
            v = "zz";
          };
          mintPathDefined = {
            g = t.defineType (t.enum "e" [ "/a" ] // { inherit (t.path) __mint __payload __sealed; });
            p = np.types.path;
            v = "/zz";
          };
          mintStringDescribed = {
            g = genMerge.mkOptionType (t.enum "e" [ "a" ] // { inherit (t.string) __mint __payload __sealed; });
            p = np.types.str;
            v = "zz";
          };
        };
        rowsOf =
          g: p: v:
          builtins.listToAttrs (
            builtins.concatMap
              (eng: [
                {
                  name = "${eng}-o12";
                  value = read eng [
                    g
                    p
                  ] v;
                }
                {
                  name = "${eng}-o21";
                  value = read eng [
                    p
                    g
                  ] v;
                }
              ])
              [
                "np"
                "gm"
              ]
          );
        refusedRows = {
          np-o12 = "REFUSED";
          np-o21 = "REFUSED";
          gm-o12 = "REFUSED";
          gm-o21 = "REFUSED";
        };
        servedRows = {
          np-o12 = "served";
          np-o21 = "served";
          gm-o12 = "served";
          gm-o21 = "served";
        };
      in
      {
        expr = builtins.mapAttrs (_: c: rowsOf c.g c.p c.v) cases // {
          live = rowsOf t.string np.types.str "s";
        };
        expected = builtins.mapAttrs (_: _: refusedRows) cases // {
          live = servedRows;
        };
      };

    # n8cpq OQ-A: a COMPLETED gen type handed to the published `defineType` as it is (not a
    # caller-named type) keeps its row, as its name gave it before the re-key and as nixpkgs' twin
    # (the type redeclared) serves: completion is idempotent, so a record whose completion stamp holds
    # is returned as it is, containers (`attrsOf`, `lazyAttrsOf`, `deferredModule`) included. A `//`
    # copy restating only a name-carried field (the nixpkgs idiom `string // { description = …; }`)
    # keeps its leaf row too, used as it is or re-completed; a copy replacing its predicate does not
    # (`test-join-witness-reads-the-row-a-record-reaches`).
    test-a-completed-type-through-defineType-keeps-its-row =
      let
        engines = {
          np = {
            ev = np.evalModules;
            mk = np.mkOption;
          };
          gm = {
            ev = evalRequest;
            mk = mkOption;
          };
        };
        read =
          eng: Ts: def:
          let
            r = engines.${eng}.ev {
              modules = map (T: { options.x = engines.${eng}.mk { type = T; }; }) Ts ++ [ { x = def; } ];
            };
            tried = builtins.tryEval (builtins.deepSeq r.config.x "served");
          in
          if tried.success then tried.value else "REFUSED";
        rowsOf = g: p: v: {
          np-o12 = read "np" [ g p ] v;
          np-o21 = read "np" [ p g ] v;
          gm-o12 = read "gm" [ g p ] v;
          gm-o21 = read "gm" [ p g ] v;
        };
        served = {
          np-o12 = "served";
          np-o21 = "served";
          gm-o12 = "served";
          gm-o21 = "served";
        };
        described = t.string // {
          description = "a described string";
        };
      in
      {
        expr = {
          string = rowsOf (t.defineType t.string) np.types.str "s";
          path = rowsOf (t.defineType t.path) np.types.path "/s";
          stringBesideGen = rowsOf (t.defineType t.string) t.string "s";
          attrsOf = rowsOf (t.defineType (t.attrsOf t.int)) (np.types.attrsOf np.types.int) { k = 1; };
          lazyAttrsOf = rowsOf (t.defineType (t.lazyAttrsOf t.int)) (np.types.lazyAttrsOf np.types.int) {
            k = 1;
          };
          deferredModule = rowsOf (t.defineType t.deferredModule) np.types.deferredModule { };
          attrsOfBesideGen = rowsOf (t.defineType (t.attrsOf t.int)) (t.attrsOf t.int) { k = 1; };
          describedCopy = rowsOf described np.types.str "s";
          describedCopyDefined = rowsOf (t.defineType described) np.types.str "s";
          # a copy REPLACING the predicate is not returned as it is: under nixpkgs' engine it is refused
          # beside `str` at a value only `str` admits, as its twin (the same copy of nixpkgs' `str`) is
          predicateCopyDefined =
            let
              r = rowsOf (t.defineType (
                t.string
                // {
                  name = "e";
                  verify = x: if x == "a" then null else "not a";
                }
              )) np.types.str "zz";
            in
            {
              inherit (r) np-o12 np-o21;
            };
        };
        expected = {
          string = served;
          path = served;
          stringBesideGen = served;
          attrsOf = served;
          lazyAttrsOf = served;
          deferredModule = served;
          attrsOfBesideGen = served;
          describedCopy = served;
          describedCopyDefined = served;
          predicateCopyDefined = {
            np-o12 = "REFUSED";
            np-o21 = "REFUSED";
          };
        };
      };

    # n8cpq: the join witness reads an operand's name modulo the row its RECORD reaches (`joinsAs`),
    # never one its name collides with. A caller's `enum "string"` against nixpkgs' `str` is a
    # renaming, so a join that answered `str` for it is not taken as keeping its check, and so is a
    # `//` copy of gen-types' `string` under another predicate, whose mark is its base's (the
    # completion stamp); gen-types' own `string` and `pathLike` are read as `str` and `path`, as the
    # leaf rows state.
    test-join-witness-reads-the-row-a-record-reaches = {
      expr = {
        genuineString = interface.joinRenames np.types.str t.string;
        namedString = interface.joinRenames np.types.str (t.enum "string" [ "a" ]);
        copiedString = interface.joinRenames np.types.str (
          t.string
          // {
            name = "e";
            verify = x: if x == "a" then null else "not a";
          }
        );
        genuinePathLike = interface.joinRenames np.types.path t.pathLike;
        namedPathLike = interface.joinRenames np.types.path (t.enum "pathLike" [ "/a" ]);
      };
      expected = {
        genuineString = false;
        namedString = true;
        copiedString = true;
        genuinePathLike = false;
        namedPathLike = true;
      };
    };

    # 46zga: the gen LEAVES whose nixpkgs twin publishes another functor name or payload, joined through
    # the leaf rows of `interface.embeddings`: gen-types' `string` is nixpkgs' `str`, `path` is
    # `pathWith { absolute = true; }` and `pathLike` is `pathWith { }`. A mixed redeclaration has nixpkgs'
    # answer whichever declaration comes first, under either engine, bare and under every container,
    # `either int str` included. `expected` is a LITERAL, and `ref` (the gen side replaced by its nixpkgs
    # twin, live) must equal it, as above. WITNESS rows, each refused as the twin refuses it:
    #  - gen `path` beside a constrained `pathWith`: the partner's relation over the embedding decides,
    #    and its refusal stands (at ceccd40 the partner-first rows served, the partner's check dropped);
    #  - gen `str` beside a partner of another key (`strMatching`, `lines`): pins the keying jointly
    #    with C1's refusal (the next rows); the keying alone is pinned by the naming cells of
    #    `tests-error.nix` `leaf-embedding-refusal`;
    #  - gen `str` beside a partner keyed `str` with a payload and a stricter check (`strict`), which the
    #    leaf join declines: pins that a declined embedding join is REFUSED, never answered by `self`.
    # The witness's name test (`joinRenames` modulo `joinsAs`) is guarded by the cells it already reds.
    # `number` (den-hoag-kawe8) and `enum` (den-hoag-n8cpq) embed nowhere and stay refused.
    test-mixed-leaf-embedding-redeclaration-is-nixpkgs-answer =
      let
        engines = {
          np = {
            ev = np.evalModules;
            mk = np.mkOption;
          };
          gm = {
            ev = evalRequest;
            mk = mkOption;
          };
        };
        members = {
          str = {
            g = t.str;
            n = np.types.str;
            v = "s";
            lit = "N";
          };
          path = {
            g = t.path;
            n = np.types.path;
            v = "/foo/bar";
            lit = "N";
          };
          pathLike = {
            g = t.pathLike;
            n = np.types.pathWith { };
            v = "rel/p";
            lit = "N";
          };
          eitherIntStr = {
            g = t.either t.int t.str;
            n = np.types.either np.types.int np.types.str;
            v = "s";
            lit = "N(N,N)";
          };
        };
        shapes = {
          bare = {
            wrap = lib': ty: ty;
            def = v: v;
            lit = inner: inner;
          };
          list = {
            wrap = lib': ty: lib'.listOf ty;
            def = v: [ v ];
            lit = inner: "N(${inner})";
          };
          null = {
            wrap = lib': ty: lib'.nullOr ty;
            def = v: v;
            lit = inner: "N(${inner})";
          };
          attrs = {
            wrap = lib': ty: lib'.attrsOf ty;
            def = v: { k = v; };
            lit = inner: "N(${inner})";
          };
        };
        sig =
          ty:
          let
            n = ty.nestedTypes or { };
            kids = builtins.filter (k: n ? ${k}) [
              "elemType"
              "left"
              "right"
            ];
          in
          (if ty ? typeMergeRel then "G" else "N")
          + (if kids == [ ] then "" else "(${builtins.concatStringsSep "," (map (k: sig n.${k}) kids)})");
        read =
          eng: Ts: def:
          let
            r = engines.${eng}.ev {
              modules = map (T: { options.x = engines.${eng}.mk { type = T; }; }) Ts ++ [ { x = def; } ];
            };
            tried = builtins.tryEval (
              builtins.deepSeq r.config.x "${sig r.options.x.type} v=${builtins.toJSON r.config.x}"
            );
          in
          if tried.success then tried.value else "REFUSED";
        rows =
          f:
          builtins.listToAttrs (
            builtins.concatMap
              (
                eng:
                builtins.concatMap (
                  m:
                  builtins.concatMap (
                    shape:
                    map
                      (o: {
                        name = "${eng}-${m}-${shape}-${o}";
                        value = f eng members.${m} shapes.${shape} o;
                      })
                      [
                        "o12"
                        "o21"
                      ]
                  ) (builtins.attrNames shapes)
                ) (builtins.attrNames members)
              )
              [
                "np"
                "gm"
              ]
          );
        # o12 declares the nixpkgs side first; `nn` replaces the gen side by its twin
        table =
          side:
          rows (
            eng: m: s: o:
            let
              a' = s.wrap np.types m.n;
              b = if side == "nn" then a' else s.wrap t m.g;
            in
            read eng (
              if o == "o12" then
                [
                  a'
                  b
                ]
              else
                [
                  b
                  a'
                ]
            ) (s.def m.v)
          );
        want = rows (
          eng: m: s: o:
          "${s.lit m.lit} v=${builtins.toJSON (s.def m.v)}"
        );
        # a nixpkgs type keyed `key` with a payload and a check stricter than `base`'s
        strict =
          key: base: bad:
          np.mkOptionType {
            name = key;
            check = x: base.check x && x != bad;
            merge = np.options.mergeEqualOption;
            functor = np.types.defaultFunctor key // {
              payload.strict = true;
              binOp = _a: _b: null;
            };
          };
        witnesses = {
          path = {
            g = t.path;
            n = np.types.path;
            v = "/s";
            partners = {
              pathInStore = np.types.pathInStore;
              externalPath = np.types.externalPath;
              pathWithNone = np.types.pathWith { };
              pathWithRelative = np.types.pathWith { absolute = false; };
            };
          };
          str = {
            g = t.str;
            n = np.types.str;
            v = "/s";
            partners = {
              strMatching = np.types.strMatching ".*";
              inherit (np.types) lines;
            };
          };
          strStrict = {
            g = t.str;
            n = np.types.str;
            v = "x";
            partners.strict = strict "str" np.types.str "x";
          };
        };
        witness =
          side:
          builtins.listToAttrs (
            builtins.concatMap
              (
                eng:
                builtins.concatMap (
                  w:
                  let
                    W = witnesses.${w};
                    g = if side == "nn" then W.n else W.g;
                  in
                  builtins.concatMap (p: [
                    {
                      name = "${eng}-${w}-${p}-genFirst";
                      value = read eng [
                        g
                        W.partners.${p}
                      ] W.v;
                    }
                    {
                      name = "${eng}-${w}-${p}-partnerFirst";
                      value = read eng [
                        W.partners.${p}
                        g
                      ] W.v;
                    }
                  ]) (builtins.attrNames W.partners)
                ) (builtins.attrNames witnesses)
              )
              [
                "np"
                "gm"
              ]
          );
        refused = builtins.mapAttrs (_: _: "REFUSED") (witness "nn");
      in
      {
        expr = {
          mixed = table "mixed";
          ref = table "nn";
          witness = witness "mixed";
          witnessRef = witness "nn";
        };
        expected = {
          mixed = want;
          ref = want;
          witness = refused;
          witnessRef = refused;
        };
      };

    # zcufn: ONE option declared by a nixpkgs union (`either`, `oneOf`) and a gen one has ONE declared
    # type whichever declaration comes first, under either engine: nixpkgs' own, at every member.
    # nixpkgs' `either` states its relation in `typeMerge` and publishes a functor whose `binOp` its
    # list payload cannot feed and whose `type` is the constructor curried over the members, so the
    # partner is REBUILT from that functor and the rebuilt record's relation decides
    # (`interface.joinInRebuiltPartner`). `sig` reads whose record each level is, by `typeMergeRel`,
    # which a gen LEAF states too (a `carries` test is blind at the leaf). `ref` is the gen side
    # replaced by its nixpkgs twin, live, and pinned. `hand` is a partner named `either` whose own
    # `typeMerge` refuses everything: the rebuild never calls it, so the pair answers as the twin does.
    # `u8` pins the refusal the witness keeps (ADR-0025 item 1); nixpkgs' engine serves it gen-first,
    # deciding alone (zvidt §2.4 item 1).
    test-mixed-union-redeclaration-record-is-order-independent =
      let
        engines = {
          np = {
            ev = np.evalModules;
            mk = np.mkOption;
          };
          gm = {
            ev = evalRequest;
            mk = mkOption;
          };
        };
        shapes = {
          int-bool = lib': lib'.either lib'.int lib'.bool;
          list-bool = lib': lib'.either (lib'.listOf lib'.int) lib'.bool;
          nested = lib': lib'.either (lib'.either lib'.int lib'.bool) (lib'.nullOr lib'.int);
          one-of =
            lib':
            lib'.oneOf [
              lib'.int
              lib'.bool
              (lib'.listOf lib'.int)
            ];
          list-of-either = lib': lib'.listOf (lib'.either lib'.int lib'.bool);
        };
        sig =
          fuel: ty:
          let
            n = ty.nestedTypes or { };
            kids = builtins.filter (
              k:
              builtins.elem k [
                "left"
                "right"
                "elemType"
              ]
            ) (builtins.attrNames n);
          in
          (if ty ? typeMergeRel then "G" else "N")
          + (
            if fuel == 0 || kids == [ ] then
              ""
            else
              "(" + builtins.concatStringsSep "," (map (k: sig (fuel - 1) n.${k}) kids) + ")"
          );
        read =
          eng: Ts:
          let
            r = engines.${eng}.ev {
              modules = map (T: { options.x = engines.${eng}.mk { type = T; }; }) Ts;
            };
            tried = builtins.tryEval (sig 4 r.options.x.type);
          in
          if tried.success then tried.value else "REFUSED";
        pairs =
          f:
          builtins.listToAttrs (
            builtins.concatMap
              (
                eng:
                builtins.concatMap (
                  k:
                  let
                    ab = f k;
                  in
                  [
                    {
                      name = "${eng}-${k}-o12";
                      value = read eng [
                        ab.a
                        ab.b
                      ];
                    }
                    {
                      name = "${eng}-${k}-o21";
                      value = read eng [
                        ab.b
                        ab.a
                      ];
                    }
                  ]
                ) (builtins.attrNames shapes)
              )
              [
                "np"
                "gm"
              ]
          );
        table =
          twin:
          pairs (k: {
            a = shapes.${k} np.types;
            b = shapes.${k} (if twin then np.types else t);
          });
        orders = eng: a: b: {
          o12 = read eng [
            a
            b
          ];
          o21 = read eng [
            b
            a
          ];
        };
        hand = np.types.either np.types.int np.types.bool // {
          typeMerge = _: null;
        };
        u8 = np.types.either np.types.ints.u8 np.types.bool;
        # A foreign answer that ABORTS is no answer: nixpkgs' `either` relation runs nixpkgs' code over
        # gen's members, so it is taken through `tryEval`. The relation stays total (`rel`), and the
        # union mirrors its bare `path` member pair (`leaf`), whatever that pair answers (nixpkgs'
        # record in both orders since gen `path` publishes `pathWith`'s payload, den-hoag-46zga).
        epath = {
          rel =
            let
              r = builtins.tryEval (
                builtins.attrNames (
                  (t.either t.path t.int).typeMergeRel (np.types.either np.types.path np.types.int)
                )
              );
            in
            if r.success then r.value else "ABORT";
          leaf = np.genAttrs [ "np" "gm" ] (eng: orders eng np.types.path t.path);
          union = np.genAttrs [ "np" "gm" ] (
            eng: orders eng (np.types.either np.types.path np.types.int) (t.either t.path t.int)
          );
        };
      in
      {
        expr = {
          mixed = table false;
          ref = table true;
          hand = {
            np = orders "np" hand (t.either t.int t.bool);
            gm = orders "gm" hand (t.either t.int t.bool);
            ref = orders "gm" hand (np.types.either np.types.int np.types.bool);
          };
          u8 = {
            np = orders "np" u8 (t.either t.int t.bool);
            gm = orders "gm" u8 (t.either t.int t.bool);
          };
          path = {
            inherit (epath) rel union;
          };
        };
        expected =
          let
            spine = {
              int-bool = "N(N,N)";
              list-bool = "N(N(N),N)";
              nested = "N(N(N,N),N(N))";
              one-of = "N(N(N,N),N(N))";
              list-of-either = "N(N(N,N))";
            };
            pinned = builtins.listToAttrs (
              builtins.concatMap
                (
                  eng:
                  builtins.concatMap (k: [
                    {
                      name = "${eng}-${k}-o12";
                      value = spine.${k};
                    }
                    {
                      name = "${eng}-${k}-o21";
                      value = spine.${k};
                    }
                  ]) (builtins.attrNames shapes)
                )
                [
                  "np"
                  "gm"
                ]
            );
            handPair = {
              o12 = "N(N,N)";
              o21 = "REFUSED";
            };
          in
          {
            mixed = pinned;
            ref = pinned;
            hand = {
              np = handPair;
              gm = handPair;
              ref = handPair;
            };
            u8 = {
              np = {
                o12 = "REFUSED";
                o21 = "N(N,N)";
              };
              gm = {
                o12 = "REFUSED";
                o21 = "REFUSED";
              };
            };
            path = {
              rel = [ "merged" ];
              union = np.mapAttrs (
                _: np.mapAttrs (_: l: if l == "REFUSED" then "REFUSED" else "${l}(${l},N)")
              ) epath.leaf;
            };
          };
      };

    # 4v489: ONE option declared by a nixpkgs nesting type and a gen one has ONE answer whichever
    # declaration comes first, under either engine: nixpkgs' answer. gen's parameters embed into the
    # partner's richer `submoduleWith` payload, so the pair is joined by the partner's own relation in
    # both orders (`interface.joinInStatedRelation`) and the nested element is a nixpkgs record either
    # way. `l` reads the module order the join built; `ref` is the same table with the gen side replaced
    # by its nixpkgs twin, live. A shared `specialArgs` key refuses in both orders, as nixpkgs refuses it.
    test-mixed-nesting-redeclaration-is-order-independent =
      let
        npM = {
          options.l = np.mkOption { type = np.types.listOf np.types.str; };
          config.l = [ "np-listed" ];
        };
        genM = {
          config.l = [ "gen-listed" ];
        };
        npReads =
          { foo, ... }:
          {
            options.l = np.mkOption {
              type = np.types.listOf np.types.str;
              default = [ "foo=${toString foo}" ];
            };
          };
        nixpkgsSide = {
          sub = np.types.submodule [ npM ];
          tree = (np.evalModules { modules = [ npM ]; }).type;
          args = np.types.submoduleWith {
            modules = [ npM ];
            shorthandOnlyDefinesConfig = true;
            specialArgs.foo = 1;
          };
          clash = np.types.submoduleWith {
            modules = [ npReads ];
            shorthandOnlyDefinesConfig = true;
            specialArgs.foo = 1;
          };
        };
        genSide = {
          sub = t.submodule [ genM ];
          tree = (evalModuleTree { } [ genM ]).type;
          args = (t.submodule [ genM ]).withArgs { bar = 2; };
          clash = (t.submodule [ genM ]).withArgs { foo = 1; };
        };
        twinSide = {
          sub = np.types.submodule [ genM ];
          tree = (np.evalModules { modules = [ genM ]; }).type;
          args = np.types.submoduleWith {
            modules = [ genM ];
            shorthandOnlyDefinesConfig = true;
            specialArgs.bar = 2;
          };
          clash = np.types.submoduleWith {
            modules = [ genM ];
            shorthandOnlyDefinesConfig = true;
            specialArgs.foo = 1;
          };
        };
        engines = {
          np = {
            ev = np.evalModules;
            mk = np.mkOption;
          };
          gm = {
            ev = evalRequest;
            mk = mkOption;
          };
        };
        read =
          eng: wrapped: Ts:
          let
            r = engines.${eng}.ev {
              modules = map (T: { options.x = engines.${eng}.mk { type = T; }; }) Ts ++ [
                { x = if wrapped then [ { } ] else { }; }
              ];
            };
            x = if wrapped then builtins.head r.config.x else r.config.x;
            element = if wrapped then r.options.x.type.nestedTypes.elemType else r.options.x.type;
            out = {
              inherit (x) l;
              genRecord = element ? carries;
            };
            tried = builtins.tryEval (builtins.deepSeq out out);
          in
          if tried.success then tried.value else "REFUSED";
        table =
          twin:
          let
            other = if twin then twinSide else genSide;
          in
          builtins.listToAttrs (
            builtins.concatMap
              (
                eng:
                builtins.concatMap
                  (
                    wrap:
                    builtins.concatMap
                      (
                        k:
                        let
                          w = wrap == "listOf";
                          a = if w then np.types.listOf nixpkgsSide.${k} else nixpkgsSide.${k};
                          b = if w then (if twin then np.types.listOf else t.listOf) other.${k} else other.${k};
                        in
                        [
                          {
                            name = "${eng}-${wrap}-${k}-o12";
                            value = read eng w [
                              a
                              b
                            ];
                          }
                          {
                            name = "${eng}-${wrap}-${k}-o21";
                            value = read eng w [
                              b
                              a
                            ];
                          }
                        ]
                      )
                      [
                        "sub"
                        "tree"
                        "args"
                        "clash"
                      ]
                  )
                  [
                    "bare"
                    "listOf"
                  ]
              )
              [
                "np"
                "gm"
              ]
          );
        # Both engines list the LATER declaration's modules first in `l` (the union is authored, as
        # nixpkgs builds it), so the literal does not depend on the engine.
        served = _: o: {
          l =
            if o == "o12" then
              [
                "gen-listed"
                "np-listed"
              ]
            else
              [
                "np-listed"
                "gen-listed"
              ];
          genRecord = false;
        };
        expected = builtins.listToAttrs (
          builtins.concatMap
            (
              eng:
              builtins.concatMap
                (
                  wrap:
                  builtins.concatMap
                    (
                      k:
                      map
                        (o: {
                          name = "${eng}-${wrap}-${k}-${o}";
                          value = if k == "clash" then "REFUSED" else served eng o;
                        })
                        [
                          "o12"
                          "o21"
                        ]
                    )
                    [
                      "sub"
                      "tree"
                      "args"
                      "clash"
                    ]
                )
                [
                  "bare"
                  "listOf"
                ]
            )
            [
              "np"
              "gm"
            ]
        );
      in
      {
        expr = {
          mixed = table false;
          ref = table true;
        };
        expected = {
          mixed = expected;
          ref = expected;
        };
      };

    # z75vj: a redeclared nesting option's module set is the AUTHORED concatenation of every
    # declaration's own set, as nixpkgs' `fixupOptionType` rebuilds it, whatever kinds the declarations
    # are (nixpkgs submodule / tree, gen submodule / tree) and under any container. `l` reads the
    # merged list, so the module-union order is observable. `expected` is the SAME table under
    # `lib.evalModules` over the SAME declared types, live, so there is no literal to drift. Rows:
    # every ordering of 2-3 declarations (bare / `listOf` / `nullOr` over submodule and tree), the
    # nixpkgs-only containers (`attrsOf`, `lazyAttrsOf`, `functionTo`), four declarations, five
    # order-observable value shapes, and `deferredModuleWith`. A mixed `attrsOf` pair is refused by
    # both engines, so it has no row; `live` fails if any row is refused in the reference.
    test-redeclared-nesting-modules-union-in-authored-order =
      let
        nt = np.types;
        npDecl = tag: {
          options.l = np.mkOption { type = nt.listOf nt.str; };
          config.l = [ "n${tag}" ];
        };
        # a gen module cannot declare `l` beside a nixpkgs one that does, so only the first one does
        genDecl =
          tag:
          {
            config.l = [ "g${tag}" ];
          }
          // (
            if tag == "A" then
              {
                options.l = mkOption { type = t.listOf t.str; };
              }
            else
              { }
          );
        build = {
          N = {
            sub = tag: nt.submodule [ (npDecl tag) ];
            tree = tag: (np.evalModules { modules = [ (npDecl tag) ]; }).type;
          };
          G = {
            sub = tag: t.submodule [ (genDecl tag) ];
            tree = tag: (evalModuleTree { } [ (genDecl tag) ]).type;
          };
        };
        wrap =
          w: v: T:
          if w == "bare" then
            T
          else if v == "N" then
            nt.${w} T
          else
            t.${w} T;
        def = {
          bare = { };
          listOf = [ { } ];
          nullOr = { };
          attrsOf = {
            k = { };
          };
          lazyAttrsOf = {
            k = { };
          };
          functionTo = _: { };
        };
        pick = {
          bare = x: x;
          listOf = builtins.head;
          nullOr = x: x;
          attrsOf = x: x.k;
          lazyAttrsOf = x: x.k;
          functionTo = x: x 0;
        };
        engines = {
          np = {
            ev = np.evalModules;
            mk = np.mkOption;
          };
          gm = {
            ev = evalRequest;
            mk = mkOption;
          };
        };
        settle =
          v:
          let
            r = builtins.tryEval (builtins.deepSeq v v);
          in
          if r.success then r.value else "REFUSED";
        decls =
          vs:
          np.imap0 (i: v: {
            inherit v;
            tag = builtins.elemAt [ "A" "B" "C" "D" ] i;
          }) vs;
        perms =
          l:
          if l == [ ] then
            [ [ ] ]
          else
            builtins.concatMap (x: map (p: [ x ] ++ p) (perms (builtins.filter (y: y != x) l))) l;
        twoOrders = ds: [
          ds
          (np.lists.reverseList ds)
        ];
        sets = {
          NN = [
            "N"
            "N"
          ];
          NG = [
            "N"
            "G"
          ];
          GG = [
            "G"
            "G"
          ];
          NNN = [
            "N"
            "N"
            "N"
          ];
          NNG = [
            "N"
            "N"
            "G"
          ];
          NGG = [
            "N"
            "G"
            "G"
          ];
          GGG = [
            "G"
            "G"
            "G"
          ];
        };
        nm = ds: builtins.concatStringsSep "-" (map (d: "${d.v}${d.tag}") ds);
        # one option `x` declared by `Ts` in order; a nesting option's list `l` is read through `pickFn`
        run =
          eng: w: Ts: pickFn:
          let
            r = engines.${eng}.ev {
              modules = map (T: { options.x = engines.${eng}.mk { type = T; }; }) Ts ++ [ { x = def.${w}; } ];
            };
          in
          settle (pickFn r.config.x);
        listRows =
          eng:
          builtins.listToAttrs (
            builtins.concatLists (
              map (
                row:
                map (ds: {
                  name = "${row.w}/${row.k}/${nm ds}";
                  value = run eng row.w (map (d: wrap row.w d.v (build.${d.v}.${row.k} d.tag)) ds) (
                    x: (pick.${row.w} x).l
                  );
                }) (row.ord (decls sets.${row.s}))
              ) rows
            )
          );
        rows =
          builtins.concatMap
            (
              w:
              builtins.concatMap
                (
                  k:
                  map (s: {
                    inherit w k s;
                    ord = perms;
                  }) (builtins.attrNames sets)
                )
                [
                  "sub"
                  "tree"
                ]
            )
            [
              "bare"
              "listOf"
              "nullOr"
            ]
          ++
            builtins.concatMap
              (
                k:
                map
                  (s: {
                    w = "attrsOf";
                    inherit k s;
                    ord = perms;
                  })
                  [
                    "NN"
                    "NNN"
                  ]
              )
              [
                "sub"
                "tree"
              ]
          ++
            builtins.concatMap
              (
                w:
                map
                  (s: {
                    inherit w s;
                    k = "sub";
                    ord = twoOrders;
                  })
                  [
                    "NN"
                    "NNN"
                  ]
              )
              [
                "lazyAttrsOf"
                "functionTo"
              ];
        fourRows =
          eng:
          builtins.listToAttrs (
            map
              (ds: {
                name = "four/${nm ds}";
                value = run eng "bare" (map (d: build.${d.v}.sub d.tag) ds) (x: x.l);
              })
              (
                perms (decls [
                  "N"
                  "G"
                  "N"
                  "G"
                ])
              )
          );
        # the value shapes the union order reaches: A declares, B only defines
        shapeDecl.options = {
          l = np.mkOption {
            type = nt.listOf nt.str;
            default = [ ];
          };
          s = np.mkOption {
            type = nt.lines;
            default = "";
          };
          sep = np.mkOption {
            type = nt.separatedString ",";
            default = "";
          };
          o = np.mkOption {
            type = nt.listOf nt.str;
            default = [ ];
          };
          m = np.mkOption {
            type = nt.attrsOf (nt.listOf nt.str);
            default = { };
          };
        };
        shapeDefs = tag: {
          config = {
            l = [ tag ];
            s = tag;
            sep = tag;
            o = np.mkOrder 500 [ tag ];
            m.k = [ tag ];
          };
        };
        shapeTypes = {
          NN = [
            (nt.submodule [
              shapeDecl
              (shapeDefs "A")
            ])
            (nt.submodule [ (shapeDefs "B") ])
          ];
          NG = [
            (nt.submodule [
              shapeDecl
              (shapeDefs "A")
            ])
            (t.submodule [ (shapeDefs "B") ])
          ];
        };
        shapeRows =
          eng:
          builtins.listToAttrs (
            builtins.concatMap
              (
                s:
                builtins.concatMap
                  (
                    ord:
                    map
                      (f: {
                        name = "shape/${s}/${ord}/${f}";
                        value = run eng "bare" (
                          if ord == "AB" then shapeTypes.${s} else np.lists.reverseList shapeTypes.${s}
                        ) (x: x.${f});
                      })
                      [
                        "l"
                        "s"
                        "sep"
                        "o"
                        "m"
                      ]
                  )
                  [
                    "AB"
                    "BA"
                  ]
              )
              [
                "NN"
                "NG"
              ]
          );
        deferredRows =
          eng:
          let
            dm = tag: nt.deferredModuleWith { staticModules = [ { config.l = [ tag ]; } ]; };
            reader = {
              options.l = np.mkOption {
                type = nt.listOf nt.str;
                default = [ ];
              };
            };
            at = {
              AB = [
                "A"
                "B"
              ];
              BA = [
                "B"
                "A"
              ];
              ABC = [
                "A"
                "B"
                "C"
              ];
              CAB = [
                "C"
                "A"
                "B"
              ];
            };
          in
          builtins.listToAttrs (
            map (n: {
              name = "deferred/${n}";
              value = run eng "bare" (map dm at.${n}) (
                x:
                (np.evalModules {
                  modules = [
                    reader
                    x
                  ];
                }).config.l
              );
            }) (builtins.attrNames at)
          );
        table = eng: listRows eng // fourRows eng // shapeRows eng // deferredRows eng;
        reference = table "np";
      in
      {
        expr = {
          gm = table "gm";
          live = builtins.all (v: v != "REFUSED") (builtins.attrValues reference);
          rows = builtins.length (builtins.attrNames reference);
        };
        expected = {
          gm = reference;
          live = true;
          rows = 252;
        };
      };
    # A WRAPPER over a nesting type keeps its own layer through the rebuild. The wrapper is built as
    # gen-schema's `refined` is: a `//` copy of a submodule with a layer of its own (`__wrapped`), a
    # relation joining the bases and re-wrapping, and a `substSubModules` re-wrapping the base's
    # rebuild. The copy carries the base's `substructure`, whose rebuild is the base's alone, so the
    # import takes the copy's own `substSubModules` (nixpkgs' `fixupOptionType` calls the outer
    # type's). `kept` reads the layer on the merged option type, `l` the union order; the `np` arm is
    # the same types mounted in `lib.evalModules`, which rebuilds through the exported protocol.
    test-redeclared-wrapper-over-nesting-keeps-its-layer =
      let
        wrapped =
          base:
          let
            self = t.mkOptionType (
              builtins.removeAttrs base [
                "functor"
                "typeMerge"
                "__mint"
                "__okAt"
                "__payload"
                "__sealed"
                "__typeSelf"
              ]
              // {
                __wrapped = base;
                typeMerge =
                  f:
                  if f.type ? __wrapped then
                    (
                      let
                        j = base.typeMerge f.type.__wrapped.functor;
                      in
                      if j == null then null else wrapped j
                    )
                  else
                    null;
                functor = {
                  name = "wrapped";
                  type = self;
                  payload = null;
                  binOp = _: _: null;
                };
                substSubModules =
                  m:
                  let
                    r = base.substSubModules m;
                  in
                  if r == null then null else wrapped r;
              }
            );
          in
          self;
        decl = {
          A = {
            options.l = mkOption { type = t.listOf t.str; };
            config.l = [ "A" ];
          };
          B.config.l = [ "B" ];
        };
        run =
          ev: mk: order:
          let
            r = ev {
              modules = map (k: { options.x = mk { type = wrapped (t.submodule [ decl.${k} ]); }; }) order ++ [
                { x = { }; }
              ];
            };
          in
          {
            kept = r.options.x.type ? __wrapped;
            inherit (r.config.x) l;
          };
        both = ev: mk: {
          AB = run ev mk [
            "A"
            "B"
          ];
          BA = run ev mk [
            "B"
            "A"
          ];
        };
      in
      {
        expr = {
          gm = both evalRequest mkOption;
          np = both np.evalModules np.mkOption;
        };
        expected =
          let
            rows = {
              AB = {
                kept = true;
                l = [
                  "B"
                  "A"
                ];
              };
              BA = {
                kept = true;
                l = [
                  "A"
                  "B"
                ];
              };
            };
          in
          {
            gm = rows;
            np = rows;
          };
      };
    # The same wrapper stating its rebuild in the OTHER copied field: `substructure.rebuild`, the
    # gen vocabulary, with the base's exported `substSubModules` carried along stale. The import
    # tells the two copies apart by the witness the export publishes beside `substSubModules`
    # (`_substSubModulesWitness`): here the field still holds it, so the copy's `substructure`
    # decides and the layer is kept, in both engines and under a single declaration.
    test-copy-stating-its-rebuild-as-substructure-keeps-its-layer =
      let
        wrapped =
          base:
          let
            self = t.mkOptionType (
              builtins.removeAttrs base [
                "functor"
                "typeMerge"
                "__mint"
                "__okAt"
                "__payload"
                "__sealed"
                "__typeSelf"
              ]
              // {
                __wrapped = base;
                typeMerge =
                  f:
                  if f.type ? __wrapped then
                    (
                      let
                        j = base.typeMerge f.type.__wrapped.functor;
                      in
                      if j == null then null else wrapped j
                    )
                  else
                    null;
                functor = {
                  name = "wrapped";
                  type = self;
                  payload = null;
                  binOp = _: _: null;
                };
                substructure = base.substructure // {
                  rebuild =
                    m:
                    let
                      r = base.substructure.rebuild m;
                    in
                    if r == null then null else wrapped r;
                };
              }
            );
          in
          self;
        decl = {
          A = {
            options.l = mkOption { type = t.listOf t.str; };
            config.l = [ "A" ];
          };
          B.config.l = [ "B" ];
        };
        run =
          ev: mk: order:
          let
            r = ev {
              modules = map (k: { options.x = mk { type = wrapped (t.submodule [ decl.${k} ]); }; }) order ++ [
                { x = { }; }
              ];
            };
          in
          {
            kept = r.options.x.type ? __wrapped;
            inherit (r.config.x) l;
          };
        both = ev: mk: {
          A = run ev mk [ "A" ];
          AB = run ev mk [
            "A"
            "B"
          ];
          BA = run ev mk [
            "B"
            "A"
          ];
        };
      in
      {
        expr = {
          gm = both evalRequest mkOption;
          np = both np.evalModules np.mkOption;
        };
        expected =
          let
            rows = {
              A = {
                kept = true;
                l = [ "A" ];
              };
              AB = {
                kept = true;
                l = [
                  "B"
                  "A"
                ];
              };
              BA = {
                kept = true;
                l = [
                  "A"
                  "B"
                ];
              };
            };
          in
          {
            gm = rows;
            np = rows;
          };
      };

    # caxcw + khltw: ONE option declared by a nixpkgs container and the gen constructor whose
    # parameters embed in it under ANOTHER functor name (`attrsOf`/`lazyAttrsOf` in `attrsWith`,
    # `deferredModule` in `deferredModuleWith`) has nixpkgs' answer in both orders, under either
    # engine. `ref` is the same table with the gen side replaced by its nixpkgs twin, live. A foreign
    # `staticModules` survives the join (`static`), a non-default `placeholder` is joined by nixpkgs'
    # own rule (`ph`), and a `lazy` disagreement refuses in both orders as nixpkgs refuses it.
    test-mixed-functor-name-redeclaration-is-nixpkgs-answer =
      let
        base = {
          options.y = np.mkOption {
            type = np.types.int;
            default = 0;
          };
          options.z = np.mkOption {
            type = np.types.int;
            default = 0;
          };
        };
        stat = {
          z = 7;
        };
        rows = {
          attrs = {
            n = np.types.attrsOf np.types.int;
            g = t.attrsOf t.int;
            twin = np.types.attrsOf np.types.int;
            def.k = 1;
          };
          lazy = {
            n = np.types.lazyAttrsOf np.types.int;
            g = t.lazyAttrsOf t.int;
            twin = np.types.lazyAttrsOf np.types.int;
            def.k = 1;
          };
          ph = {
            n = np.types.attrsWith {
              elemType = np.types.int;
              placeholder = "host";
            };
            g = t.attrsOf t.int;
            twin = np.types.attrsOf np.types.int;
            def.k = 1;
          };
          lazyVsEager = {
            n = np.types.attrsOf np.types.int;
            g = t.lazyAttrsOf t.int;
            twin = np.types.lazyAttrsOf np.types.int;
            def.k = 1;
          };
          deferred = {
            n = np.types.deferredModule;
            g = t.deferredModule;
            twin = np.types.deferredModule;
            def.y = 5;
          };
          static = {
            n = np.types.deferredModuleWith { staticModules = [ stat ]; };
            g = t.deferredModule;
            twin = np.types.deferredModule;
            def.y = 5;
          };
        };
        engines = {
          np = {
            ev = np.evalModules;
            mk = np.mkOption;
          };
          gm = {
            ev = evalRequest;
            mk = mkOption;
          };
        };
        read =
          eng: def: Ts:
          let
            r = engines.${eng}.ev {
              modules = map (T: { options.x = engines.${eng}.mk { type = T; }; }) Ts ++ [ { x = def; } ];
            };
            v = r.config.x;
            out = {
              value =
                if v ? imports then
                  { inherit ((np.evalModules { modules = [ base ] ++ v.imports; }).config) y z; }
                else
                  v;
              functor = r.options.x.type.functor.name;
              genRecord = r.options.x.type ? typeMergeRel;
            };
            tried = builtins.tryEval (builtins.deepSeq out out);
          in
          if tried.success then tried.value else "REFUSED";
        table =
          twin:
          builtins.listToAttrs (
            builtins.concatMap (
              eng:
              builtins.concatMap (
                k:
                let
                  row = rows.${k};
                  b = if twin then row.twin else row.g;
                in
                [
                  {
                    name = "${eng}-${k}-o12";
                    value = read eng row.def [
                      row.n
                      b
                    ];
                  }
                  {
                    name = "${eng}-${k}-o21";
                    value = read eng row.def [
                      b
                      row.n
                    ];
                  }
                ]
              ) (builtins.attrNames rows)
            ) (builtins.attrNames engines)
          );
        answer = {
          attrs = {
            value.k = 1;
            functor = "attrsWith";
            genRecord = false;
          };
          lazy = answer.attrs;
          ph = answer.attrs;
          lazyVsEager = "REFUSED";
          deferred = {
            value = {
              y = 5;
              z = 0;
            };
            functor = "deferredModuleWith";
            genRecord = false;
          };
          static = answer.deferred // {
            value = {
              y = 5;
              z = 7;
            };
          };
        };
        expected = builtins.listToAttrs (
          builtins.concatMap (
            eng:
            builtins.concatMap (k: [
              {
                name = "${eng}-${k}-o12";
                value = answer.${k};
              }
              {
                name = "${eng}-${k}-o21";
                value = answer.${k};
              }
            ]) (builtins.attrNames rows)
          ) (builtins.attrNames engines)
        );
        # THE WITNESS: a wrapped element (`ints.u8`) beside gen's `int`. Where gen's relation decides
        # (nixpkgs' engine, nixpkgs' declaration first) the join renames past `u8' and refuses, as the
        # same pair under `listOf` refuses; nixpkgs' relation deciding alone serves, as it does there.
        # gen's engine refuses both orders, as it refuses the nixpkgs × nixpkgs twin.
        u8 = np.types.attrsOf np.types.ints.u8;
        g8 = t.attrsOf t.int;
      in
      {
        expr = {
          mixed = table false;
          ref = table true;
          witness = {
            np-o12 = read "np" { k = 300; } [
              u8
              g8
            ];
            np-o21 = read "np" { k = 300; } [
              g8
              u8
            ];
            gm-o12 = read "gm" { k = 300; } [
              u8
              g8
            ];
            gm-o21 = read "gm" { k = 300; } [
              g8
              u8
            ];
          };
        };
        expected = {
          mixed = expected;
          ref = expected;
          witness = {
            np-o12 = "REFUSED";
            np-o21 = answer.attrs // {
              value.k = 300;
            };
            gm-o12 = "REFUSED";
            gm-o21 = "REFUSED";
          };
        };
      };

    # THE PUBLISHED SURFACE of the embedded types, pinned directly: the functor name a foreign engine
    # keys a redeclaration on, and the payload keys its `binOp` reads. A leaf row with no parameters
    # publishes a NULL payload, and every embedded type keeps its own `name`. `listOf`, which embeds
    # nowhere, is the unchanged control.
    test-embedded-constructors-publish-the-richer-functor =
      let
        surface = ty: {
          inherit (ty.functor) name;
          payload = if ty.functor.payload == null then null else builtins.attrNames ty.functor.payload;
        };
      in
      {
        expr = {
          attrsOf = surface (t.attrsOf t.int);
          lazyAttrsOf = surface (t.lazyAttrsOf t.int);
          deferredModule = surface t.deferredModule;
          str = surface t.str;
          path = surface t.path;
          pathLike = surface t.pathLike;
          listOf = surface (t.listOf t.int);
          params = {
            attrsOf = { inherit ((t.attrsOf t.int).functor.payload) lazy placeholder; };
            lazyAttrsOf = { inherit ((t.lazyAttrsOf t.int).functor.payload) lazy placeholder; };
            deferredModule = t.deferredModule.functor.payload.staticModules;
            path = t.path.functor.payload;
            pathLike = t.pathLike.functor.payload;
          };
          names = {
            str = t.str.name;
            path = t.path.name;
            pathLike = t.pathLike.name;
          };
        };
        expected = {
          attrsOf = {
            name = "attrsWith";
            payload = [
              "elemType"
              "lazy"
              "placeholder"
            ];
          };
          lazyAttrsOf = {
            name = "attrsWith";
            payload = [
              "elemType"
              "lazy"
              "placeholder"
            ];
          };
          deferredModule = {
            name = "deferredModuleWith";
            payload = [ "staticModules" ];
          };
          str = {
            name = "str";
            payload = null;
          };
          path = {
            name = "path";
            payload = [
              "absolute"
              "inStore"
            ];
          };
          pathLike = {
            name = "path";
            payload = [
              "absolute"
              "inStore"
            ];
          };
          listOf = {
            name = "listOf";
            payload = [ "elemType" ];
          };
          params = {
            attrsOf = {
              lazy = false;
              placeholder = "name";
            };
            lazyAttrsOf = {
              lazy = true;
              placeholder = "name";
            };
            deferredModule = [ ];
            path = {
              absolute = true;
              inStore = null;
            };
            pathLike = {
              absolute = null;
              inStore = null;
            };
          };
          names = {
            str = "string";
            path = "path";
            pathLike = "pathLike";
          };
        };
      };

    # THE EMBEDDED `functor.type` IS TOTAL BY REFUSAL: handed a payload of the richer constructor at
    # parameters that are not this type's own, it refuses rather than rebuilding at its own and
    # dropping the caller's. Its own embedding rebuilds (the live control), for each constructor.
    test-embedded-functor-type-refuses-a-payload-off-its-embedding =
      let
        rebuilt =
          ty: p:
          let
            r = builtins.tryEval (builtins.deepSeq (ty.functor.type p).name (ty.functor.type p).name);
          in
          if r.success then r.value else "REFUSED";
        off = {
          elemType = t.int;
          lazy = true;
          placeholder = "x";
        };
      in
      {
        expr = {
          attrsOf = {
            own = rebuilt (t.attrsOf t.int) (t.attrsOf t.int).functor.payload;
            lazy = rebuilt (t.attrsOf t.int) (off // { placeholder = "name"; });
            placeholder = rebuilt (t.attrsOf t.int) (off // { lazy = false; });
            both = rebuilt (t.attrsOf t.int) off;
          };
          lazyAttrsOf = {
            own = rebuilt (t.lazyAttrsOf t.int) (t.lazyAttrsOf t.int).functor.payload;
            eager = rebuilt (t.lazyAttrsOf t.int) (
              off
              // {
                lazy = false;
                placeholder = "name";
              }
            );
            placeholder = rebuilt (t.lazyAttrsOf t.int) off;
          };
          deferredModule = {
            own = rebuilt t.deferredModule t.deferredModule.functor.payload;
            static = rebuilt t.deferredModule { staticModules = [ { z = 7; } ]; };
          };
        };
        expected = {
          attrsOf = {
            own = "attrsOf";
            lazy = "REFUSED";
            placeholder = "REFUSED";
            both = "REFUSED";
          };
          lazyAttrsOf = {
            own = "lazyAttrsOf";
            eager = "REFUSED";
            placeholder = "REFUSED";
          };
          deferredModule = {
            own = "deferredModule";
            static = "REFUSED";
          };
        };
      };

    # ── 1 · ROUTING ────────────────────────────────────────────────────────────────────────────
    # The whole table in one cell, so no row can pass while its neighbour is unread. The `algebra`
    # rows are the library's own `typeMerge`; the `routed` rows are the engine's declaration merge
    # over the SAME pairs. Row by row they agree, which is the claim: the declaration path does not
    # decide type compatibility, it asks. The two container rows carry the parameterised case —
    # same-named containers that refuse on their ELEMENTS.
    test-declaration-merge-routes-through-the-type-algebra = {
      expr = {
        algebra = {
          strVsStr = algebra t.str t.str;
          strVsInt = algebra t.str t.int;
          enumVsEnum = algebra (t.enum "e" [ "a" ]) (t.enum "e" [ "b" ]);
          structVsStruct = algebra (t.struct "s" { a = t.str; }) (t.struct "s" { a = t.int; });
          attrsOfStrVsStr = algebra (t.attrsOf t.str) (t.attrsOf t.str);
          attrsOfStrVsInt = algebra (t.attrsOf t.str) (t.attrsOf t.int);
        };
        routed = {
          strVsStr = routed t.str t.str;
          strVsInt = routed t.str t.int;
          enumVsEnum = routed (t.enum "e" [ "a" ]) (t.enum "e" [ "b" ]);
          structVsStruct = routed (t.struct "s" { a = t.str; }) (t.struct "s" { a = t.int; });
          attrsOfStrVsStr = routed (t.attrsOf t.str) (t.attrsOf t.str);
          attrsOfStrVsInt = routed (t.attrsOf t.str) (t.attrsOf t.int);
        };
        # CROSS-ENGINE CONTROL, same run, BOTH ARMS: nixpkgs' own `typeMerge` answers the mergeable
        # and the unmergeable pair the same way. Without it the rows above are consistent with a
        # protocol this library implements consistently and wrongly.
        nixpkgs = {
          strVsStr = algebra np.types.str np.types.str;
          strVsInt = algebra np.types.str np.types.int;
        };
      };
      expected = {
        algebra = {
          strVsStr = "MERGED:string";
          strVsInt = "NULL-REFUSE";
          enumVsEnum = "MERGED:e";
          structVsStruct = "NULL-REFUSE";
          attrsOfStrVsStr = "MERGED:attrsOf";
          attrsOfStrVsInt = "NULL-REFUSE";
        };
        routed = {
          strVsStr = "MERGED:string";
          strVsInt = "REFUSED";
          enumVsEnum = "MERGED:e";
          structVsStruct = "REFUSED";
          attrsOfStrVsStr = "MERGED:attrsOf";
          attrsOfStrVsInt = "REFUSED";
        };
        nixpkgs = {
          strVsStr = "MERGED:str";
          strVsInt = "NULL-REFUSE";
        };
      };
    };

    # ── 2 · DISCRIMINATION ─────────────────────────────────────────────────────────────────────
    # A mergeable redeclaration still EVALUATES, all the way to a value. The refusal cells prove
    # that something now throws; only this proves that it throws on the right inputs.
    test-mergeable-redeclaration-still-evaluates = {
      expr = (evalRequest shadowing).config.x;
      expected = "from-B";
    };
    # Two same-named `enum`s over different value sets merge to their ordered union (nixpkgs' `enum`
    # functor `binOp`), so a value from the SECOND declaration is admitted and one outside both is
    # refused. nixpkgs' `evalModules` over the same declarations is the reference arm. Three
    # declarations fold pairwise, so the third's value is admitted too.
    test-same-named-enum-redeclaration-unions =
      let
        enumsOf =
          mk: ty: sets: v:
          map (e: {
            options.x = mk { type = ty "e" e; };
          }) sets
          ++ [ { config.x = v; } ];
        gen = sets: v: builtins.tryEval (evalModuleTree { } (enumsOf mkOption t.enum sets v)).config.x;
        ref =
          sets: v:
          builtins.tryEval
            (np.evalModules { modules = enumsOf np.mkOption (_: np.types.enum) sets v; }).config.x;
        ab = [
          [ "a" ]
          [ "b" ]
        ];
      in
      {
        expr = {
          admitted = gen ab "b";
          outside = gen ab "c";
          three = gen (ab ++ [ [ "c" ] ]) "c";
          refAdmitted = ref ab "b";
          refOutside = ref ab "c";
        };
        expected = {
          admitted = {
            success = true;
            value = "b";
          };
          outside = {
            success = false;
            value = false;
          };
          three = {
            success = true;
            value = "c";
          };
          refAdmitted = {
            success = true;
            value = "b";
          };
          refOutside = {
            success = false;
            value = false;
          };
        };
      };
    # …and the layering shape reaches its `apply`, which is the pattern the ordered fold exists for.
    # (Its lint-side twin is `test-accept-apply-redeclare-is-not-type-merge`, ci/tests/lint.nix.)
    test-apply-layering-is-not-a-redeclaration = {
      expr = (evalRequest layering).config.x;
      expected = "from-A!";
    };

    # ── 3 · RECOVERABILITY ─────────────────────────────────────────────────────────────────────
    # The ordered fold blesses the later declaration; the earlier one stays reachable beside it,
    # with the file that declared it. Both halves are asserted together — a `losers` list whose
    # `winner` was not also checked would not show that the bias still happened.
    test-shadowed-declaration-stays-reachable = {
      expr =
        let
          decl = (evalRequest shadowing).options.x;
        in
        {
          winner = {
            inherit (decl) default description;
          };
          losers = map (o: {
            inherit (o) file;
            inherit (o.declaration) default description;
          }) decl.overridden;
        };
      expected = {
        winner = {
          default = "from-B";
          description = "desc-B";
        };
        losers = [
          {
            file = "a.nix";
            default = "from-A";
            description = "desc-A";
          }
        ];
      };
    };
    # Three declarations chain, oldest first, each attributed to its own file — the shape a `super`
    # chain has. A two-declaration cell alone cannot tell an accumulating record from one that keeps
    # only the immediately preceding declaration.
    test-shadow-chain-keeps-every-declaration-in-order = {
      expr =
        let
          decl =
            (evalModuleTree { } [
              {
                _file = "a.nix";
                options.x = mkOption {
                  type = t.str;
                  default = "A";
                };
              }
              {
                _file = "b.nix";
                options.x = mkOption {
                  type = t.str;
                  default = "B";
                };
              }
              {
                _file = "c.nix";
                options.x = mkOption {
                  type = t.str;
                  default = "C";
                };
              }
            ]).options.x;
        in
        {
          winner = decl.default;
          losers = map loserOf decl.overridden;
        };
      expected = {
        winner = "C";
        losers = [
          {
            file = "a.nix";
            default = "A";
          }
          {
            file = "b.nix";
            default = "B";
          }
        ];
      };
    };
    # ATTRIBUTION ACROSS A NON-SHADOWING DECLARATION — the shape that separates "which module
    # contributed the field being shadowed" from "which declaration of the option is this". `b.nix`
    # only ADDS a description, so it shadows nothing and records no entry of its own; `c.nix` then
    # restates that description, and the entry for it must name `b.nix`, which wrote it, and not
    # `a.nix`, which declared the option and never had a description at all. Counting entries rather
    # than declaring modules gets this wrong by exactly one module, and only here — the chain cell
    # above, where every merge shadows, cannot tell the two apart.
    test-attribution-follows-the-contributing-module-not-the-entry-count = {
      expr =
        let
          decl =
            (evalModuleTree { } [
              {
                _file = "a.nix";
                options.x = mkOption {
                  type = t.str;
                  default = "A";
                };
              }
              {
                _file = "b.nix";
                options.x = mkOption { description = "desc-from-B"; };
              }
              {
                _file = "c.nix";
                options.x = mkOption { description = "desc-from-C"; };
              }
              {
                _file = "d.nix";
                options.x = mkOption { default = "D"; };
              }
            ]).options.x;
        in
        {
          winner = {
            inherit (decl) default description;
          };
          losers = map (o: {
            inherit (o) file;
            inherit (o.declaration) default description;
          }) decl.overridden;
        };
      expected = {
        winner = {
          default = "D";
          description = "desc-from-C";
        };
        # Two entries, not three: `b.nix` shadowed nothing, so it contributes no entry — it appears
        # as the ATTRIBUTION of the entry `c.nix` created.
        losers = [
          {
            file = "b.nix";
            default = "A";
            description = "desc-from-B";
          }
          {
            file = "c.nix";
            default = "A";
            description = "desc-from-C";
          }
        ];
      };
    };
    # THE CARRIER'S OWN DISCRIMINATION, and a run without it is worth little: a record only carries
    # `overridden` where a declaration really was shadowed. The layering module restates nothing, so
    # its merged record is exactly what the plain field-union produced — asserted in the same cell
    # as the shadowing shape, which does carry it, so "absent" here is a decision and not a surface
    # that never populates.
    test-overridden-appears-only-where-a-field-was-shadowed = {
      expr = {
        layered = (evalRequest layering).options.x ? overridden;
        shadowed = (evalRequest shadowing).options.x ? overridden;
        # A single declaration is not a redeclaration.
        alone =
          (evalModuleTree { } [
            {
              _file = "a.nix";
              options.x = mkOption {
                type = t.str;
                default = "A";
              };
            }
          ]).options.x
            ? overridden;
      };
      expected = {
        layered = false;
        shadowed = true;
        alone = false;
      };
    };

    # f010k: THE DECLARATION GUARD FORCES THE SPINE, NEVER THE MERGED RECORD. A declared `type` is a
    # descriptor field, so the guard decides leaf or group per declaring module and merges no
    # redeclared leaf. Two observable consequences, each a cell; the control (a read that reaches
    # the clashing option still refuses with the type-merge text) is on `../tests-error.nix`.
    #
    # A `type` read from a `_module.args` argument is admitted however many modules declare the
    # option. Declared once it always was; declared twice the guard once refused it with the
    # stratification text, because forcing the merged type read the argument under the poisoned
    # declaration-stratum arguments.
    test-module-args-typed-option-declared-twice-is-admitted = {
      expr =
        (evalModuleTree { } [
          ({ ty, ... }: { options.p = mkOption { type = ty; }; })
          ({ ty, ... }: { options.p = mkOption { type = ty; }; })
          {
            config._module.args.ty = t.str;
            config.p = "v";
          }
        ]).config.p;
      expected = "v";
    };
    # A type clash on `p` is not on the read path of an unrelated option's descriptor: the answer
    # `declaredOptions` gives, and nixpkgs'.
    test-a-type-clash-leaves-an-unrelated-options-type-readable = {
      expr =
        (evalModuleTree { } [
          { options.p = mkOption { type = t.str; }; }
          { options.p = mkOption { type = t.int; }; }
          {
            options.q = mkOption {
              type = t.str;
              default = "x";
            };
          }
        ]).options.q.type.name;
      expected = "string";
    };
    # `overridden` in authored order when the LAST declaration shadows nothing: `p2` shadows `p1`'s
    # type, `p3` adds a field, `p4` shadows `p3`'s description and `p5` only adds `apply`. The list is
    # published at the last step, which here records no entry of its own.
    test-overridden-is-published-when-the-last-declaration-shadows-nothing = {
      expr =
        let
          decl =
            (evalModuleTree { } [
              {
                _file = "p1";
                options.p = mkOption {
                  type = t.str;
                  description = "a";
                };
              }
              {
                _file = "p2";
                options.p = mkOption { type = t.str; };
              }
              {
                _file = "p3";
                options.p = mkOption { example = "x"; };
              }
              {
                _file = "p4";
                options.p = mkOption { description = "b"; };
              }
              {
                _file = "p5";
                options.p = mkOption { apply = x: x; };
              }
            ]).options.p;
        in
        map (o: {
          inherit (o) file;
          description = o.declaration.description or null;
        }) decl.overridden;
      expected = [
        {
          file = "p1";
          description = "a";
        }
        {
          file = "p3";
          description = "a";
        }
      ];
    };
  };
}
