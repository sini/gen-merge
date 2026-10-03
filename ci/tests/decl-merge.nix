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
  genMerge,
  nixpkgsLib,
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
          (evalModuleTree {
            modules = [
              {
                _file = "a.nix";
                options.x = mkOption { type = a; };
              }
              {
                _file = "b.nix";
                options.x = mkOption { type = b; };
              }
            ];
          }).options.x.type.name;
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
          gm = table evalModuleTree mkOption;
          ref = table np.evalModules np.mkOption;
          # the gen-native veto across a fold step it is not adjacent to by position
          gen-first-int-Fint-str = read evalModuleTree mkOption [ t.int Fint np.types.str ] n;
          # the one departure, by refusing: `Fx`'s relation answers `int` for `str`, which keeps
          # neither operand's name (nixpkgs answers `int`)
          renaming-int-str-Fx = read evalModuleTree mkOption [ np.types.int np.types.str Fx ] n;
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
          gm = table evalModuleTree;
          ref = table np.evalModules;
          ff-renaming-21 = read evalModuleTree [ Bf Ar ] "s";
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
          gm = table evalModuleTree mkOption;
          ref = table np.evalModules np.mkOption;
        };
        expected = {
          gm = expected;
          ref = expected;
        };
      };

    # zvidt: ONE option declared by a nixpkgs container and a gen container has ONE declared-type spine
    # whichever declaration comes first, under either engine: nixpkgs' own. The partner's relation
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
            ev = evalModuleTree;
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
          (if ty ? carries then "G" else "N")
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
          tree = (evalModuleTree { modules = [ genM ]; }).type;
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
            ev = evalModuleTree;
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
            tree = tag: (evalModuleTree { modules = [ (genDecl tag) ]; }).type;
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
            ev = evalModuleTree;
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
                "__id"
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
          gm = both evalModuleTree mkOption;
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
                "__id"
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
          gm = both evalModuleTree mkOption;
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
      expr = (evalModuleTree shadowing).config.x;
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
        gen =
          sets: v: builtins.tryEval (evalModuleTree { modules = enumsOf mkOption t.enum sets v; }).config.x;
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
      expr = (evalModuleTree layering).config.x;
      expected = "from-A!";
    };

    # ── 3 · RECOVERABILITY ─────────────────────────────────────────────────────────────────────
    # The ordered fold blesses the later declaration; the earlier one stays reachable beside it,
    # with the file that declared it. Both halves are asserted together — a `losers` list whose
    # `winner` was not also checked would not show that the bias still happened.
    test-shadowed-declaration-stays-reachable = {
      expr =
        let
          decl = (evalModuleTree shadowing).options.x;
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
            (evalModuleTree {
              modules = [
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
              ];
            }).options.x;
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
            (evalModuleTree {
              modules = [
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
              ];
            }).options.x;
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
        layered = (evalModuleTree layering).options.x ? overridden;
        shadowed = (evalModuleTree shadowing).options.x ? overridden;
        # A single declaration is not a redeclaration.
        alone =
          (evalModuleTree {
            modules = [
              {
                _file = "a.nix";
                options.x = mkOption {
                  type = t.str;
                  default = "A";
                };
              }
            ];
          }).options.x
            ? overridden;
      };
      expected = {
        layered = false;
        shadowed = true;
        alone = false;
      };
    };
  };
}
