# A COPY STATING `getSubModules = null` CONTRIBUTES NO MODULE SET OF ITS OWN (den-hoag-y4w78), AND A DECLARATION LIST
# STATING NONE MOUNTS THE SETS ITS COPIES CARRY (den-hoag-b9fl0). nixpkgs reads a declaration's module set off its
# `getSubModules` alone: `mergeOptionDecls` collects a declaration's set only where it is not `null`, and `fixupOptionType`
# rebuilds the merged type over the collected list, except where that list is empty (nixpkgs d17afff), where it keeps the
# merged type, the join of the copies' functors, which carries the union of their sets. So a nulled copy declared twice
# is served, and with distinct sets it mounts both; a declaration stating a set beside it mounts only the stated sets.
# Gen reads the statement too, not the `substructure` the copy carried from its base, at each reader that decides a
# declaration's contribution to its option: a door (`defineType`, `mkOptionType`), the fixup (`fixupModuleSets`), the
# spine (`spineModules`), the join (`sameValue.kept`) and a foreign record's mount over the fold's list
# (`homedRootFixed`). Each cell reads gen's engine, nixpkgs' engine over the same records, and the all-nixpkgs twin
# (`gt.*` as `np.*`, the doors as identity) in the same cell; the copy declared ONCE, and BESIDE its plain twin, is
# served, as nixpkgs serves it. The refusal of a cycle through a nulled copy is pinned by name on the error plane
# (`tests-error.nix`, `cyclic-types`).
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  nl = nixpkgsLib;
  np = nl.types;
  runV =
    v: eng: ts: w:
    let
      gt = if eng == "twin" then np else gm.types;
      mods =
        map (t: { options.x = (if eng == "gen" then gm else nl).mkOption { type = t gt eng; }; }) ts
        ++ [ { x = w v; } ];
      r =
        if eng == "gen" then
          (gm.evalModuleTree { } mods).config.x
        else
          (nl.evalModules { modules = mods; }).config.x;
      o = builtins.tryEval (builtins.deepSeq r (builtins.toJSON r));
    in
    if o.success then o.value else "REFUSED";
  run = runV { a = 1; };
  engines = ts: w: nl.genAttrs [ "gen" "np" "twin" ] (eng: run eng ts w);
  sub =
    gt: eng:
    let
      mk = if eng == "gen" then gm.mkOption else nl.mkOption;
    in
    gt.submodule {
      key = "nulled-module-set-sub-${eng}";
      options.a = mk {
        type = gt.int;
        default = 0;
      };
      options.b = mk {
        type = gt.int;
        default = 0;
      };
    };
  # the same module set as a FOREIGN record: nixpkgs' own `submodule`, whatever the engine
  subF =
    gt: eng:
    np.submodule {
      key = "nulled-module-set-foreign-sub";
      options.a = nl.mkOption {
        type = np.int;
        default = 0;
      };
      options.b = nl.mkOption {
        type = np.int;
        default = 0;
      };
    };
  # declaration i's own module set, declaring `a<i>` only, for the union law; `E` states an empty set
  subD =
    foreign: i: ch: gt: eng:
    let
      K = if foreign then np else gt;
      mk = if foreign || eng != "gen" then nl.mkOption else gm.mkOption;
    in
    if ch == "E" then
      K.submodule [ ]
    else
      K.submodule {
        key = "nulled-module-set-sub-${if foreign then "f" else eng}-${toString i}";
        options."a${toString i}" = mk {
          type = K.int;
          default = 0;
        };
      };
  nulled = t: t // { getSubModules = null; };
  door =
    eng: d:
    if eng == "twin" then
      (t: t)
    else
      {
        def = gm.types.defineType;
        mkO = gm.mkOptionType;
      }
      .${d};
  # each class's repro (den-hoag-58ja3 scout v1 `repro1.nix`), as a function of whether its copy is nulled
  classesOver = sub: {
    # a door re-derives the module set from the copy's carried `substructure`
    N-D = {
      t =
        c: gt: eng:
        np.attrsOf (door eng "def" (c (sub gt eng)));
      w = v: { k = v; };
    };
    # the fixup reads the carried `substructure`
    N-S = {
      t =
        c: gt: eng:
        c (sub gt eng);
      w = v: v;
    };
    # the fixup and the spine
    N-SP = {
      t =
        c: gt: eng:
        gt.attrsOf (c (sub gt eng));
      w = v: { k = v; };
    };
    # the spine walks past a gen container stating `null` to its element's set
    N-P = {
      t =
        c: gt: eng:
        gt.attrsOf (c (gt.nullOr (sub gt eng)));
      w = v: { k = v; };
    };
    # the door and the fixup
    N-DS = {
      t =
        c: gt: eng:
        np.attrsOf (door eng "mkO" (c (sub gt eng)));
      w = v: { k = v; };
    };
    # the join: two declarations of one value merge to the first operand, keeping its stated `null`
    N-C = {
      t =
        c: gt: eng:
        door eng "mkO" (c (np.nullOr (sub gt eng)));
      w = v: v;
    };
  };
  classes = classesOver sub;
  foreignClasses = classesOver subF;
  chars = str: builtins.genList (i: builtins.substring i 1 str) (builtins.stringLength str);
  # the union law over a declaration sequence (N a nulled copy, P plain, E an empty stated set), defining nothing, so
  # the served keys are the mounted set
  unionAt =
    foreign: seq:
    nl.genAttrs [ "gen" "np" "twin" ] (
      eng:
      runV { } eng (nl.imap0 (
        i: ch: gt: eng:
        (if ch == "N" then nulled else plain) (subD foreign i ch gt eng)
      ) (chars seq)) (v: v)
    );
  plain = t: t;
  # declaration i's own keyed set for the order law: it defines `l = [ "a<i>" ]`, and set 0 also declares `l`, so the
  # served list is the mounted modules in mount order
  subO =
    i: ch: gt: eng:
    let
      mk = if eng == "gen" then gm.mkOption else nl.mkOption;
    in
    if ch == "E" then
      gt.submodule [ ]
    else
      gt.submodule (
        {
          key = "nulled-module-set-order-${eng}-${toString i}";
          config.l = [ "a${toString i}" ];
        }
        // (
          if i == 0 then
            {
              options.l = mk {
                type = gt.listOf gt.str;
                default = [ ];
              };
            }
          else
            { }
        )
      );
  # where the declarations' copies sit: at the root or under gen `attrsOf`, raw or through a door
  orderShapes = {
    root = {
      t =
        _: _: s:
        s;
      w = { };
      r = x: x.l;
    };
    root-door = {
      t =
        eng: _: s:
        door eng "def" s;
      w = { };
      r = x: x.l;
    };
    attrs = {
      t =
        _: gt: s:
        gt.attrsOf s;
      w.k = { };
      r = x: x.k.l;
    };
    attrs-door = {
      t =
        eng: gt: s:
        gt.attrsOf (door eng "def" s);
      w.k = { };
      r = x: x.k.l;
    };
  };
  orderAt =
    shape: seq:
    nl.genAttrs [ "gen" "np" "twin" ] (
      eng:
      let
        gt = if eng == "twin" then np else gm.types;
        mods =
          nl.imap0 (i: ch: {
            options.x = (if eng == "gen" then gm else nl).mkOption {
              type = shape.t eng gt ((if ch == "N" then nulled else plain) (subO i ch gt eng));
            };
          }) (chars seq)
          ++ [ { x = shape.w; } ];
        r =
          shape.r
            (if eng == "gen" then gm.evalModuleTree { } mods else nl.evalModules { modules = mods; }).config.x;
        o = builtins.tryEval (builtins.deepSeq r (builtins.toJSON r));
      in
      if o.success then o.value else "REFUSED"
    );
  # what nixpkgs serves the definition `{ a = 1; }` through the class's shape
  servedAt =
    w:
    nl.genAttrs [ "gen" "np" "twin" ] (
      _:
      builtins.toJSON (w {
        a = 1;
        b = 0;
      })
    );
in
{
  flake.tests.nulled-module-set =
    # declared two, three and four times, gen's and a foreign module set: served as the twin serves (den-hoag-b9fl0)
    nl.foldl' (a: b: a // b) { } (
      nl.mapCartesianProduct
        (
          { k, src }:
          nl.mapAttrs' (n: c: {
            name = "test-${src.name}${n}-declared-${toString k}-times-is-served-as-its-twin-serves";
            value = {
              expr = engines (builtins.genList (_: c.t nulled) k) c.w;
              expected = servedAt c.w;
            };
          }) src.classes
        )
        {
          k = [
            2
            3
            4
          ];
          src = [
            {
              name = "";
              inherit classes;
            }
            {
              name = "foreign-";
              classes = foreignClasses;
            }
          ];
        }
    )
    # the union law, hand-derived: no declaration states a module set, so the copies' carried sets are mounted, in
    # union; a declaration stating one mounts only the stated sets (non-monotone: NNP loses a0 and a1); an empty
    # stated set states none
    // nl.foldl' (a: b: a // b) { } (
      map
        (
          foreign:
          nl.mapAttrs'
            (seq: keys: {
              name = "test-union-${if foreign then "foreign-" else ""}${seq}-mounts-${
                if keys == [ ] then "nothing" else nl.concatStrings keys
              }";
              value = {
                expr = unionAt foreign seq;
                expected = nl.genAttrs [ "gen" "np" "twin" ] (_: builtins.toJSON (nl.genAttrs keys (_: 0)));
              };
            })
            {
              NN = [
                "a0"
                "a1"
              ];
              NNN = [
                "a0"
                "a1"
                "a2"
              ];
              NNNN = [
                "a0"
                "a1"
                "a2"
                "a3"
              ];
              NNE = [
                "a0"
                "a1"
              ];
              EN = [ "a1" ];
              NNP = [ "a2" ];
              PNN = [ "a0" ];
              NPN = [ "a1" ];
            }
        )
        [
          false
          true
        ]
    )
    # THE ORDER LAW: the kept join is nixpkgs' `binOp`, `lhs.modules ++ rhs.modules`, so a declaration list stating no
    # module set mounts the copies' sets EARLIER-FIRST, and a list built across them comes out in declaration order. The
    # rebuild over stated sets (PP, PPP) stays later-first, as nixpkgs' `mergeOptionDecls` collects them; both orders
    # are pinned, so the join's operand order is read on both paths
    // nl.foldl' (a: b: a // b) { } (
      nl.mapAttrsToList (
        sn: shape:
        nl.mapAttrs'
          (seq: l: {
            name = "test-order-${sn}-${seq}-mounts-${nl.concatStrings l}";
            value = {
              expr = orderAt shape seq;
              expected = nl.genAttrs [ "gen" "np" "twin" ] (_: builtins.toJSON l);
            };
          })
          {
            NN = [
              "a0"
              "a1"
            ];
            NNN = [
              "a0"
              "a1"
              "a2"
            ];
            NNNN = [
              "a0"
              "a1"
              "a2"
              "a3"
            ];
            NNE = [
              "a0"
              "a1"
            ];
            NEN = [
              "a0"
              "a2"
            ];
            PP = [
              "a1"
              "a0"
            ];
            PPP = [
              "a2"
              "a1"
              "a0"
            ];
          }
      ) orderShapes
    )
    // nl.mapAttrs' (n: c: {
      name = "test-control-${n}-declared-once-is-served-as-its-twin-serves-it";
      value = {
        expr = engines [ (c.t nulled) ] c.w;
        expected = servedAt c.w;
      };
    }) classes
    // nl.mapAttrs' (n: c: {
      name = "test-control-${n}-beside-its-plain-twin-is-served-as-its-twin-serves-it";
      value = {
        expr = {
          copyFirst = engines [
            (c.t nulled)
            (c.t plain)
          ] c.w;
          plainFirst = engines [
            (c.t plain)
            (c.t nulled)
          ] c.w;
        };
        expected = {
          copyFirst = servedAt c.w;
          plainFirst = servedAt c.w;
        };
      };
    }) classes
    # THE CHECK ORACLE over the served class: a nulled copy of a CHECKED module set declared two to four times. nixpkgs'
    # twin keeps the join of the copies' functors, which drops the declared check, so it serves the rejected value
    # (nixpkgs' own value is silent there); gen's engine owes every declared check, so it serves the accepted value as the
    # twin does and refuses the rejected one by name (ADR-0039, the serve half's exception and Not covered: a foreign
    # `addCheck` over a submodule is enforced in gen's engine). An ad-hoc override of a FOREIGN set stating no module set
    # is refused by name whatever its value (`adHocChecked`, as nixpkgs refuses it declared once): the twin serves it only
    # because its join erased the override
    // nl.foldl' (a: b: a // b) { } (
      nl.mapCartesianProduct
        (
          { k, c }:
          {
            "test-checked-${c.name}-declared-${toString k}-times-serves-what-its-checks-accept-and-refuses-the-rest" =
              {
                expr = nl.genAttrs [ "ok" "bad" ] (
                  d:
                  run "gen"
                    (builtins.genList (
                      _: gt: eng:
                      c.copy (c.sub gt eng)
                    ) k)
                    (_: {
                      a = if d == "ok" then 1 else 2;
                    })
                );
                expected = {
                  ok =
                    if c.name == "foreign-override" then
                      "REFUSED"
                    else
                      builtins.toJSON {
                        a = 1;
                        b = 0;
                      };
                  bad = "REFUSED";
                };
              };
          }
        )
        {
          k = [
            2
            3
            4
          ];
          c =
            let
              p = v: !(builtins.isAttrs v) || !(v ? a) || !(builtins.isInt v.a) || v.a != 2;
            in
            [
              {
                name = "add-check";
                inherit sub;
                copy = s: np.addCheck s p // { getSubModules = null; };
              }
              {
                name = "foreign-add-check";
                sub = subF;
                copy = s: np.addCheck s p // { getSubModules = null; };
              }
              {
                name = "override";
                inherit sub;
                copy =
                  s:
                  s
                  // {
                    check = v: s.check v && p v;
                    getSubModules = null;
                  };
              }
              {
                name = "foreign-override";
                sub = subF;
                copy =
                  s:
                  s
                  // {
                    check = v: s.check v && p v;
                    getSubModules = null;
                  };
              }
              {
                name = "verify";
                inherit sub;
                copy =
                  s:
                  s
                  // {
                    verify = v: if p v then null else "rejected";
                    getSubModules = null;
                  };
              }
            ];
        }
    )
    // {
      # a door's return over a type whose element is the door's own return reads its module set lazily: forcing it at the
      # door ends in infinite recursion (den-hoag-y4w78 P1)
      test-control-a-self-referential-type-through-define-type-reads-its-module-set =
        let
          s = gm.types.defineType (gm.types.listOf s);
          v = [
            [ ]
            [ [ ] ]
          ];
          r =
            (gm.evalModuleTree { } [
              { options.x = gm.mkOption { type = s; }; }
              { x = v; }
            ]).config.x;
        in
        {
          expr = builtins.tryEval (builtins.deepSeq r r);
          expected = {
            success = true;
            value = v;
          };
        };
    };
}
