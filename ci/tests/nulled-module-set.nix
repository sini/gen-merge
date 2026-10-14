# A COPY STATING `getSubModules = null` CONTRIBUTES NO MODULE SET (den-hoag-y4w78). nixpkgs reads a declaration's module
# set off its `getSubModules` alone, so a `//` copy nulling it, declared TWICE, leaves the option's submodule declaring
# nothing, and nixpkgs refuses the definition (``The option `x.a' does not exist``). Gen reads the statement too, not the
# `substructure` the copy carried from its base, at each reader that decides a declaration's contribution to its option:
# a door (`defineType`, `mkOptionType`), the fixup (`fixupModuleSets`), the spine (`spineModules`) and the join
# (`sameValue.kept`). Each cell reads gen's engine, nixpkgs' engine over the same records, and the all-nixpkgs twin
# (`gt.*` as `np.*`, the doors as identity) in the same cell; the copy declared ONCE, and BESIDE its plain twin, is
# served, as nixpkgs serves it. The refusal of a cycle through a nulled copy is pinned by name on the error plane
# (`tests-error.nix`, `cyclic-types`).
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  nl = nixpkgsLib;
  np = nl.types;
  run =
    eng: ts: w:
    let
      gt = if eng == "twin" then np else gm.types;
      mods =
        map (t: { options.x = (if eng == "gen" then gm else nl).mkOption { type = t gt eng; }; }) ts
        ++ [ { x = w { a = 1; }; } ];
      r =
        if eng == "gen" then
          (gm.evalModuleTree { } mods).config.x
        else
          (nl.evalModules { modules = mods; }).config.x;
      o = builtins.tryEval (builtins.deepSeq r (builtins.toJSON r));
    in
    if o.success then o.value else "REFUSED";
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
  classes = {
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
  plain = t: t;
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
    nl.mapAttrs' (n: c: {
      name = "test-${n}-declared-twice-is-refused-as-its-twin-refuses";
      value = {
        expr = engines [
          (c.t nulled)
          (c.t nulled)
        ] c.w;
        expected = nl.genAttrs [ "gen" "np" "twin" ] (_: "REFUSED");
      };
    }) classes
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
