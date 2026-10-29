# TWO DECLARATIONS BOTH STATING `default`, `example`, `description` OR `apply` ARE REFUSED, as nixpkgs'
# `mergeOptionDecls` refuses them (`bothHave`), by PRESENCE and ahead of the type decision. Each cell reads
# gen-merge's engine over gen's types and nixpkgs' `lib.evalModules` over nixpkgs' types on the same
# declarations, through gen-merge's `mkOption`, nixpkgs' `lib.mkOption` and the raw `{ _type = "option"; }`
# form; the refusals' texts are `ci/tests-error.nix`, `bothhave-guard`. The controls are the shapes the guard
# must not reach: one declaration, a guarded field on one side only (gen-schema's ref-binding layering), the
# four fields spread one per declaration, one keyed module reached twice, and an unguarded field (`visible`),
# which both engines fold.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  lib = nixpkgsLib;
  try =
    v:
    let
      r = builtins.tryEval (builtins.deepSeq v v);
    in
    if r.success then r.value else "REFUSED";
  # `decls` are declaration records without their door or type: `{ file; fields; }`, `fields.type = true`
  # standing for the engine's `int`; `defs` the definitions of `deep`
  engines = {
    gen = {
      ev = ms: gm.evalModuleTree { } ms;
      int = gm.types.int;
      mk = gm.mkOption;
    };
    nixpkgs = {
      ev = ms: lib.evalModules { modules = ms; };
      int = lib.types.int;
      mk = lib.mkOption;
    };
  };
  doors = {
    # the engine's own `mkOption`
    gm = E: f: E.mk f;
    lp = _: f: lib.mkOption f;
    raw = _: f: f // { _type = "option"; };
  };
  modsOf =
    E: door: decls: defs:
    map (d: {
      _file = d.file;
      options.deep = doors.${door} E (
        builtins.removeAttrs d.fields [ "type" ]
        // (if d.fields.type or false then { type = E.int; } else { })
      );
    }) decls
    ++ map (v: { config.deep = v; }) defs;
  read =
    E: door: decls: defs:
    try (E.ev (modsOf E door decls defs)).config.deep;
  both = door: decls: defs: {
    gen = read engines.gen door decls defs;
    nixpkgs = read engines.nixpkgs door decls defs;
  };
  decl = file: fields: { inherit file fields; };
  refused = {
    gen = "REFUSED";
    nixpkgs = "REFUSED";
  };
  served = v: {
    gen = v;
    nixpkgs = v;
  };
  overDoors = f: {
    gm = f "gm";
    lp = f "lp";
    raw = f "raw";
  };
  # one keyed module reached twice through a submodule's module set unioned with itself
  keyedTwice =
    E: sub:
    let
      m = {
        key = "deep-module";
        options.deep = E.mk {
          type = E.int;
          default = 2;
        };
      };
      t = sub [ m ];
    in
    try
      (E.ev [
        {
          options.x = E.mk {
            type = t;
            default = { };
          };
        }
        { options.x = E.mk { type = t; }; }
      ]).config.x.deep;
in
{
  flake.tests.bothhave-guard = {
    test-two-declarations-stating-a-guarded-field-are-refused-in-both-engines = {
      expr = overDoors (door: {
        default =
          both door
            [
              (decl "dup-a.nix" {
                type = true;
                default = 2;
              })
              (decl "dup-b.nix" {
                type = true;
                default = 2;
              })
            ]
            [ ];
        description =
          both door
            [
              (decl "dup-a.nix" {
                type = true;
                description = "a";
              })
              (decl "dup-b.nix" {
                type = true;
                description = "b";
              })
            ]
            [ 1 ];
        example =
          both door
            [
              (decl "dup-a.nix" {
                type = true;
                example = 1;
              })
              (decl "dup-b.nix" {
                type = true;
                example = 2;
              })
            ]
            [ 1 ];
        apply =
          both door
            [
              (decl "dup-a.nix" {
                type = true;
                apply = x: x + 1;
              })
              (decl "dup-b.nix" { apply = x: x * 10; })
            ]
            [ 1 ];
        # `description = null` on both is still presence
        null =
          both door
            [
              (decl "dup-a.nix" {
                type = true;
                description = null;
              })
              (decl "dup-b.nix" {
                type = true;
                description = null;
              })
            ]
            [ 1 ];
      });
      expected = overDoors (_: {
        default = refused;
        description = refused;
        example = refused;
        apply = refused;
        null = refused;
      });
    };
    # N = 3 and 4, the colliding pair adjacent or not: `av` is the accumulation of every earlier declaration
    test-a-non-adjacent-pair-is-refused = {
      expr = overDoors (door: {
        k3 =
          both door
            [
              (decl "dup-a.nix" {
                type = true;
                default = 2;
              })
              (decl "dup-b.nix" { type = true; })
              (decl "dup-c.nix" { default = 3; })
            ]
            [ ];
        k3end =
          both door
            [
              (decl "dup-a.nix" { type = true; })
              (decl "dup-b.nix" { default = 2; })
              (decl "dup-c.nix" { default = 3; })
            ]
            [ ];
        k4 =
          both door
            [
              (decl "dup-a.nix" {
                type = true;
                default = 2;
              })
              (decl "dup-b.nix" { type = true; })
              (decl "dup-c.nix" { description = "c"; })
              (decl "dup-d.nix" { default = 4; })
            ]
            [ ];
      });
      expected = overDoors (_: {
        k3 = refused;
        k3end = refused;
        k4 = refused;
      });
    };
    test-the-shapes-the-guard-must-not-reach-are-served = {
      expr = overDoors (door: {
        one =
          both door
            [
              (decl "dup-a.nix" {
                type = true;
                default = 2;
              })
            ]
            [ ];
        # gen-schema's ref binding: `apply` on one side over a typed default, typed or untyped
        layer =
          both door
            [
              (decl "kind.nix" {
                type = true;
                default = 2;
              })
              (decl "bind.nix" { apply = x: x * 10; })
            ]
            [ ];
        layerTyped =
          both door
            [
              (decl "kind.nix" {
                type = true;
                default = 2;
                description = "k";
              })
              (decl "bind.nix" {
                type = true;
                apply = x: x * 10;
              })
            ]
            [ ];
        spread =
          both door
            [
              (decl "dup-a.nix" {
                type = true;
                default = 2;
              })
              (decl "dup-b.nix" { example = 7; })
              (decl "dup-c.nix" { description = "c"; })
              (decl "dup-d.nix" { apply = x: x * 10; })
            ]
            [ ];
      });
      expected = overDoors (_: {
        one = served 2;
        layer = served 20;
        layerTyped = served 20;
        spread = served 20;
      });
    };
    test-one-keyed-module-reached-twice-is-not-refused = {
      expr = {
        gen = keyedTwice engines.gen gm.types.submodule;
        nixpkgs = keyedTwice engines.nixpkgs lib.types.submodule;
      };
      expected = served 2;
    };
    # an unguarded field both declarations state is folded, not refused (`visible`)
    test-an-unguarded-field-on-both-is-served = {
      expr = overDoors (
        door:
        let
          v =
            E:
            try
              (E.ev (
                modsOf E door
                  [
                    (decl "dup-a.nix" {
                      type = true;
                      visible = false;
                    })
                    (decl "dup-b.nix" {
                      type = true;
                      visible = true;
                    })
                  ]
                  [ 1 ]
              )).config.deep;
        in
        {
          gen = v engines.gen;
          nixpkgs = v engines.nixpkgs;
        }
      );
      expected = overDoors (_: served 1);
    };
  };
}
