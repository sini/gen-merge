# A WHOLE `_module.args` DEFINITION UNDER A PROPERTY, AS NIXPKGS' OPTION RANKS IT (den-hoag-b44rx). nixpkgs runs
# its override pass over each module's whole definition of `_module.args`, the engine's own among them
# (`internalModule`'s `{ extendModules; moduleType; }`, a nested evaluation's position `name`), all at the
# default priority, before `lazyAttrsOf` merges keys. One construction per form × position × read, on two
# engines: nixpkgs' `evalModules` over nixpkgs' types (`np`) and gen-merge's `evalModuleTree` over gen's (`gm`).
# The value cells are `../module-args-whole-set.nix`, the refusals `../../tests-error.nix`.
{ gm, np }:
let
  engine =
    eng:
    let
      L = if eng == "gm" then gm else np;
    in
    {
      inherit L;
      ev =
        mods:
        if eng == "gm" then
          gm.evalModuleTree { specialArgs.sa = "S"; } mods
        else
          np.evalModules {
            modules = mods;
            specialArgs.sa = "S";
          };
    };
  show =
    v:
    if builtins.isFunction v then
      "<fn>"
    else if builtins.isAttrs v && v._type or null == "option-type" then
      "<type>"
    else if builtins.isAttrs v then
      "<attrs>"
    else
      v;
  formsOf = L: {
    # controls: no whole-set property, or one at the default
    none = [ ];
    plain = [
      {
        _module.args = {
          q = 1;
        };
      }
    ];
    o100 = [ { _module.args = L.mkOverride 100 { q = 1; }; } ];
    keyF = [ { _module.args.q = L.mkForce 1; } ];
    fpxsd = [ { _module.args.name = L.mkForce "forced"; } ];
    # above the default: only the forced set stays
    force = [ { _module.args = L.mkForce { q = 1; }; } ];
    o10 = [ { _module.args = L.mkOverride 10 { q = 1; }; } ];
    o99 = [ { _module.args = L.mkOverride 99 { q = 1; }; } ];
    ift = [ { _module.args = L.mkIf true (L.mkForce { q = 1; }); } ];
    mmerge = [
      {
        _module.args = L.mkMerge [
          (L.mkForce { q = 1; })
          { r = 2; }
        ];
      }
    ];
    two = [
      { _module.args = L.mkForce { q = 1; }; }
      { _module.args = L.mkForce { r = 2; }; }
    ];
    outer = [
      {
        _module = L.mkForce {
          args = {
            q = 1;
          };
        };
      }
    ];
    nameF = [
      {
        _module.args = L.mkForce {
          name = "f";
          q = 1;
        };
      }
    ];
    # below the default: the engine's own definitions outrank the set
    dflt = [ { _module.args = L.mkDefault { q = 1; }; } ];
    odflt = [ { _module.args = L.mkOptionDefault { q = 1; }; } ];
    # a condition at the default stays per key: its keys need no condition forced
    iff = [ { _module.args = L.mkIf false { q = 1; }; } ];
  };
  o = L: default: { options.r = L.mkOption { inherit default; }; };
  readersOf = L: {
    keys = { config, ... }: o L (builtins.attrNames config._module.args);
    nameVal = { config, ... }: o L (show (config._module.args.name or "<none>"));
    name = { name, ... }: o L (show name);
    extendModules = { extendModules, ... }: o L (show extendModules);
    moduleType = { moduleType, ... }: o L (show moduleType);
    q = { q, ... }: o L (show q);
    r = { r, ... }: o L (show r);
    zz = { zz, ... }: o L (show zz);
    base =
      {
        config,
        options,
        specialArgs,
        _class,
        _prefix,
        ...
      }:
      o L (
        builtins.seq config (builtins.seq options (builtins.seq specialArgs (builtins.seq _prefix "ok")))
      );
    sa = { sa, ... }: o L (show sa);
  };
  at =
    eng: pos: mods:
    let
      inherit (engine eng) L ev;
    in
    if pos == "root" then
      (ev mods).config.r
    else if pos == "sub" then
      (ev [
        {
          options.s = L.mkOption {
            type = L.types.submodule { imports = mods; };
            default = { };
          };
        }
      ]).config.s.r
    else
      (ev [
        {
          options.a = L.mkOption { type = L.types.attrsOf (L.types.submodule { imports = mods; }); };
          config.a.x = { };
        }
      ]).config.a.x.r;
in
{
  forms = builtins.attrNames (formsOf np);
  positions = [
    "root"
    "sub"
    "aof"
  ];
  readsAt = pos: builtins.filter (r: pos == "root" || r != "sa") (builtins.attrNames (readersOf np));
  # the arguments nixpkgs leaves undefined, so its read aborts (`attribute 'x' missing`); every other read serves
  undefinedAt =
    form: pos:
    let
      outranked = [
        "extendModules"
        "moduleType"
        "name"
      ];
      at' = {
        force = outranked ++ [ "r" ];
        o10 = outranked ++ [ "r" ];
        o99 = outranked ++ [ "r" ];
        ift = outranked ++ [ "r" ];
        mmerge = outranked ++ [ "r" ];
        outer = outranked ++ [ "r" ];
        two = outranked;
        nameF = [
          "extendModules"
          "moduleType"
          "r"
        ];
        dflt = [
          "q"
          "r"
        ];
        odflt = [
          "q"
          "r"
        ];
        iff = [
          "q"
          "r"
        ];
        none = [
          "q"
          "r"
        ];
        fpxsd = [
          "q"
          "r"
        ];
        plain = [ "r" ];
        o100 = [ "r" ];
        keyF = [ "r" ];
      };
    in
    # a root has no position `name`; a form stating one defines it
    [ "zz" ]
    ++ at'.${form}
    ++ (
      if
        pos == "root"
        && !(builtins.elem "name" at'.${form})
        && !(builtins.elem form [
          "nameF"
          "fpxsd"
        ])
      then
        [ "name" ]
      else
        [ ]
    );
  cell =
    eng: form: pos: read:
    let
      inherit (engine eng) L;
    in
    at eng pos ((formsOf L).${form} ++ [ (readersOf L).${read} ]);

  # A whole-set condition that reads an argument (`flag` is defined from `p`): the condition is forced only where
  # an override above the default sits under it, so `mkIf config.flag { q }` reaches its fixpoint (`flag` true,
  # `q` 1) and `mkIf config.flag (mkForce { q })`, which has none, recurses as nixpkgs' does. `ctl` reads no argument.
  conditional =
    eng: case: read:
    let
      inherit (engine eng) L ev;
      r = ev [
        (
          { config, ... }:
          {
            _module.args =
              if case == "forced" then
                L.mkIf config.flag (L.mkForce { q = 1; })
              else
                L.mkIf config.flag { q = 1; };
          }
        )
        {
          options.flag = L.mkOption {
            type = L.types.bool;
            default = false;
          };
        }
        (if case == "ctl" then { config.flag = true; } else ({ p, ... }: { config.flag = p; }))
        { _module.args.p = true; }
        {
          options.out = L.mkOption {
            type = L.types.raw;
            default = null;
          };
        }
        ({ q, ... }: { config.out = q; })
      ];
    in
    if read == "flag" then r.config.flag else r.config.out;

  # A positioned child that re-declares `options._module.args` reads its `name` from the merged set itself.
  declaring =
    forced:
    (gm.evalModuleTree { } [
      {
        options.s = gm.mkOption {
          type = gm.types.submodule {
            imports = [
              { options._module.args = gm.mkOption { type = gm.types.lazyAttrsOf gm.types.raw; }; }
              (if forced then { _module.args = gm.mkForce { q = 1; }; } else { _module.args.q = 1; })
              ({ name, ... }: { options.n = gm.mkOption { default = name; }; })
            ];
          };
          default = { };
        };
      }
    ]).config.s.n;
}
