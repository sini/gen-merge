# THE PUBLISHED MODULE SET, PER SITE THAT PLACES A NAME MODULE (den-hoag-1k5mi), on three engines: nixpkgs'
# `evalModules` over nixpkgs' types (np, the reference), gen-merge's `evalModuleTree` over gen's types (gm), and
# nixpkgs' `evalModules` over gen's nesting types (bx, the export bridge). Read by the value cells
# (`../published-module-set.nix`) and the refusal cells (`../../tests-error.nix`, `published-module-set`).
#
# A submodule's type module reads, inside its own evaluation, its `name`, its `_module.args` record and its
# `moduleType.getSubModules` labels, at six sites: the child itself, its `moduleType` reused as an option type
# (`again`), `moduleType.emptyValue`, `extendModules` with and without `prefix`, and the type's
# `getSubOptions` (`docs`). Six variants place `name` differently: none (`plain`), a function module stating it
# (`namePlain`), shorthand definitions with no name, a plain one or an `mkDefault` one, and a second type module
# stating it at `mkOptionDefault` (`tmOD`).
{ gm, np }:
let
  inherit (builtins)
    tryEval
    deepSeq
    isAttrs
    isFunction
    attrNames
    concatStringsSep
    ;

  show =
    v:
    if isFunction v then
      "<fn>"
    else if isAttrs v && v._type or null == "option-type" then
      "type"
    else if isAttrs v && v._type or null == "override" then
      "o${toString v.priority}:${toString (show v.content)}"
    else if isAttrs v then
      "{${concatStringsSep "," (attrNames v)}}"
    else
      toString v;
  # the `_module.args` record, one string per definition: file, then each key=value
  rec_ =
    o:
    map (
      d: "${d.file}|${concatStringsSep "," (map (k: "${k}=${show d.value.${k}}") (attrNames d.value))}"
    ) o.definitionsWithLocations;
  label =
    m:
    if isFunction m then
      "<fn>"
    else if isAttrs m then
      concatStringsSep "|" (
        [ (m._file or "-") ]
        ++ (
          if m ? _module && m._module ? args then
            [
              "args:${
                concatStringsSep "," (map (k: "${k}=${show m._module.args.${k}}") (attrNames m._module.args))
              }"
            ]
          else
            [ ]
        )
        ++ (if m ? imports then [ "imports[${concatStringsSep ";" (map label m.imports)}]" ] else [ ])
        ++ (if m ? config then [ "config" ] else [ ])
      )
    else
      "path:${toString m}";
  safe =
    v:
    let
      r = tryEval (deepSeq v v);
    in
    if r.success then r.value else "<error>";

  # arm: np | gm | bx; the outer evaluation and the types/mkOption the type module declares with
  arm =
    a:
    if a == "np" then
      {
        O = np;
        I = np;
      }
    else if a == "gm" then
      {
        O = gm;
        I = gm;
      }
    else
      {
        O = np;
        I = gm;
      };

  cells =
    a: variant:
    let
      inherit (arm a) O I;
      outerEval =
        mods: if a == "gm" then gm.evalModuleTree { } mods else np.evalModules { modules = mods; };
      mkOption = I.mkOption;
      reads = c: {
        nm = c.nm;
        rcd = c.rcd;
        sm = c.sm;
      };
      typeMod =
        {
          options,
          config,
          moduleType,
          extendModules,
          name,
          ...
        }:
        {
          _file = "type.nix";
          options = {
            rcd = mkOption { default = rec_ options._module.args; };
            nm = mkOption { default = name; };
            sm = mkOption { default = map label (moduleType.getSubModules or [ ]); };
            again = mkOption {
              type = moduleType;
              default = { };
            };
            extP = mkOption {
              default =
                reads
                  (extendModules {
                    prefix = [ "elsewhere" ];
                    modules = [ { _file = "ext.nix"; } ];
                  }).config;
            };
            extN = mkOption {
              default = reads (extendModules { modules = [ { _file = "ext.nix"; } ]; }).config;
            };
            emptyV = mkOption { default = reads moduleType.emptyValue.value; };
          };
        };
      # tmOD: a second type module defining `name` at mkOptionDefault, the placeholder's priority
      nameMod = {
        _file = "tn.nix";
        _module.args.name = I.mkOptionDefault "tn";
      };
      typeMods = [ typeMod ] ++ (if variant == "tmOD" then [ nameMod ] else [ ]);
      subT =
        if a == "gm" || a == "bx" then
          gm.types.submodule typeMods
        else
          np.types.submoduleWith {
            modules = typeMods;
            shorthandOnlyDefinesConfig = true;
          };
      shArgs =
        if variant == "sh" || variant == "tmOD" then
          { foo = "d"; }
        else if variant == "shNamePlain" then
          {
            foo = "d";
            name = "def-name";
          }
        else if variant == "shNameDefault" then
          {
            foo = "d";
            name = O.mkDefault "def-name";
          }
        else
          null;
      fnDef =
        { ... }:
        {
          _file = "def.nix";
          _module.args = {
            foo = "d";
          }
          // (if variant == "namePlain" then { name = "def-name"; } else { });
        };
      r = outerEval [
        {
          _file = "decl.nix";
          options.sub = O.mkOption {
            type = subT;
            default = { };
          };
        }
        {
          _file = "cfg.nix";
          config.sub = if shArgs != null then { _module.args = shArgs; } else fnDef;
        }
      ];
      c = r.config.sub;
      docs = r.options.sub.type.getSubOptions [ "p" ];
    in
    {
      child = {
        nm = safe c.nm;
        rcd = safe c.rcd;
        sm = safe c.sm;
      };
      again = {
        nm = safe c.again.nm;
        rcd = safe c.again.rcd;
        sm = safe c.again.sm;
      };
      extP = builtins.mapAttrs (_: safe) c.extP;
      extN = builtins.mapAttrs (_: safe) c.extN;
      emptyV = builtins.mapAttrs (_: safe) c.emptyV;
      docs = {
        nm = safe docs.nm.default;
        rcd = safe docs.rcd.default;
        sm = safe docs.sm.default;
      };
      raw = {
        childNm = c.nm;
        againNm = c.again.nm;
        docsNm = docs.nm.default;
        emptyNm = c.emptyV.nm;
        extPNm = c.extP.nm;
      };
    };
  variants = [
    "plain"
    "namePlain"
    "sh"
    "shNamePlain"
    "shNameDefault"
    "tmOD"
  ];
  strip = x: removeAttrs x [ "raw" ];
in
{
  table = builtins.listToAttrs (
    map (v: {
      name = v;
      value = builtins.listToAttrs (
        map
          (a: {
            name = a;
            value = strip (cells a v);
          })
          [
            "np"
            "gm"
            "bx"
          ]
      );
    }) variants
  );
  raw =
    a: v: k:
    (cells a v).raw.${k};
  # The uniqueness refusal where the winners straddle the groups the record orders: a type module
  # stating a plain `name` (`tm.nix`) beside a definition stating one (`cfg.nix`) and the position.
  # `located`: one declaration, so the type's modules are located (gen: a root). `redecl`: the option
  # declared twice, the second adding the type module, so gen holds no root for the group.
  edge =
    a: shape:
    let
      inherit (arm a) O I;
      outerEval =
        mods: if a == "gm" then gm.evalModuleTree { } mods else np.evalModules { modules = mods; };
      T = if a == "np" then np.types else gm.types;
      tm = {
        _file = "tm.nix";
        _module.args.name = "tm";
      };
      base0 = {
        _file = "base.nix";
        options.nm = I.mkOption { default = "-"; };
      };
      sub =
        ms:
        if a == "np" then
          np.types.submoduleWith {
            modules = ms;
            shorthandOnlyDefinesConfig = true;
          }
        else
          T.submodule ms;
      decls =
        if shape == "located" then
          [
            {
              _file = "decl.nix";
              options.s = O.mkOption {
                type = sub [
                  base0
                  tm
                ];
              };
            }
          ]
        else
          [
            {
              _file = "decl.nix";
              options.s = O.mkOption { type = sub [ base0 ]; };
            }
            {
              _file = "decl2.nix";
              options.s = O.mkOption { type = sub [ tm ]; };
            }
          ];
    in
    (outerEval (
      decls
      ++ [
        {
          _file = "cfg.nix";
          config.s = { name, ... }: {
            _module.args.name = "def-name";
            nm = name;
          };
        }
      ]
    )).config.s.nm;
}
