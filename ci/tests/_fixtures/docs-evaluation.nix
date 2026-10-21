# A NESTING TYPE'S DOCUMENTATION EVALUATION, on three engines: nixpkgs' `evalModules` over nixpkgs' types (np, the
# reference), gen-merge's `evalModuleTree` over gen's types (gm), and nixpkgs' `evalModules` over gen's nesting types
# (bx, the export bridge). Read by `../docs-evaluation.nix`.
#
# nixpkgs evaluates a submodule for documentation (`getSubOptions`) over its module set with its
# `noCheckForDocsModule` appended. A type module reads, inside that evaluation, its `_module.check` (`chk`, and the
# option's value `chkOpt`) and its `moduleType.getSubModules` labels (`sm`), at three sites: the type's
# `getSubOptions` itself, the docs evaluation's own `moduleType` documented again (`sm2`/`chk2`) and the same through
# `attrsOf` (`smE`/`chkE`). Beside them the reads the docs module must leave alone: option names, `description`
# (also through `attrsOf`), `nestedTypes.freeformType`, `_freeformOptions` and the checked child's own reads. Five
# variants shape the type module: none (`plain`), an undeclared definition (`stray`), `_module.check = mkForce true`
# (`force`), a freeform type (`ff`), and `ff` beside `stray` (`ffStray`).
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

  safe =
    v:
    let
      r = tryEval (deepSeq v v);
    in
    if r.success then r.value else "<error>";
  label =
    m:
    if isFunction m then
      "<fn>"
    else if isAttrs m then
      concatStringsSep "|" (
        [ (m._file or "-") ]
        ++ (if m ? imports then [ "imports[${concatStringsSep ";" (map label m.imports)}]" ] else [ ])
        ++ (if m ? config then [ "config" ] else [ ])
      )
    else
      "path:${toString m}";

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
      typeMod =
        { config, moduleType, ... }:
        {
          _file = "type.nix";
          options = {
            chk = I.mkOption { default = config._module.check; };
            sm = I.mkOption { default = map label (moduleType.getSubModules or [ ]); };
            again = I.mkOption {
              type = moduleType;
              default = { };
            };
          };
        };
      strayMod = {
        _file = "stray.nix";
        config.bogus = 1;
      };
      forceMod = {
        _file = "force.nix";
        config._module.check = I.mkForce true;
      };
      ffMod = {
        _file = "ff.nix";
        freeformType = I.types.attrsOf I.types.int;
      };
      typeMods = [
        typeMod
      ]
      ++ {
        plain = [ ];
        stray = [ strayMod ];
        force = [ forceMod ];
        ff = [ ffMod ];
        ffStray = [
          ffMod
          strayMod
        ];
      }
      .${variant};
      subT =
        if a == "np" then
          np.types.submoduleWith {
            modules = typeMods;
            shorthandOnlyDefinesConfig = true;
          }
        else
          gm.types.submodule typeMods;
      r = outerEval [
        {
          _file = "decl.nix";
          options.sub = O.mkOption {
            type = subT;
            default = { };
          };
          options.subs = O.mkOption {
            type = O.types.attrsOf subT;
            default = { };
          };
        }
      ];
      T = r.options.sub.type;
      docs = T.getSubOptions [ "p" ];
      docs2 = docs.again.type.getSubOptions [ "q" ];
      docsE = r.options.subs.type.getSubOptions [ "s" ];
    in
    {
      sm = safe docs.sm.default;
      chk = safe docs.chk.default;
      chkOpt = safe docs._module.check.value;
      sm2 = safe docs2.sm.default;
      chk2 = safe docs2.chk.default;
      smE = safe docsE.sm.default;
      chkE = safe docsE.chk.default;
      names = safe (attrNames docs);
      desc = safe T.description;
      descE = safe r.options.subs.type.description;
      nested = safe (
        if T.nestedTypes ? freeformType then T.nestedTypes.freeformType.description else "none"
      );
      ffOpts = safe (attrNames (docs._freeformOptions or { }));
      child = safe r.config.sub.chk;
      childSm = safe r.config.sub.sm;
    };
  variants = [
    "plain"
    "stray"
    "force"
    "ff"
    "ffStray"
  ];
in
{
  table = builtins.listToAttrs (
    map (v: {
      name = v;
      value = builtins.listToAttrs (
        map
          (a: {
            name = a;
            value = cells a v;
          })
          [
            "np"
            "gm"
            "bx"
          ]
      );
    }) variants
  );
}
