# A REFUSED EVALUATION'S GEN-ONLY RESULT ATTRIBUTES, and warm evaluations over a refused prior. Read by the value
# cells (`../genonly-attrs-gated.nix`) and the error plane (`../../tests-error.nix`, `genonly-attrs-gated`).
#
# Three refusal sources, each with a twin that serves: `s1` an undeclared definition under the default check, `s2` a
# freeform evaluation whose own `_module.check` throws, `idm` a warm re-compose whose edit moves a minted identity
# (`../warm.nix`'s `idOf` / `flatBase` / `plantLive`). `w3*` are warm evaluations over a prior refused by a refusal
# the edit removes, beside their cold evaluations: `w3a` the orphan, declared by the edit; `w3b` a throwing check at
# default priority, overridden; `w3c` and `w3e` the same with an uncatchable `abort` and an evaluation error; `w3d` a
# clean prior. A read is `"served"` when it deep-forces, `"refused"` on a catchable throw, and `"<absent>"` when the
# attribute is missing, tested with `?` first.
{ gm }:
let
  inherit (gm) evalModuleTree mkOption mkDefault;
  t = gm.types;
  inherit (builtins) tryEval deepSeq toJSON;
  state = v: if (tryEval (deepSeq v true)).success then "served" else "refused";

  decl = {
    options.a = mkOption {
      type = t.int;
      default = 1;
    };
  };
  defA = {
    config.a = 5;
  };
  stray = {
    config.bogus = 7;
  };
  declBogus = {
    options.bogus = mkOption { type = t.int; };
  };

  s1Modules = [
    decl
    defA
    stray
  ];
  s1 = evalModuleTree { } s1Modules;
  s1clean = evalModuleTree { } [
    decl
    defA
  ];
  ffModules =
    refuse:
    [
      {
        freeformType = t.attrsOf t.int;
        options.a = mkOption {
          type = t.int;
          default = 1;
        };
      }
      {
        config.a = 5;
        config.free = 7;
      }
    ]
    ++ (if refuse then [ { config._module.check = throw "khk2v-plant-check"; } ] else [ ]);
  s2 = evalModuleTree { } (ffModules true);
  s2clean = evalModuleTree { } (ffModules false);

  idOf =
    kind:
    (
      { config, options, ... }:
      {
        options.id_hash = mkOption { type = t.str; };
        config.id_hash =
          let
            keys = builtins.filter (
              k:
              k != "id_hash"
              && builtins.elem (options.${k}.type.name or "") [
                "str"
                "string"
              ]
              && !(options.${k}.internal or false)
            ) (builtins.attrNames options);
          in
          "${kind}:" + builtins.hashString "sha256" (builtins.toJSON (map (k: config.${k}) keys));
      }
    );
  flatBase = [
    (idOf "host")
    {
      options.name = mkOption { type = t.str; };
      options.role = mkOption { type = t.str; };
    }
    {
      _file = "flat-base";
      config.name = "igloo";
      config.role = "web";
    }
  ];
  plantLive = [
    {
      _file = "plant";
      options.grommet = mkOption {
        type = t.str;
        default = "plain";
      };
    }
  ];
  idm = evalModuleTree {
    warmFrom = evalModuleTree { } flatBase;
    editedModules = plantLive;
  } (flatBase ++ plantLive);
  idmClean = evalModuleTree { } (flatBase ++ plantLive);

  checkOverridden = [ { config._module.check = true; } ];
  warmCell =
    base: edited:
    let
      w = evalModuleTree {
        warmFrom = evalModuleTree { } base;
        editedModules = edited;
      } (base ++ edited);
      c = evalModuleTree { } (base ++ edited);
    in
    {
      inherit (w.warmDecision) mode reason;
      config = toJSON w.config == toJSON c.config;
      provenance = toJSON w.provenance == toJSON c.provenance;
    };
  hasNext = r: r.warmDecision ? next;
in
{
  # The attributes carrying a definition value, per refused evaluation: read through its refusal.
  gated = {
    s1 = {
      "optionDefs.values" = state s1.optionDefs.values;
      "optionDefs.topDefs" = state s1.optionDefs.topDefs;
      "optionDefs.realized.unmatched" = state s1.optionDefs.realized.unmatched;
      freeformConfig = state s1.freeformConfig;
      "warmDecision.uncheckedConfig" = state s1.warmDecision.uncheckedConfig;
    };
    s2 = {
      "optionDefs.values" = state s2.optionDefs.values;
      freeformConfig = state s2.freeformConfig;
      "warmDecision.uncheckedConfig" = state s2.warmDecision.uncheckedConfig;
    };
    idm = {
      "optionDefs.values" = state idm.optionDefs.values;
      freeformConfig = state idm.freeformConfig;
      "warmDecision.uncheckedConfig" = state idm.warmDecision.uncheckedConfig;
    };
  };
  # The refusal each source carries, the control on the reads above.
  config = {
    s1 = state s1.config;
    s2 = state s2.config;
    idm = state idm.config;
  };
  # The twins serve the same reads, and their values are the evaluation's own.
  clean = {
    s1 = {
      "optionDefs.values" = state s1clean.optionDefs.values;
      "optionDefs.topDefs" = state s1clean.optionDefs.topDefs;
      "warmDecision.uncheckedConfig.a" = s1clean.warmDecision.uncheckedConfig.a;
      "config.a" = s1clean.config.a;
    };
    s2 = {
      "freeformConfig" = s2clean.freeformConfig;
      "warmDecision.uncheckedConfig.free" = s2clean.warmDecision.uncheckedConfig.free;
      "config.free" = s2clean.config.free;
    };
    idm = {
      "optionDefs.values" = state idmClean.optionDefs.values;
      "warmDecision.uncheckedConfig.name" = idmClean.warmDecision.uncheckedConfig.name;
    };
  };
  # The metadata, stated as served past the refusal (README: the provenance and deprecation records, and
  # `undeclared`).
  stated = builtins.mapAttrs (_: r: {
    provenance = state r.provenance;
    undeclared = state r.undeclared;
    deprecations = state r.deprecations;
    freeformProv = state r.freeformProv;
    "warmDecision.mode" = state r.warmDecision.mode;
    "warmDecision.strict" = state r.warmDecision.strict;
    "warmDecision.options" = state (builtins.attrNames r.warmDecision.options);
  }) { inherit s1 s2 idm; };
  warm = {
    w3a = warmCell s1Modules [ declBogus ];
    w3b = warmCell [
      decl
      defA
      { config._module.check = mkDefault (throw "khk2v-plant-check"); }
    ] checkOverridden;
    w3c = warmCell [
      decl
      defA
      { config._module.check = mkDefault (abort "khk2v-plant-abort"); }
    ] checkOverridden;
    w3d =
      warmCell
        [
          decl
          defA
          declBogus
          { config.bogus = 7; }
        ]
        [ { config.a = gm.mkForce 9; } ];
    w3e = warmCell [
      decl
      defA
      { config._module.check = mkDefault (1 + "x"); }
    ] checkOverridden;
  };
  # The continuation over the refused `s1`'s own modules, nothing edited: an evaluation refusing as `s1` does.
  next =
    if !(hasNext s1) then
      "<absent>"
    else
      let
        r = s1.warmDecision.next { editedModules = [ ]; } s1Modules;
      in
      {
        config = state r.config;
        "optionDefs.values" = state r.optionDefs.values;
        "optionDefs.topDefs" = state r.optionDefs.topDefs;
        freeformConfig = state r.freeformConfig;
        "warmDecision.uncheckedConfig" = state r.warmDecision.uncheckedConfig;
      };
  # After an edit declaring the stray: the continuation is the door warm-started from `s1`, and cold.
  nextEdited =
    if !(hasNext s1) then
      "<absent>"
    else
      let
        o = {
          editedModules = [ declBogus ];
        };
        m = s1Modules ++ [ declBogus ];
        n = s1.warmDecision.next o m;
        d = evalModuleTree (o // { warmFrom = s1; }) m;
        c = evalModuleTree { } m;
      in
      {
        mode = n.warmDecision.mode;
        doorConfig = toJSON n.config == toJSON d.config;
        doorProvenance = toJSON n.provenance == toJSON d.provenance;
        coldConfig = toJSON n.config == toJSON c.config;
        coldProvenance = toJSON n.provenance == toJSON c.provenance;
      };
  # The continuation refuses what the door refuses: the internal `root` and a misspelt option.
  doorArms =
    let
      m = [
        decl
        defA
      ];
      arm = f: state (f m).config;
    in
    {
      door = {
        root = arm (evalModuleTree {
          root = "/x";
        });
        misspelt = arm (evalModuleTree {
          chekc = false;
        });
      };
      next =
        if !(hasNext s1clean) then
          "<absent>"
        else
          {
            root = arm (s1clean.warmDecision.next { root = "/x"; });
            misspelt = arm (s1clean.warmDecision.next { chekc = false; });
          };
    };
  # For the error plane: the uncaught reads.
  raw = {
    s1Values = builtins.deepSeq s1.optionDefs.values null;
    s2Free = builtins.deepSeq s2.freeformConfig null;
    idmValues = builtins.deepSeq idm.optionDefs.values null;
    nextRoot = builtins.seq (s1clean.warmDecision.next { root = "/x"; }) null;
    nextMisspelt = builtins.seq (s1clean.warmDecision.next { chekc = false; }) null;
  };
}
