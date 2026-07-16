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
