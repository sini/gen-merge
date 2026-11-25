# THE PAIRED CONSTRUCTION (den-hoag-t5ndo 1b H1). `refusingSubmodulePaired stated keys args mods` returns
# `{ type; evaluate; }` from ONE construction: `type` is `(refusingSubmodule stated keys mods).withArgs args`,
# and `evaluate loc defs` is the exported merge's own threaded call with the child's whole result kept,
# `{ config; provenance; }`. These cells pin that the evaluator's `config` IS the typed merge's on every row
# (the drift guard: `evaluate` shares the threaded arm's site record and domain guard, and a restated copy that
# moves splits a row here), that no derived or edited value carries an evaluator, that the typed merge stays a
# plain function, and that provenance is served under a poisoned sibling. The evaluation count is the
# process plane's (`paired-eval`).
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  gt = gm.types;
  nt = nixpkgsLib.types;
  mods = [
    (
      { name, ... }:
      {
        options.a = gm.mkOption {
          type = gt.int;
          default = 0;
        };
        options.addr = gm.mkOption {
          type = gt.str;
          default = "x";
        };
        options.nm = gm.mkOption {
          type = gt.str;
          default = "n-" + name;
        };
        options.ls = gm.mkOption {
          type = gt.listOf gt.str;
          default = [ "base" ];
        };
        options.ff = gm.mkOption {
          type = gt.attrsOf gt.str;
          default = { };
        };
      }
    )
  ];
  other = [ { options.b = gm.mkOption { default = 7; }; } ];
  P = gm.refusingSubmodulePaired null [ "config" ] { } mods;
  Q = gm.refusingSubmodulePaired null [ "config" ] { } other;
  loc = [
    "users"
    "tux"
  ];
  try =
    e:
    let
      r = builtins.tryEval (builtins.deepSeq e e);
    in
    if r.success then r.value else "refused";
  rows = {
    plain = [
      {
        file = "d.nix";
        value.a = 1;
      }
    ];
    two = [
      {
        file = "d1.nix";
        value = {
          a = 1;
          ls = [ "x" ];
        };
      }
      {
        file = "d2.nix";
        value = {
          addr = "y";
          ls = [ "y" ];
        };
      }
    ];
    named = [
      {
        file = "d.nix";
        value.name = "other";
      }
    ];
    wrongType = [
      {
        file = "d.nix";
        value.a = "str";
      }
    ];
    forced = [
      {
        file = "d1.nix";
        value.a = nixpkgsLib.mkForce 3;
      }
      {
        file = "d2.nix";
        value.a = 4;
      }
    ];
    fn = [
      {
        file = "d.nix";
        value =
          { config, ... }:
          {
            addr = "f-" + config.nm;
          };
      }
    ];
    argName = [
      {
        file = "d.nix";
        value._module.args.name = "argn";
      }
    ];
    outOfDomain = [
      {
        file = "d.nix";
        value = 5;
      }
    ];
    undeclared = [
      {
        file = "d.nix";
        value.zz = 1;
      }
    ];
    empty = [ ];
  };
  isPair = v: builtins.isAttrs v && v ? evaluate;
in
{
  flake.tests.refusing-submodule-paired = {
    test-the-pair-and-its-result-have-their-stated-shape = {
      expr = {
        pair = builtins.attrNames P;
        result = builtins.attrNames (P.evaluate loc rows.plain);
      };
      expected = {
        pair = [
          "evaluate"
          "type"
        ];
        result = [
          "config"
          "provenance"
        ];
      };
    };
    # The drift guard: every row's `config` (or its refusal) is the typed merge's. `argName` is the row a
    # reconstruction over the public module evaluation serves where the typed merge refuses.
    test-the-evaluators-config-is-the-typed-merges-on-every-row = {
      expr = builtins.mapAttrs (
        _: defs: try (P.evaluate loc defs).config == try (P.type.merge loc defs)
      ) rows;
      expected = builtins.mapAttrs (_: _: true) rows;
    };
    # The guard's own control: the rows refuse and serve as stated, so the equality above is not two refusals
    # everywhere.
    test-the-rows-serve-and-refuse-as-stated = {
      expr = builtins.mapAttrs (_: defs: try (P.evaluate loc defs).config != "refused") rows;
      expected = {
        plain = true;
        two = true;
        named = false;
        wrongType = false;
        forced = true;
        fn = true;
        argName = false;
        outOfDomain = false;
        undeclared = false;
        empty = true;
      };
    };
    test-the-type-is-the-refusing-submodule-with-its-args = {
      expr = gt.typeEq P.type ((gm.refusingSubmodule null [ "config" ] mods).withArgs { });
      expected = true;
    };
    test-no-derived-or-edited-value-carries-an-evaluator = {
      expr = {
        withArgs = isPair (P.type.withArgs { });
        edited = isPair (P.type // { check = _: true; });
        genAttrsElem = isPair (gt.attrsOf P.type).nestedTypes.elemType;
        nixpkgsAttrsElem = isPair (nt.attrsOf P.type).nestedTypes.elemType;
        onTheType = P.type ? evaluate;
      };
      expected = {
        withArgs = false;
        edited = false;
        genAttrsElem = false;
        nixpkgsAttrsElem = false;
        onTheType = false;
      };
    };
    # Each pair evaluates its own construction: handed a definition both admit, P's evaluator serves P's options.
    test-each-pair-evaluates-its-own-construction = {
      expr =
        let
          c =
            (P.evaluate loc [
              {
                file = "d.nix";
                value = { };
              }
            ]).config;
          d = (Q.evaluate loc [ ]).config;
        in
        {
          pHasA = c ? a;
          pHasB = c ? b;
          qB = d.b;
          qHasA = d ? a;
        };
      expected = {
        pHasA = true;
        pHasB = false;
        qB = 7;
        qHasA = false;
      };
    };
    test-the-typed-merge-stays-a-plain-function = {
      expr = {
        isFunction = builtins.isFunction P.type.merge;
        functionArgs = builtins.functionArgs P.type.merge;
      };
      expected = {
        isFunction = true;
        functionArgs = { };
      };
    };
    # Q2 / G7: a poisoned declared sibling leaves the rest of the result lazy: `a`'s value and its provenance
    # are served, and only the poisoned option refuses.
    test-provenance-is-served-beside-a-poisoned-sibling = {
      expr =
        let
          r = P.evaluate loc [
            {
              file = "d.nix";
              value = {
                a = 1;
                addr = throw "POISON";
              };
            }
          ];
        in
        {
          a = r.config.a;
          aFiles = map (d: d.file) r.provenance.a.defs;
          addr = (builtins.tryEval r.config.addr).success;
        };
      expected = {
        a = 1;
        aFiles = [
          "<default>"
          "d.nix"
        ];
        addr = false;
      };
    };
  };
}
