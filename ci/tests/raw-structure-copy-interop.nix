# A raw post-completion `//` copy that overrides a completed record's `nests` or a container's `split` is an
# interoperability limit, not a parity row (ADR-0039 guidance; den-ag-design
# specs/2026-11-19-gen-merge-raw-structure-copy-interop-note.md). gen's engine reads the copy's own structural field; nixpkgs'
# engine reads the exported protocol (`getSubModules` / `substSubModules`), whose closures see the base. No
# cross-engine equivalence is promised for that shape, so these cells pin which field each engine reads, never that
# the two agree on it. Honest constructions, the recommended rebuild among them, agree. Refusals are symmetric: a
# throw in the field one engine reads refuses there and is unseen by the other.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  t = gm.types;
  inherit (builtins) deepSeq tryEval mapAttrs;
  kind =
    aspects:
    t.submodule {
      options.aspects = gm.mkOption {
        type = t.listOf t.str;
        default = [ ];
      };
      options.flag = gm.mkOption {
        type = t.bool;
        default = false;
      };
      config = { inherit aspects; };
    };
  # the base and the departing operand
  E0 = kind (gm.mkDefault [ "k" ]);
  EF = kind (gm.mkForce [ "t" ]);
  defs = {
    s0.aspects = [ "loom" ];
    s1.flag = true;
    s2.aspects = gm.mkForce [ "nf" ];
  };
  run =
    eng: type:
    let
      m = {
        options.x = gm.mkOption { inherit type; };
        config.x = defs;
      };
      cfg =
        if eng == "gm" then
          (gm.evalModuleTree { } [ m ]).config
        else
          (nixpkgsLib.evalModules { modules = [ m ]; }).config;
      v = mapAttrs (_: s: s.aspects) cfg.x;
      r = tryEval (deepSeq v v);
    in
    if r.success then r.value else "REFUSED";
  both = type: {
    gm = run "gm" type;
    np = run "np" type;
  };
  base = {
    s0 = [ "loom" ];
    s1 = [ "k" ];
    s2 = [ "nf" ];
  };
  departed = {
    s0 = [ "t" ];
    s1 = [ "t" ];
    s2 = [
      "t"
      "nf"
    ];
  };
  boom = throw "raw-structure-copy-interop: this field was read";
in
{
  flake.tests.raw-structure-copy-interop = {
    # honest constructions agree; `rebuilt` is the recommended surface, the constructor of the fold the record
    # states (`attrsOf`) built over the departing operand. RED where either engine's read of an honest record moves
    test-honest-constructions-agree-across-engines = {
      expr = {
        attrs = both (t.attrsOf E0);
        rebuilt = both (t.attrsOf EF);
      };
      expected = {
        attrs = {
          gm = base;
          np = base;
        };
        rebuilt = {
          gm = departed;
          np = departed;
        };
      };
    };
    # the raw copies: gen's engine reads the copy's `nests` (N) and `split` (S); nixpkgs' engine does not see them
    # and serves the base. RED where gen's engine reads the completed base instead (the scout's mNv / mSkw), or
    # where nixpkgs' engine starts reading the overlay
    test-raw-copies-each-engine-reads-its-own-field = {
      expr = {
        nests = both (
          t.attrsOf (
            E0
            // {
              nests = E0.nests // {
                inherit (EF.nests) modules;
              };
            }
          )
        );
        split = both (t.attrsOf E0 // { inherit (t.attrsOf EF) split; });
      };
      expected = {
        nests = {
          gm = departed;
          np = base;
        };
        split = {
          gm = departed;
          np = base;
        };
      };
    };
    # symmetric refusals: a throw in `nests` / `split` refuses only in gen's engine; a throw in `getSubModules`
    # refuses only in nixpkgs'. RED where either engine reads, or stops reading, the other's field
    test-refusals-are-symmetric = {
      expr = {
        nests = both (t.attrsOf (E0 // { nests = boom; }));
        split = both (t.attrsOf E0 // { split = boom; });
        nestsGetSubModules = both (t.attrsOf (E0 // { getSubModules = boom; }));
        splitGetSubModules = both (t.attrsOf E0 // { getSubModules = boom; });
      };
      expected = {
        nests = {
          gm = "REFUSED";
          np = base;
        };
        split = {
          gm = "REFUSED";
          np = base;
        };
        nestsGetSubModules = {
          gm = base;
          np = "REFUSED";
        };
        splitGetSubModules = {
          gm = base;
          np = "REFUSED";
        };
      };
    };
  };
}
