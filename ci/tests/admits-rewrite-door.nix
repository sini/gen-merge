# An `admits` REWRITE through a published door (den-hoag-56u5o). A `//` copy of a completed gen container whose `admits`
# is not the slot its fold was completed with is handed on as the check rewrite it states, so the value it drops is
# refused by name (`ci/tests-error.nix`, `admits-rewrite-door`). These cells are the other half: what the copy KEEPS is
# served as the plain container through the same door serves it, and the records the door must not read as a rewrite
# read as they did before it.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  noB = v: builtins.isAttrs v && !(v ? b);
  run =
    eng: k: T: v:
    let
      mods =
        builtins.genList (_: { options.x = (if eng == "gen" then gm else nl).mkOption { type = T; }; }) k
        ++ [ { x = v; } ];
      r =
        if eng == "gen" then
          (gm.evalModuleTree { } mods).config.x
        else
          (nl.evalModules { modules = mods; }).config.x;
      o = builtins.tryEval (builtins.deepSeq r r);
    in
    if o.success then o.value else "REFUSED";
  containers = {
    listOf = {
      t = gt.listOf gt.int;
      n = v: builtins.isList v && builtins.length v <= 1;
      ok = [ 1 ];
    };
    attrsOf = {
      t = gt.attrsOf gt.int;
      n = noB;
      ok = {
        a = 1;
      };
    };
    lazyAttrsOf = {
      t = gt.lazyAttrsOf gt.int;
      n = noB;
      ok = {
        a = 1;
      };
    };
    nullOr = {
      t = gt.nullOr gt.int;
      n = v: v == null || (builtins.isInt v && v < 5);
      ok = 1;
    };
    either = {
      t = gt.either gt.int gt.str;
      n = builtins.isInt;
      ok = 1;
    };
  };
  doors = {
    defineType = gt.defineType;
    mkOptionType = gm.mkOptionType;
  };
  # every container in `cs` x door x engine x declared once and twice, read through `f`
  grid =
    cs: f:
    builtins.mapAttrs (
      cn: C:
      builtins.mapAttrs (
        dn: door:
        nl.genAttrs [ "gen" "np" ] (
          eng: nl.genAttrs [ "once" "twice" ] (tn: f C door eng (if tn == "once" then 1 else 2))
        )
      ) doors
    ) cs;
in
{
  flake.tests.admits-rewrite-door = {
    # the value the narrowed `admits` keeps is served as the plain container serves it (red where the rewrite is
    # refused outright, or where its check judges a value the copy keeps)
    test-the-value-an-admits-rewrite-keeps-is-served-as-the-plain-container-serves-it = {
      expr = grid containers (
        C: door: eng: k:
        run eng k (door (C.t // { admits = C.n; })) C.ok
      );
      expected = grid containers (
        C: door: eng: k:
        run eng k (door C.t) C.ok
      );
    };
    # a copy REMOVING `admits` states no domain: its check is still its completion's, and it is served (an arm that
    # reads `admits` on every departing slot aborts here, uncatchably, `attribute 'admits' missing`)
    test-a-copy-removing-admits-is-served-as-the-plain-container =
      let
        cs = { inherit (containers) listOf nullOr; };
      in
      {
        expr = grid cs (
          C: door: eng: k:
          run eng k (door (builtins.removeAttrs C.t [ "admits" ])) C.ok
        );
        expected = grid cs (
          C: door: eng: k:
          C.ok
        );
      };
    # a self-referential type completed through `defineType` reads as it did before the arm: the door tells a copy by
    # the fold's own completion record, which forces no element (a test through the completion stamp forces the
    # element, and these types diverge)
    test-a-self-referential-type-through-define-type-reads-as-before =
      let
        list =
          let
            s = gt.defineType (gt.listOf s);
          in
          s;
        listNull =
          let
            s = gt.defineType (gt.listOf (gt.nullOr s));
          in
          s;
        vals = {
          empty = [ ];
          nested = [
            [ ]
            [ [ ] ]
          ];
          nulls = [
            null
            [ null ]
          ];
          int = [ 1 ];
        };
        read = T: nl.genAttrs [ "gen" "np" ] (eng: builtins.mapAttrs (_: run eng 1 T) vals);
      in
      {
        expr = {
          list = read list;
          listNull = read listNull;
        };
        expected = {
          list = {
            gen = {
              inherit (vals) empty nested;
              int = "REFUSED";
              nulls = "REFUSED";
            };
            np = {
              empty = "REFUSED";
              int = "REFUSED";
              nested = "REFUSED";
              nulls = "REFUSED";
            };
          };
          listNull = {
            gen = {
              inherit (vals) empty nested nulls;
              int = "REFUSED";
            };
            np = {
              empty = "REFUSED";
              int = "REFUSED";
              nested = "REFUSED";
              nulls = "REFUSED";
            };
          };
        };
      };
  };
}
