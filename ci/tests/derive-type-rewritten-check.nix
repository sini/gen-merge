# `deriveType` KEEPS A CHECK-REWRITTEN BASE'S CHECK (den-hoag-vtfqp).
#
# `np.addCheck G p` and `G // { check }` over a gen module-set type G (`submodule`, or `nullOr` / `listOf` /
# `attrsOf` / `either` / `nullOr nullOr` of one) state a check on a record whose checked fold is the plain
# one: the rewritten check lives in the `check` field and its `_checkWitness`, and nowhere else. A
# derivation over it carries "the base's check and fold" (derive-type.nix C5), so the pair crosses the
# derivation's cut. `deriveType` used to cut it, and the derivation then served the value its base refuses.
# An `either` of a submodule states no module set itself (`getSubModules` null), so its `// { check }` is the
# ad-hoc override nixpkgs refuses, not the module-set check the owner's ruling covers: declared alone it is
# refused by name, as nixpkgs refuses it, the accepted value too, and declared twice it is met and served.
# Each served cell is paired with its refusing twin, and `unrewritten` is the control that the refusing
# cells fire on the rewrite and not on every module set.
{
  genMerge,
  genTypes,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  gt = gm.types;
  np = nixpkgsLib.types;
  inherit (builtins) deepSeq tryEval mapAttrs;

  isBad =
    v:
    v == 1
    || (builtins.isAttrs v && ((v.a or null) == 1 || builtins.any isBad (builtins.attrValues v)))
    || (builtins.isList v && builtins.any isBad v);
  p = v: !(isBad v);
  g = gt.submodule { options.a = gm.mkOption { type = gt.int; }; };
  # the module-set shapes, with the value each holds
  shapes = {
    sub = {
      b = g;
      ok = {
        a = 2;
      };
      bad = {
        a = 1;
      };
    };
    nullSub = {
      b = gt.nullOr g;
      ok = {
        a = 2;
      };
      bad = {
        a = 1;
      };
    };
    listSub = {
      b = gt.listOf g;
      ok = [ { a = 2; } ];
      bad = [ { a = 1; } ];
    };
    attrsSub = {
      b = gt.attrsOf g;
      ok = {
        k = {
          a = 2;
        };
      };
      bad = {
        k = {
          a = 1;
        };
      };
    };
    eitherSub = {
      b = gt.either g gt.str;
      ok = {
        a = 2;
      };
      bad = {
        a = 1;
      };
    };
    nullNullSub = {
      b = gt.nullOr (gt.nullOr g);
      ok = {
        a = 2;
      };
      bad = {
        a = 1;
      };
    };
  };
  # the leaves and leaf containers, where the check always survived: the control population
  leaves = {
    int = {
      b = gt.int;
      ok = 2;
      bad = 1;
    };
    listInt = {
      b = gt.listOf gt.int;
      ok = [ 2 ];
      bad = [ 1 ];
    };
  };
  # the two spellings of a rewritten check
  forms = {
    add = b: np.addCheck b p;
    ovr =
      b:
      b
      // {
        check = v: b.check v && p v;
      };
  };
  derive = b: gt.deriveType { key = "k"; } "d" b;
  # how the derivation is taken: over the copy itself, and over the copy through the `mkOptionType` door
  doors = {
    over = derive;
    viaDoor = c: derive (gm.mkOptionType c);
    twice = c: gt.deriveType { key = "j"; } "e" (derive c);
  };

  read =
    mods:
    let
      v = (gm.evalModuleTree { } mods).config.x;
      o = tryEval (deepSeq v v);
    in
    if o.success then o.value else "REFUSED";
  decl = T: { options.x = gm.mkOption { type = T; }; };
  arrs = {
    a =
      T: v:
      read [
        (decl T)
        { x = v; }
      ];
    LL =
      T: v:
      read [
        (decl T)
        (decl T)
        { x = v; }
      ];
  };
  # what each cell reads, for one population, one way of taking the type and one value
  tableOf =
    pop: way: val:
    mapAttrs (
      _: S:
      mapAttrs (
        _: form: mapAttrs (_: door: mapAttrs (_: arr: arr (door (form S.b)) S.${val}) arrs) way
      ) forms
    ) pop;
  every =
    pop: f:
    mapAttrs (_: S: mapAttrs (_: _: mapAttrs (_: _: mapAttrs (_: _: f S) arrs) doors) forms) pop;
  # the ad-hoc override on the `either` declared alone, which is refused rather than served
  adHocOnce =
    table:
    table
    // {
      eitherSub = table.eitherSub // {
        ovr = mapAttrs (_: d: builtins.removeAttrs d [ "a" ]) table.eitherSub.ovr;
      };
    };
in
{
  flake.tests.derive-type-rewritten-check = {
    # The value the rewritten check rejects stays refused through the derivation, in every module-set
    # shape, both spellings, and both arrangements. A derivation that cut the check would serve it.
    test-a-derivation-over-a-check-rewritten-module-set-refuses-the-rejected-value = {
      expr = tableOf shapes doors "bad";
      expected = every shapes (_: "REFUSED");
    };
    # The value every declared check admits is still served, at the value it holds.
    test-a-derivation-over-a-check-rewritten-module-set-serves-the-accepted-value = {
      expr = adHocOnce (tableOf shapes doors "ok");
      expected = adHocOnce (every shapes (S: S.ok));
    };
    # The ad-hoc override on the `either` of a submodule, declared alone, refuses the accepted value by name.
    test-a-derivation-over-an-ad-hoc-check-on-an-either-of-a-submodule-refuses-the-accepted-value-declared-alone = {
      expr = mapAttrs (_: door: arrs.a (door (forms.ovr shapes.eitherSub.b)) shapes.eitherSub.ok) doors;
      expected = mapAttrs (_: _: "REFUSED") doors;
    };
    # The derivation reads as the underived copy does, on both values.
    test-the-derivation-agrees-with-the-underived-copy = {
      expr = {
        ok = tableOf shapes (builtins.removeAttrs doors [ "twice" ]) "ok";
        bad = tableOf shapes (builtins.removeAttrs doors [ "twice" ]) "bad";
      };
      expected =
        let
          copy = tableOf shapes {
            over = c: c;
            viaDoor = gm.mkOptionType;
          };
        in
        {
          ok = copy "ok";
          bad = copy "bad";
        };
    };
    # Control: over the UNREWRITTEN base the derivation serves what the base admits, the rejected value
    # included, so the refusing cells above fire on the rewrite and not on every module set.
    test-control-a-derivation-over-the-unrewritten-module-set-serves-what-the-base-admits = {
      expr = mapAttrs (_: S: mapAttrs (_: arr: arr (derive S.b) S.bad) arrs) shapes;
      expected = mapAttrs (_: S: mapAttrs (_: _: S.bad) arrs) shapes;
    };
    # Control: over a leaf and a leaf container, where the check always survived, it still does.
    test-control-a-derivation-over-a-check-rewritten-leaf-still-refuses-the-rejected-value = {
      expr = {
        bad = tableOf leaves doors "bad";
        ok = tableOf leaves doors "ok";
      };
      expected = {
        bad = every leaves (_: "REFUSED");
        ok = every leaves (S: S.ok);
      };
    };
    # The rewritten submodule bare, declared once: the cell den-hoag-n8ssa moved from refused to served.
    test-a-derivation-over-a-bare-check-rewritten-submodule-refuses-in-one-declaration = {
      expr = {
        add = arrs.a (derive (forms.add g)) shapes.sub.bad;
        ovr = arrs.a (derive (forms.ovr g)) shapes.sub.bad;
      };
      expected = {
        add = "REFUSED";
        ovr = "REFUSED";
      };
    };
    # Two separately-built derivations of one rewritten base, declared together, are not `typeEq` (below)
    # but still merge and enforce: the accepted value is served, the rejected one refused.
    test-two-separate-derivations-of-a-check-rewritten-base-declare-together =
      let
        two =
          S: form: val:
          let
            c = forms.${form} S.b;
          in
          read [
            (decl (derive c))
            (decl (derive c))
            { x = S.${val}; }
          ];
      in
      {
        expr = mapAttrs (
          _: S:
          mapAttrs (form: _: {
            ok = two S form "ok";
            bad = two S form "bad";
          }) forms
        ) { inherit (shapes) sub attrsSub; };
        expected = mapAttrs (
          _: S:
          mapAttrs (_: _: {
            ok = S.ok;
            bad = "REFUSED";
          }) forms
        ) { inherit (shapes) sub attrsSub; };
      };
    # Identity and phrase are not the check's: the mint regime, the name and the description read as
    # they do over the unrewritten base, and a derivation is still not its base. Two derivations of
    # one rewritten base are COMPARED by value (the standing of every check-rewritten record under
    # `typeEq`, ADR-0034), so separate constructions are unequal where they were equal while the check
    # was cut.
    test-a-derivation-over-a-check-rewritten-base-keeps-its-identity-and-phrase =
      let
        c = forms.add g;
        d = derive c;
        dP = derive g;
      in
      {
        expr = {
          regime = builtins.attrNames d.__mint;
          sealed = builtins.attrNames d.__sealed;
          name = d.name;
          phrase = d.description == dP.description;
          self = genTypes.typeEq d d;
          notItsBase = genTypes.typeEq d dP;
          separateConstructions = genTypes.typeEq d (derive c);
        };
        expected = {
          regime = [ "minted" ];
          sealed = [ "members.0" ];
          name = "submodule";
          phrase = true;
          self = true;
          notItsBase = false;
          separateConstructions = false;
        };
      };
  };
}
