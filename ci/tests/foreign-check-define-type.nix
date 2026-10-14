# A FOREIGN `check` STATED ON A DESCRIPTOR HANDED TO THE PUBLISHED `defineType` (den-hoag-zdp46). The door imports it
# as the import door imports a `check` (`interface.importDefined`), so the value it rejects is refused by name
# (`ci/tests-error.nix`, `foreign-check-define-type`). These cells are the other half: what every stated predicate
# admits is served as nixpkgs' own `mkOptionType` stating their conjunction serves it, a raw gen-types leaf (whose own
# curried `check` beside `verify` is no foreign check, `interface.checksDefs`) reads as it did, and a member stating
# `verify` and `check` is not chosen by a union for a value its check rejects.
{
  genMerge,
  genTypes,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
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
  # each predicate rejects one int of its own: the check 3, `admits` 5, `verify` 7
  fields = {
    check = v: builtins.isInt v && v != 3;
    admits = v: builtins.isInt v && v != 5;
    verify = v: if builtins.isInt v && v != 7 then null else "not an int other than 7";
    mergeDefs = loc: defs: nl.mergeEqualOption loc defs;
  };
  # every descriptor stating `check`, with any of `admits`, `verify`, `mergeDefs` beside it
  descriptors = builtins.listToAttrs (
    map
      (ks: {
        name = builtins.concatStringsSep "-" ks;
        value = {
          name = "evenT";
        }
        // nl.getAttrs ks fields;
      })
      (
        map (s: [ "check" ] ++ s) [
          [ ]
          [ "admits" ]
          [ "verify" ]
          [ "mergeDefs" ]
          [
            "admits"
            "verify"
          ]
          [
            "admits"
            "mergeDefs"
          ]
          [
            "verify"
            "mergeDefs"
          ]
          [
            "admits"
            "verify"
            "mergeDefs"
          ]
        ]
      )
  );
  grid =
    f:
    builtins.mapAttrs (
      _: d:
      nl.genAttrs [ "gen" "np" ] (
        eng: nl.genAttrs [ "once" "twice" ] (tn: f d eng (if tn == "once" then 1 else 2))
      )
    ) descriptors;
in
{
  flake.tests.foreign-check-define-type = {
    # a value every stated predicate admits is served (red where the door refuses a descriptor stating `check`)
    test-a-value-every-stated-predicate-admits-is-served = {
      expr = grid (
        d: eng: k:
        run eng k (gt.defineType d) 4
      );
      expected = grid (
        _: _: _:
        4
      );
    };
    # the check is imported BESIDE what the descriptor states in gen's words, never over it: a value only its `admits`
    # rejects (5) or only its `verify` rejects (7) is refused, in both engines, through `defineType` and through the
    # import door `mkOptionType`, whose checked fold judges the check and the `admits` together. Red where the import
    # overwrites a stated `admits` with the check, or folds by the check alone.
    test-what-a-stated-admits-or-verify-rejects-beside-the-check-is-refused =
      let
        doors = {
          define-type = gt.defineType;
          mk-option-type = gm.mkOptionType;
        };
        read =
          f:
          builtins.mapAttrs (
            _: door:
            builtins.mapAttrs (
              _: d:
              nl.genAttrs [ "gen" "np" ] (
                eng:
                nl.optionalAttrs (d ? admits) { v5 = f eng door d 5; }
                // nl.optionalAttrs (d ? verify) { v7 = f eng door d 7; }
              )
            ) descriptors
          ) doors;
      in
      {
        expr = read (
          eng: door: d: v:
          map (k: run eng k (door d) v) [
            1
            2
          ]
        );
        expected = read (
          _: _: _: _: [
            "REFUSED"
            "REFUSED"
          ]
        );
      };

    # a raw gen-types leaf states its own curried `check` beside `verify`: it is no foreign check, and it reads as it
    # did (an arm reading every `check` as foreign aborts or refuses here)
    test-a-raw-gen-types-leaf-reads-as-before =
      let
        gtl = genTypes;
        leaves = {
          string = [
            "a"
            1
          ];
          int = [
            1
            "a"
          ];
          bool = [
            true
            1
          ];
          float = [
            1.5
            1
          ];
        };
      in
      {
        expr = builtins.mapAttrs (
          n: vs: nl.genAttrs [ "gen" "np" ] (eng: map (run eng 1 (gt.defineType gtl.${n})) vs)
        ) leaves;
        expected = builtins.mapAttrs (
          _: vs:
          nl.genAttrs [ "gen" "np" ] (_: [
            (builtins.head vs)
            "REFUSED"
          ])
        ) leaves;
      };
    # a union member stating `verify` and `check` is not chosen for a value its check rejects, so the next member
    # serves it, as nixpkgs' twin (one `check`, their conjunction) is not chosen
    test-a-union-skips-a-member-whose-check-rejects =
      let
        d = descriptors.check-verify;
      in
      {
        expr = nl.genAttrs [ "gen" "np" ] (
          eng:
          run eng 1 ((if eng == "gen" then gt else nl.types).either (gt.defineType d)
            (if eng == "gen" then gt else nl.types).int
          ) 3
        );
        expected = {
          gen = 3;
          np = 3;
        };
      };
    # a fresh descriptor carrying a stock container's own v2 fold (a nixpkgs type with `_type` removed) and stating a
    # `check` that is not the fold's coherent one, or a `verify` beside the fold's own `check`: each stated predicate is
    # its domain, declared once and twice, in both engines. Red where the door imports such a `check` as an ad-hoc
    # override of the fold (the admitted value refused) or routes a stated `verify` past the door's `verify` arm (the
    # value it rejects served by nixpkgs' engine declared twice); `submodule` is the module-set fold.
    test-a-check-or-verify-stated-over-a-stock-fold-is-its-domain =
      let
        np = nl.types;
        sub = np.submodule { options.a = nl.mkOption { type = np.int; }; };
        has =
          n: v: v == n || builtins.isList v && builtins.elem n v || builtins.isAttrs v && (v.a or null) == n;
        noNine = v: if has 9 v then "holds 9" else null;
        folds = {
          list-of-int = {
            type = np.listOf np.int;
            check = v: builtins.isList v && builtins.length v < 3;
            values = {
              ok = [ 1 ];
              check = [
                1
                2
                3
              ];
              verify = [ 9 ];
            };
          };
          submodule = {
            type = sub;
            check = v: !(has 3 v);
            values = {
              ok.a = 1;
              check.a = 3;
              verify.a = 9;
            };
          };
        };
        shapes = f: {
          check = removeAttrs f.type [ "_type" ] // {
            inherit (f) check;
          };
          check-verify = removeAttrs f.type [ "_type" ] // {
            inherit (f) check;
            verify = noNine;
          };
          verify = removeAttrs f.type [ "_type" ] // {
            verify = noNine;
          };
        };
        rejects = {
          check = [ "check" ];
          check-verify = [
            "check"
            "verify"
          ];
          verify = [ "verify" ];
        };
        read =
          g:
          builtins.mapAttrs (
            _: f:
            builtins.mapAttrs (
              sn: d:
              nl.genAttrs [ "gen" "np" ] (
                eng: nl.genAttrs [ "once" "twice" ] (tn: builtins.mapAttrs (vn: v: g f sn d eng tn vn v) f.values)
              )
            ) (shapes f)
          ) folds;
      in
      {
        expr = read (
          _: _: d: eng: tn: _: v:
          run eng (if tn == "once" then 1 else 2) (gt.defineType d) v
        );
        expected = read (
          _: sn: _: _: _: vn: v:
          if builtins.elem vn rejects.${sn} then "REFUSED" else v
        );
      };
  };
}
