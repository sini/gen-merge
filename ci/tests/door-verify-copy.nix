# A verify copy of a type through the published doors (`types.defineType`, `mkOptionType`) is judged on its MERGED
# value by gen's readers, as the raw copy is, and publishes a one-definition projection as its own check witness for
# foreign readers (den-hoag-d74w0, owner arm (ii)). An ad-hoc override beside the verify stays a per-definition check.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  inherit (builtins)
    all
    attrValues
    deepSeq
    isAttrs
    mapAttrs
    tryEval
    ;
  read =
    ty: defs:
    let
      v =
        (gm.evalModuleTree { } (
          [ { options.x = gm.mkOption { type = ty; }; } ] ++ map (d: { x = d; }) defs
        )).config.x;
      o = tryEval (deepSeq v v);
    in
    if o.success then o.value else "REFUSED";
  readNp =
    ty: defs:
    let
      v =
        (nl.evalModules {
          modules = [ { options.x = nl.mkOption { type = ty; }; } ] ++ map (d: { x = d; }) defs;
        }).config.x;
      o = tryEval (deepSeq v v);
    in
    if o.success then o.value else "REFUSED";
  rejected = p: v: if p v then null else "rejected by p";
  doors = {
    inherit (gt) defineType;
    inherit (gm) mkOptionType;
  };
  Sq = gt.submodule {
    options.a = gm.mkOption {
      type = gt.int;
      default = 1;
    };
    options.b = gm.mkOption {
      type = gt.int;
      default = 0;
    };
    options.c = gm.mkOption {
      type = gt.int;
      default = 5;
    };
  };
  # total on the type's members only (`v.c`, `v.a` are the submodule's defaults on no definition)
  q = v: v.c == 5 && (v.a != 1 || v.b == 1);
  shapes = {
    sub = {
      x = Sq;
      w = v: v;
      p = q;
    };
    nullOr = {
      x = gt.nullOr Sq;
      w = v: v;
      p = v: v == null || q v;
    };
    attrsOf = {
      x = gt.attrsOf Sq;
      w = v: { k = v; };
      p = v: all q (attrValues v);
    };
  };
  # (a list's definitions are separate elements, so a split is not one merged member: `sep.nix` holds `listOf`
  # against nixpkgs' value)
  # each definition fails `q`; the merged value of every one but `rejected` passes it
  cases = w: {
    defaulted = [ (w { a = 2; }) ];
    split = [
      (w { a = 1; })
      (w { b = 1; })
    ];
    function = [ (w ({ ... }: { b = 1; })) ];
    forced = [
      (w {
        a = 1;
        b = gm.mkForce 1;
      })
      (w { b = 0; })
    ];
    defaulting = [
      (w {
        a = 1;
        b = gm.mkDefault 0;
      })
      (w { b = 1; })
    ];
    conditional = [
      (w {
        a = 1;
        b = gm.mkIf true 1;
      })
    ];
    rejected = [ (w { b = 3; }) ];
  };
  want = w: {
    defaulted = w {
      a = 2;
      b = 0;
      c = 5;
    };
    split = w {
      a = 1;
      b = 1;
      c = 5;
    };
    function = w {
      a = 1;
      b = 1;
      c = 5;
    };
    forced = w {
      a = 1;
      b = 1;
      c = 5;
    };
    defaulting = w {
      a = 1;
      b = 1;
      c = 5;
    };
    conditional = w {
      a = 1;
      b = 1;
      c = 5;
    };
    rejected = "REFUSED";
  };
  # the `both` form: an ad-hoc override beside the `verify`, admitting every definition here
  forms = X: p: {
    verify = X // {
      verify = rejected p;
    };
    both =
      X
      // {
        check = v: X.check v && true;
      }
      // {
        verify = rejected p;
      };
  };
  # a copy of a nesting record and a copy of a container over a leaf, through each door
  pair = Y: Y ? _checkWitness && Y.check == Y._checkWitness;
  S1 = gt.submodule {
    options.a = gm.mkOption {
      type = gt.int;
      default = 1;
    };
  };
  notSeven = v: !(isAttrs v) || (v.a or 0) != 7;
  ovr = S1 // { check = v: S1.check v && notSeven v; } // { verify = _: null; };
  np = nl.types;
  # a member-reading verify (`v.c`, no `or`): a per-definition reading of it aborts uncatchably
  kinds = {
    nest = {
      t = Sq // {
        verify = rejected q;
      };
      ok = [
        { a = 1; }
        { b = 1; }
      ];
      bad = [ { a = 1; } ];
    };
    leaf = {
      t = gt.listOf gt.int // {
        verify = rejected (v: builtins.length v == 2);
      };
      ok = [
        [ 1 ]
        [ 2 ]
      ];
      bad = [ [ 1 ] ];
    };
  };
  # an alternative that OVERLAPS the copy: it admits the value the copy's verify rejects, so a union must try it
  overlapping = {
    either = y: np.either y (np.attrsOf np.int);
    oneOf =
      y:
      np.oneOf [
        y
        (np.attrsOf np.int)
      ];
    gtEither = y: gt.either y (gt.attrsOf gt.int);
    gtOneOf =
      y:
      gt.oneOf [
        y
        (gt.attrsOf gt.int)
      ];
  };
  readNpGen =
    ty: defs:
    let
      v =
        (nl.evalModules {
          modules = [ { options.x = nl.mkOption { type = ty; }; } ] ++ map (d: { x = d; }) defs;
        }).config.x;
      o = tryEval (deepSeq v v);
    in
    if o.success then o.value else "REFUSED";
  unions = {
    either = y: np.either y np.str;
    eitherR = y: np.either np.str y;
    oneOf =
      y:
      np.oneOf [
        np.int
        y
      ];
  };
in
{
  flake.tests.door-verify-copy = {
    # A stock nixpkgs container over a gen leaf's verify copy, through `mkOptionType`, is re-homed (den-hoag-8uwxu,
    # the door's guard is `homedAt`'s own): the fold reads the copy's `verify`, so the rejected value refuses
    # declared alone and twice, and `deriveType` over the same container serves the admitted one at nixpkgs' value
    test-a-stock-container-over-a-verify-copy-through-mk-option-type-reads-the-verify =
      let
        copy = gt.int // {
          verify = v: if v < 10 then null else "the copy rejects ${toString v}";
        };
        containers = {
          attrsOf = {
            m = np.attrsOf;
            w = v: { k = v; };
          };
          lazyAttrsOf = {
            m = np.lazyAttrsOf;
            w = v: { k = v; };
          };
          listOf = {
            m = np.listOf;
            w = v: [ v ];
          };
          nullOr = {
            m = np.nullOr;
            w = v: v;
          };
          either = {
            m = t: np.either t np.str;
            w = v: v;
          };
        };
        decl = n: ty: map (_: { options.x = gm.mkOption { type = ty; }; }) (builtins.genList (i: i) n);
        readN =
          n: ty: v:
          let
            x = (gm.evalModuleTree { } (decl n ty ++ [ { x = v; } ])).config.x;
            o = tryEval (deepSeq x x);
          in
          if o.success then o.value else "REFUSED";
        twin = c: v: readNp (c.m np.int) [ (c.w v) ];
      in
      {
        expr =
          mapAttrs (_: c: {
            bad = readN 1 (gm.mkOptionType (c.m copy)) (c.w 20);
            ok = readN 1 (gm.mkOptionType (c.m copy)) (c.w 1) == twin c 1;
            derived = readN 1 (gm.deriveType { } "uccyi" (c.m copy)) (c.w 1) == twin c 1;
          }) containers
          // {
            LL =
              let
                c = containers.attrsOf;
              in
              {
                bad = readN 2 (gm.mkOptionType (c.m copy)) (c.w 20);
                # a nixpkgs leaf's copy: over gen's `int` the twice-derived join still states no `recarry`
                derived =
                  readN 2 (gm.deriveType { } "uccyi" (c.m (np.int // { inherit (copy) verify; }))) (c.w 1)
                  == twin c 1;
              };
          };
        expected =
          mapAttrs (_: _: {
            bad = "REFUSED";
            ok = true;
            derived = true;
          }) containers
          // {
            LL = {
              bad = "REFUSED";
              derived = true;
            };
          };
      };
    # Through each door, the `verify` judges the MERGED value, as it does raw.
    test-a-door-completed-verify-copy-judges-the-merged-value = {
      expr = mapAttrs (
        _: s:
        mapAttrs (_: door: mapAttrs (_: X: mapAttrs (_: read (door X)) (cases s.w)) (forms s.x s.p)) doors
      ) shapes;
      expected = mapAttrs (_: s: mapAttrs (_: _: mapAttrs (_: _: want s.w) (forms s.x s.p)) doors) shapes;
    };
    # The door publishes the copy's own definition check and its witness as one pair: a verify copy's pair is
    # coherent, and an override's stays the witnessed rewrite it arrived as, whose `check` is the override's.
    test-a-door-completed-verify-copy-of-a-nesting-record-publishes-its-own-check-pair = {
      expr = mapAttrs (
        _: door:
        let
          v = door (S1 // { verify = _: null; });
          o = door ovr;
        in
        {
          verify = pair v;
          override = pair o;
          overrideRejectsSeven = !(o.check { a = 7; }) && o.check { a = 2; };
        }
      ) doors;
      expected = mapAttrs (_: _: {
        verify = true;
        override = false;
        overrideRejectsSeven = true;
      }) doors;
    };
    # An ad-hoc override beside the `verify` is still judged on each definition (ADR-0039, 2026-10-08).
    test-an-override-beside-a-verify-is-judged-per-definition-through-each-door = {
      expr = mapAttrs (_: door: {
        seven = read (door ovr) [ { a = 7; } ];
        two = read (door ovr) [ { a = 2; } ];
      }) (doors // { raw = x: x; });
      expected = mapAttrs (_: _: {
        seven = "REFUSED";
        two.a = 2;
      }) (doors // { raw = x: x; });
    };
    # Through each door, a foreign union read under nixpkgs' own `evalModules` sees the copy's one-definition
    # projection (owner arm (ii)): at a union whose other member does not overlap the copy, a split the verify
    # admits only merged is refused, as nixpkgs' own `addCheck` twin refuses it, and a merged value the verify
    # rejects is refused too, for a nesting copy and a copy of a container over leaves.
    test-a-door-completed-verify-copy-is-judged-per-definition-at-a-foreign-union = {
      expr = mapAttrs (
        _: door:
        mapAttrs (
          _: k:
          mapAttrs (_: u: {
            ok = readNp (u (door k.t)) k.ok;
            bad = readNp (u (door k.t)) k.bad;
          }) unions
        ) kinds
      ) doors;
      expected = mapAttrs (
        _: _:
        mapAttrs (
          _: _:
          mapAttrs (_: _: {
            ok = "REFUSED";
            bad = "REFUSED";
          }) unions
        ) kinds
      ) doors;
    };
    # A door copy as a member of an OVERLAPPING union: the copy's verify rejects the value and the other member
    # admits it, so the union serves the other member's reading, as main and nixpkgs' `addCheck` twin do. The
    # member choice reads the copy's verify as a reason to move on, never as a throw inside the choice.
    test-a-door-completed-verify-copy-yields-to-an-overlapping-union-member = {
      expr = mapAttrs (
        _: door:
        let
          Y = door kinds.nest.t;
          v = [
            {
              a = 2;
              c = 4;
            }
          ];
        in
        {
          either = read (overlapping.either Y) v;
          oneOf = read (overlapping.oneOf Y) v;
          gtEither = read (overlapping.gtEither Y) v;
          gtOneOf = read (overlapping.gtOneOf Y) v;
          gtEitherNp = readNpGen (overlapping.gtEither Y) v;
          gtOneOfNp = readNpGen (overlapping.gtOneOf Y) v;
        }
      ) doors;
      expected = mapAttrs (
        _: _:
        let
          served = {
            a = 2;
            c = 4;
          };
        in
        {
          either = served;
          oneOf = served;
          gtEither = served;
          gtOneOf = served;
          gtEitherNp = served;
          gtOneOfNp = served;
        }
      ) doors;
    };
  };
}
