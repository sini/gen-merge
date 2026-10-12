# A gen nesting record copied with a `verify` is folded threaded at the option binding (den-hoag-jgr98).
#
# The engine's option binding answered a record stating `verify` without threading it, as a gen leaf. A gen
# submodule copied with a `verify` (`S // { verify }`, or a container of one) still folds by its threaded
# sibling, so answered as a leaf its CALLED fold refused every value ("its called `mergeDefs' does not
# evaluate the nested tree"), through the raw record, `defineType` and `mkOptionType` alike. The binding now
# asks for the threaded sibling, not for `verify`, and `threadedAs` keeps the `verify` the rich fold applies to
# the merged value. Used raw, that is the whole verdict. Through `defineType` and `mkOptionType` the copy
# also publishes a `check` derived from its `verify` under its base's check witness, which `threadedAs` reads
# as a rewrite and applies to each definition (den-hoag-d74w0); the door cells here therefore hold only values
# every surviving definition of which the `verify` also admits. Each served cell is paired with its refusing twin: a
# binding that dropped the `verify` would pass the first alone.
{
  genMerge,
  ...
}:
let
  gm = genMerge;
  gt = gm.types;
  inherit (builtins)
    all
    attrValues
    deepSeq
    isAttrs
    mapAttrs
    tryEval
    ;

  S = gt.submodule {
    options.a = gm.mkOption {
      type = gt.int;
      default = 1;
    };
    options.b = gm.mkOption {
      type = gt.int;
      default = 0;
    };
  };
  pS = v: !(isAttrs v) || (v.a or 2) != 1;
  # a gen submodule and each gen container of one, with how a value sits in it and `p` over its value
  bases = {
    sub = {
      x = S;
      w = v: v;
      p = pS;
    };
    nullOr = {
      x = gt.nullOr S;
      w = v: v;
      p = v: v == null || pS v;
    };
    listOf = {
      x = gt.listOf S;
      w = v: [ v ];
      p = all pS;
    };
    attrsOf = {
      x = gt.attrsOf S;
      w = v: { k = v; };
      p = v: all pS (attrValues v);
    };
  };
  rejected = p: v: if p v then null else "rejected by p";
  formsOf = B: {
    # a `verify` that rejects nothing
    ver0 = B.x // {
      verify = _: null;
    };
    verP = B.x // {
      verify = rejected B.p;
    };
    # an ad-hoc check override with a `verify` (the `both` form of `recompletion-identity`)
    both =
      B.x
      // {
        check = v: B.x.check v && B.p v;
      }
      // {
        verify = rejected B.p;
      };
  };
  rawDoor = {
    raw = x: x;
  };
  completingDoors = {
    inherit (gt) defineType;
    inherit (gm) mkOptionType;
  };
  doors = rawDoor // completingDoors;
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
  # `one` definition; `force`, a forced definition beside a losing one; `field` (the rejected side only), the
  # offending field left to the submodule's own default, so only the merged value shows it
  defsOf =
    B: n: m:
    {
      one = [ (B.w { a = n; }) ];
      force = [
        (gm.mkForce (B.w { a = n; }))
        (B.w { a = m; })
      ];
    }
    // (if n == 2 then { } else { field = [ (B.w { }) ]; });
  tableOn =
    doors: forms: n: m:
    mapAttrs (
      _: B:
      mapAttrs (_: X: mapAttrs (_: door: mapAttrs (_: read (door X)) (defsOf B n m)) doors) (
        forms (formsOf B)
      )
    ) bases;
  everyOn =
    doors: forms: n: f:
    mapAttrs (
      _: B:
      mapAttrs (_: _: mapAttrs (_: _: mapAttrs (_: _: f B) (defsOf B n 1)) doors) (forms (formsOf B))
    ) bases;
  table = tableOn doors;
  every = everyOn doors;
  served =
    B:
    B.w {
      a = 2;
      b = 0;
    };
  servedBad =
    B:
    B.w {
      a = 1;
      b = 0;
    };
  enforcing = f: { inherit (f) verP both; };
  accepting = f: { inherit (f) ver0; };
in
{
  flake.tests.nesting-verify-copy = {
    # Used raw, the value `p` admits is served at the value nixpkgs' twin merges.
    test-a-raw-verify-copy-of-a-gen-nesting-record-is-served = {
      expr = tableOn rawDoor (f: f) 2 1;
      expected = everyOn rawDoor (f: f) 2 served;
    };
    # Through `defineType` and `mkOptionType`, a value whose surviving definitions `p` also admits is served
    # (the door judges the definitions that survive the merge as well: den-hoag-d74w0; the losing definition of
    # `force` fails `p` and is not judged).
    test-a-door-completed-verify-copy-serves-a-value-its-surviving-definitions-admit = {
      expr = tableOn completingDoors (f: f) 2 1;
      expected = everyOn completingDoors (f: f) 2 served;
    };
    # Used raw, the `verify` judges the MERGED value alone: `q` reads a field no definition states (`c`, the
    # submodule's default) and a relation across definitions (`a = 1` needs `b = 1`), so every definition below
    # fails `q` while the merged value of the served ones passes it.
    test-a-raw-verify-copy-judges-the-merged-value =
      let
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
        q = v: v.c == 5 && (v.a != 1 || v.b == 1);
        copyOf = X: p: X // { verify = rejected p; };
        shapes = {
          sub = {
            x = copyOf Sq q;
            w = v: v;
          };
          attrsOf = {
            x = copyOf (gt.attrsOf Sq) (v: all q (attrValues v));
            w = v: { k = v; };
          };
        };
        cases = w: {
          defaulted = [ (w { a = 2; }) ];
          split = [
            (w { a = 1; })
            (w { b = 1; })
          ];
          function = [ (w ({ ... }: { b = 1; })) ];
          rejected = [ (w { b = 3; }) ];
        };
      in
      {
        expr = mapAttrs (_: s: mapAttrs (_: read s.x) (cases s.w)) shapes;
        expected = mapAttrs (_: s: {
          defaulted = s.w {
            a = 2;
            b = 0;
            c = 5;
          };
          split = s.w {
            a = 1;
            b = 1;
            c = 5;
          };
          function = s.w {
            a = 1;
            b = 1;
            c = 5;
          };
          rejected = "REFUSED";
        }) shapes;
      };
    # The binding asks for the threaded fold, not for a role: a record with the sibling and no `carries` (a
    # caller's `removeAttrs`) is threaded and served as its base is, and its `verify` still refuses. Asking
    # `carries` instead would answer it as a leaf, and its called fold would refuse the accepted value too.
    test-a-record-with-a-threaded-fold-and-no-role-is-threaded = {
      expr =
        let
          S1 = gt.submodule {
            options.a = gm.mkOption {
              type = gt.int;
              default = 1;
            };
          };
          r = removeAttrs (S1 // { verify = rejected (v: v.a != 1); }) [ "carries" ];
        in
        {
          shape = {
            threaded = r ? mergeDefs.threaded;
            carries = r ? carries;
          };
          ok = read r [ { a = 2; } ];
          bad = read r [ { } ];
          base = read (removeAttrs S1 [ "carries" ]) [ { a = 2; } ];
        };
      expected = {
        shape = {
          threaded = true;
          carries = false;
        };
        ok.a = 2;
        bad = "REFUSED";
        base.a = 2;
      };
    };
    # The value `p` rejects is refused through every door, the defaulted field included.
    test-a-value-the-verify-copy-rejects-stays-refused = {
      expr = table enforcing 1 2;
      expected = every enforcing 1 (_: "REFUSED");
    };
    # A `verify` that rejects nothing serves the value `p` would reject, as its base does.
    test-a-verify-copy-that-rejects-nothing-serves-what-its-base-serves = {
      expr = table accepting 1 2;
      expected = every accepting 1 servedBad;
    };

    # The record threads: the nested tree is a child of the one evaluation, so each module defining the
    # option is read at its own declaration address (a second root would read none), as the plain record is.
    # The `mkOptionType` image of this recording submodule reads none for the plain record too, so it is not
    # read here.
    test-a-verify-copy-threads-its-nested-tree =
      let
        sub = gt.submodule [
          {
            options.seen = gm.mkOption {
              type = gt.listOf gt.anything;
              default = [ ];
            };
          }
        ];
        n = sub.nests;
        E = gt.defineType (
          sub
          // {
            nests = n // {
              entry = d: {
                imports = [ (n.entry { inherit (d) file value; }) ];
                config.seen = [
                  (
                    let
                      r = tryEval (deepSeq d.declAt d.declAt);
                    in
                    if r.success then r.value else "REFUSED"
                  )
                ];
              };
              declAt = true;
            };
          }
        );
        at =
          T:
          let
            c =
              (gm.evalModuleTree { } [
                {
                  _file = "/decl.nix";
                  options.s = gm.mkOption { type = T; };
                }
                {
                  _file = "/def1.nix";
                  config.s = { };
                }
                {
                  _file = "/def2.nix";
                  config.s = { };
                }
              ]).config;
            o = tryEval (deepSeq c.s.seen c.s.seen);
          in
          if o.success then o.value else "REFUSED";
        copy = E // {
          verify = _: null;
        };
      in
      {
        expr = {
          plain = at E;
          raw = at copy;
          defineType = at (gt.defineType copy);
        };
        expected =
          let
            addrs = [
              [
                "a:1"
                "s"
              ]
              [
                "a:2"
                "s"
              ]
            ];
          in
          {
            plain = addrs;
            raw = addrs;
            defineType = addrs;
          };
      };

    # The values: a gen leaf stating `verify`, and a copy of a container over a leaf (which nests nothing), serve
    # and refuse as they did. This pins values, not which arm answers them: the value is the same on either arm.
    test-a-leaf-verify-and-a-container-over-a-leaf-verify-keep-their-values = {
      expr = {
        leafOk = read (gt.int // { verify = rejected (v: v != 1); }) [ 2 ];
        leafBad = read (gt.int // { verify = rejected (v: v != 1); }) [ 1 ];
        listOk = read (gt.listOf gt.int // { verify = rejected (all (v: v != 1)); }) [ [ 2 ] ];
        listBad = read (gt.listOf gt.int // { verify = rejected (all (v: v != 1)); }) [ [ 1 ] ];
      };
      expected = {
        leafOk = 2;
        leafBad = "REFUSED";
        listOk = [ 2 ];
        listBad = "REFUSED";
      };
    };
  };
}
