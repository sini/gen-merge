# A check nixpkgs' `addCheck` states over a nixpkgs submodule is enforced in gen's engine, alone and
# beside another submodule declaration, at the top and as a container's element, through a gen
# container too (den-hoag-8ip0d).
#
# nixpkgs rebuilds a module-set type at declaration (`fixupOptionType`, `substSubModules`), which
# erases a wrapper's check, and a declaration fold joins module sets without one, so nixpkgs serves a
# value the wrapper rejects. A foreign record states no check witness, so no merge step can see the
# drop; the mount and the declaration list's fixup carry every foreign declaration's check instead
# (`interface.carriedAtDepth`). Each refusal is paired with its passing twin, so a carriage that refused
# everything would not pass.

{
  genMerge,
  nixpkgsLib,
  ...
}:

let
  gm = genMerge;
  gt = gm.types;
  np = nixpkgsLib.types;
  inherit (builtins) deepSeq tryEval;

  accepted =
    ts: v:
    let
      x =
        (gm.evalModuleTree { } (map (t: { options.x = gm.mkOption { type = t; }; }) ts ++ [ { x = v; } ]))
        .config.x;
    in
    (tryEval (deepSeq x x)).success;

  intOpt = mk: t: n: {
    options.${n} = mk {
      type = t;
      default = 0;
    };
  };
  not7 = v: !(builtins.isAttrs v && (v.a or 0) == 7);
  W = np.addCheck (np.submodule (intOpt nixpkgsLib.mkOption np.int "a")) not7;
  N = np.submodule (intOpt nixpkgsLib.mkOption np.int "b");
  G = gt.submodule (intOpt gm.mkOption gt.int "c");
  both = ts: ok: bad: {
    ok = accepted ts ok;
    bad = accepted ts bad;
  };
  top = ts: both ts { a = 1; } { a = 7; };
  attrs = ts: both ts { k.a = 1; } { k.a = 7; };
  list = ts: both ts [ { a = 1; } ] [ { a = 7; } ];
  nested = ts: both ts { k.j.a = 1; } { k.j.a = 7; };
  enforced = {
    ok = true;
    bad = false;
  };
in

{
  flake.tests.module-set-carriage = {
    test-a-foreign-wrapper-over-a-submodule-beside-another-declaration-is-enforced = {
      expr = {
        alone = top [ W ];
        gen = top [
          W
          G
        ];
        genFirst = top [
          G
          W
        ];
        foreign = top [
          N
          W
        ];
        three = top [
          G
          N
          W
        ];
      };
      expected = {
        alone = enforced;
        gen = enforced;
        genFirst = enforced;
        foreign = enforced;
        three = enforced;
      };
    };
    test-a-foreign-wrapper-over-a-submodule-element-is-enforced = {
      expr = {
        attrsAlone = attrs [ (np.attrsOf W) ];
        attrsGen = attrs [
          (gt.attrsOf G)
          (np.attrsOf W)
        ];
        attrsForeign = attrs [
          (np.attrsOf W)
          (np.attrsOf N)
        ];
        listAlone = list [ (np.listOf W) ];
        listGen = list [
          (np.listOf W)
          (gt.listOf G)
        ];
      };
      expected = {
        attrsAlone = enforced;
        attrsGen = enforced;
        attrsForeign = enforced;
        listAlone = enforced;
        listGen = enforced;
      };
    };
    # the walk descends through a container that owes nothing itself, a gen one included
    test-a-foreign-wrapper-below-a-gen-container-in-a-foreign-one-is-enforced = {
      expr = nested [ (np.attrsOf (gt.attrsOf W)) ];
      expected = enforced;
    };
    # an ad-hoc `// { check }` override of a nixpkgs submodule is the same check (den-hoag-ukitj): beside
    # a gen submodule and as an element, what it admits is served and what it rejects is refused
    test-an-ad-hoc-override-of-a-submodule-is-enforced-as-a-wrapper-is = {
      expr =
        let
          S = np.submodule (intOpt nixpkgsLib.mkOption np.int "a");
          Ah = S // {
            check = v: S.check v && not7 v;
          };
        in
        {
          beside = top [
            Ah
            G
          ];
          element = attrs [ (np.attrsOf Ah) ];
        };
      expected = {
        beside = enforced;
        element = enforced;
      };
    };
    # a module set reaches a foreign `substSubModules` located at its declaring file, as nixpkgs'
    # `mergeOptionDecls` hands it: `attrTag`'s destructures `{ _file, imports }`, so a bare module
    # aborted it, uncatchably, wherever the declaration list is rebuilt
    test-a-nixpkgs-attrTag-over-a-submodule-redeclared-serves-nixpkgs-value = {
      expr =
        let
          tag = np.attrTag {
            t = nixpkgsLib.mkOption {
              type = np.submodule { options.a = nixpkgsLib.mkOption { type = np.int; }; };
            };
          };
          door = gt.defineType tag;
          served =
            ts:
            (gm.evalModuleTree { } (
              map (t: { options.x = gm.mkOption { type = t; }; }) ts ++ [ { x.t.a = 2; } ]
            )).config.x;
        in
        {
          raw = served [
            tag
            tag
          ];
          door = served [
            door
            door
          ];
          rawBesideDoor = served [
            tag
            door
          ];
          doorBesideRaw = served [
            door
            tag
          ];
        };
      expected =
        let
          tag = np.attrTag {
            t = nixpkgsLib.mkOption {
              type = np.submodule { options.a = nixpkgsLib.mkOption { type = np.int; }; };
            };
          };
          served =
            (nixpkgsLib.evalModules {
              modules = [
                { options.x = nixpkgsLib.mkOption { type = tag; }; }
                { options.x = nixpkgsLib.mkOption { type = tag; }; }
                { x.t.a = 2; }
              ];
            }).config.x;
        in
        {
          raw = served;
          door = served;
          rawBesideDoor = served;
          doorBesideRaw = served;
        };
    };
    # a checked nixpkgs submodule through `mkOptionType` is a gen completion over a module set gen did not
    # build: its check rides on every rebuild as the raw record's does, redeclared beside the plain
    # submodule, beside it through the same door, twice, below a gen container and as a nixpkgs
    # container's element
    test-a-checked-nixpkgs-submodule-through-mkOptionType-is-enforced-redeclared =
      let
        M = gm.mkOptionType;
        # the twin is the record the form wraps, and it states no default: a module set declared twice
        # declares its options twice, and two declarations of one option may not both state a default
        S = np.submodule { options.a = nixpkgsLib.mkOption { type = np.int; }; };
        forms = {
          wrapper = np.addCheck S not7;
          adHoc = S // {
            check = v: S.check v && not7 v;
          };
        };
        at = X: {
          beside = top [
            S
            (M X)
          ];
          after = top [
            (M X)
            S
          ];
          door = top [
            (M S)
            (M X)
          ];
          twice = top [
            (M X)
            (M X)
          ];
          container = attrs [
            (gt.attrsOf S)
            (gt.attrsOf (M X))
          ];
          # the door record as the element of a nixpkgs container, alone, beside the plain container and
          # twice
          npAttrs = attrs [ (np.attrsOf (M X)) ];
          npAttrsBeside = attrs [
            (np.attrsOf S)
            (np.attrsOf (M X))
          ];
          npAttrsTwice = attrs [
            (np.attrsOf (M X))
            (np.attrsOf (M X))
          ];
          npList = list [ (np.listOf (M X)) ];
          npListBeside = list [
            (np.listOf S)
            (np.listOf (M X))
          ];
          npListTwice = list [
            (np.listOf (M X))
            (np.listOf (M X))
          ];
        };
        every = {
          beside = enforced;
          after = enforced;
          door = enforced;
          twice = enforced;
          container = enforced;
          npAttrs = enforced;
          npAttrsBeside = enforced;
          npAttrsTwice = enforced;
          npList = enforced;
          npListBeside = enforced;
          npListTwice = enforced;
        };
      in
      {
        expr = builtins.mapAttrs (_: at) forms;
        expected = {
          wrapper = every;
          adHoc = every;
        };
      };
    # a checked nixpkgs submodule as a member of gen's `either` or `oneOf`: the union merges its members
    # pairwise, and a member's join at a module set is met as every step's is (den-hoag-78k2m), raw and
    # through `mkOptionType`, beside the plain submodule's union, after it, and twice
    test-a-checked-nixpkgs-submodule-as-a-union-member-is-enforced-redeclared =
      let
        M = gm.mkOptionType;
        # no default: a module set declared twice (see the cell above)
        S = np.submodule { options.a = nixpkgsLib.mkOption { type = np.int; }; };
        forms = {
          wrapper = np.addCheck S not7;
          adHoc = S // {
            check = v: S.check v && not7 v;
          };
        };
        unions = {
          left = m: gt.either m gt.str;
          right = m: gt.either gt.str m;
          oneOf =
            m:
            gt.oneOf [
              gt.str
              m
            ];
        };
        at =
          X:
          builtins.mapAttrs (_: u: {
            beside = top [
              (u S)
              (u X)
            ];
            after = top [
              (u X)
              (u S)
            ];
            twice = top [
              (u X)
              (u X)
            ];
            door = top [
              (u (M S))
              (u (M X))
            ];
          }) unions;
        every = {
          beside = enforced;
          after = enforced;
          twice = enforced;
          door = enforced;
        };
        members = {
          left = every;
          right = every;
          oneOf = every;
        };
      in
      {
        expr = builtins.mapAttrs (_: at) forms;
        expected = {
          wrapper = members;
          adHoc = members;
        };
      };
    # the same record as the `freeformType` of two modules: the freeform plane's steps are met too, though
    # the declaration list's fixup does not run there (den-hoag-78k2m)
    test-a-checked-nixpkgs-submodule-as-a-freeformType-of-two-modules-is-enforced =
      let
        S = np.submodule { options.a = nixpkgsLib.mkOption { type = np.int; }; };
        free =
          X: v:
          let
            x =
              (gm.evalModuleTree { } [
                { freeformType = gt.lazyAttrsOf X; }
                { freeformType = gt.lazyAttrsOf X; }
                { x = v; }
              ]).config.x;
          in
          (tryEval (deepSeq x x)).success;
        at = X: {
          ok = free X { a = 1; };
          bad = free X { a = 7; };
        };
      in
      {
        expr = {
          wrapper = at (np.addCheck S not7);
          adHoc = at (
            S
            // {
              check = v: S.check v && not7 v;
            }
          );
        };
        expected = {
          wrapper = enforced;
          adHoc = enforced;
        };
      };
    # a nixpkgs container through `mkOptionType` whose element is a checked submodule, declared alone:
    # the mount rebuilds the container with its element's check carried, not its root's alone
    test-a-checked-nixpkgs-submodule-element-through-mkOptionType-is-enforced-alone =
      let
        M = gm.mkOptionType;
      in
      {
        expr = {
          attrsOf = attrs [ (M (np.attrsOf W)) ];
          lazyAttrsOf = attrs [ (M (np.lazyAttrsOf W)) ];
          listOf = list [ (M (np.listOf W)) ];
        };
        expected = {
          attrsOf = enforced;
          lazyAttrsOf = enforced;
          listOf = enforced;
        };
      };
    # a module set copied with a `// { verify }`, raw, through either door, and through `defineType` over
    # the copy: no rebuild reads `verify`, so it rides on the redeclaration as a check does, twice,
    # beside the uncopied record and below a gen container
    test-a-verify-copy-of-a-nixpkgs-submodule-is-enforced-redeclared =
      let
        S = np.submodule { options.a = nixpkgsLib.mkOption { type = np.int; }; };
        copy = R: R // { verify = v: if (v.a or 0) == 7 then "a is 7" else null; };
        doors = {
          raw = d: d;
          defineType = gt.defineType;
          mkOptionType = gm.mkOptionType;
        };
        at = R: V: {
          twice = top [
            V
            V
          ];
          besideItsRecord = top [
            R
            V
          ];
          container = attrs [
            (gt.attrsOf V)
            (gt.attrsOf V)
          ];
        };
        every = {
          twice = enforced;
          besideItsRecord = enforced;
          container = enforced;
        };
      in
      {
        expr = builtins.mapAttrs (_: D: at (D S) (copy (D S))) doors // {
          definedCopy = at S (gt.defineType (copy S));
        };
        expected = {
          raw = every;
          defineType = every;
          mkOptionType = every;
          definedCopy = every;
        };
      };
    # a verify copy is read once, on the MERGED value: split across two definitions of a redeclared option, the
    # value it admits is served, and the one definition it rejects alone is refused (a reading per definition
    # would refuse both)
    test-a-verify-copy-of-a-nixpkgs-submodule-reads-the-merged-value-redeclared =
      let
        o = nixpkgsLib.mkOption {
          type = np.int;
          default = 0;
        };
        A = np.submodule { options.a = o; };
        B = np.submodule { options.b = o; };
        X = A // {
          verify = v: if (v.a or 0) == 1 && (v.b or 0) == 0 then "a = 1 needs b" else null;
        };
        read =
          ts: w: rd: ds:
          let
            x =
              rd
                (gm.evalModuleTree { } (
                  map (t: { options.x = gm.mkOption { type = t; }; }) ts ++ map (d: { x = w d; }) ds
                )).config.x;
            r = tryEval (deepSeq x x);
          in
          if r.success then r.value else "REFUSED";
        at = D: {
          Tb = {
            ts = [
              B
              (D X)
            ];
            w = v: v;
            rd = x: x;
          };
          bT = {
            ts = [
              (D X)
              B
            ];
            w = v: v;
            rd = x: x;
          };
          cTb = {
            ts = [
              (gt.attrsOf B)
              (gt.attrsOf (D X))
            ];
            w = v: { k = v; };
            rd = x: x.k;
          };
        };
        both = c: {
          split = read c.ts c.w c.rd [
            { a = 1; }
            { b = 1; }
          ];
          alone = read c.ts c.w c.rd [ { a = 1; } ];
        };
        doors = {
          raw = d: d;
          defineType = gt.defineType;
          mkOptionType = gm.mkOptionType;
        };
        every = {
          split = {
            a = 1;
            b = 1;
          };
          alone = "REFUSED";
        };
      in
      {
        expr = builtins.mapAttrs (_: D: builtins.mapAttrs (_: both) (at D)) doors;
        expected = builtins.mapAttrs (_: _: {
          Tb = every;
          bT = every;
          cTb = every;
        }) doors;
      };
    test-a-foreign-wrapper-below-a-gen-container-beside-its-gen-twin-is-enforced = {
      expr = nested [
        (gt.attrsOf (gt.attrsOf W))
        (gt.attrsOf (gt.attrsOf G))
      ];
      expected = enforced;
    };
    # a nixpkgs module set through the published `defineType`, declared as an option INSIDE a nixpkgs submodule:
    # the host's evaluation rebuilds it (`fixupOptionType`, and `typeMerge` declared twice), so the record the door
    # returns answers its rebuilds with its own check and `verify` carried (`interface.rebuildClosed`), the check at
    # every depth; the copy declared through the door twice, and a container over the checked set. A `verify` is
    # read on the merged value: two definitions whose merge it admits are served
    test-a-nixpkgs-module-set-through-defineType-keeps-its-checks-inside-a-nixpkgs-submodule =
      let
        S = np.submodule { options.a = nixpkgsLib.mkOption { type = np.int; }; };
        inside =
          ts: ok: bad:
          both [
            (np.submodule { imports = map (t: { options.y = nixpkgsLib.mkOption { type = t; }; }) ts; })
          ] { y = ok; } { y = bad; };
        D = gt.defineType;
        at = X: {
          once = inside [ X ] { a = 1; } { a = 7; };
          twice = inside [
            X
            X
          ] { a = 1; } { a = 7; };
        };
        S2 = np.submodule {
          options.a = nixpkgsLib.mkOption {
            type = np.int;
            default = 0;
          };
          options.b = nixpkgsLib.mkOption {
            type = np.int;
            default = 0;
          };
        };
        needsB = S2 // {
          verify = v: if v.a == 7 && v.b == 0 then "a is 7 and b is unset" else null;
        };
        merged =
          defs:
          (tryEval (
            deepSeq ((gm.evalModuleTree { } (
              [
                {
                  options.x = gm.mkOption {
                    type = np.submodule {
                      options.y = nixpkgsLib.mkOption { type = D needsB; };
                    };
                  };
                }
              ]
              ++ map (d: { x.y = d; }) defs
            )).config.x
            ) true
          )).success;
      in
      {
        expr = {
          check = at (D (D S // { check = v: S.check v && not7 v; }));
          wrapper = at (D (np.addCheck S not7));
          verify = at (D (S // { verify = v: if (v.a or 0) == 7 then "a is 7" else null; }));
          element = {
            once = inside [ (D (np.listOf (np.addCheck S not7))) ] [ { a = 1; } ] [ { a = 7; } ];
          };
          verifyMerged = {
            admitted = merged [
              { a = 7; }
              { b = 1; }
            ];
            rejected = merged [ { a = 7; } ];
          };
        };
        expected = {
          check = {
            once = enforced;
            twice = enforced;
          };
          wrapper = {
            once = enforced;
            twice = enforced;
          };
          verify = {
            once = enforced;
            twice = enforced;
          };
          element.once = enforced;
          verifyMerged = {
            admitted = true;
            rejected = false;
          };
        };
      };
    # a nixpkgs `addCheck` over a submodule copied with its module set nulled (`// { getSubModules = null; }`)
    # states no module set while its functor, merge and rebuild are the submodule's: beside the plain submodule
    # through `mkOptionType`, whose completion retains the author's relation, and as a gen container's element
    # beside the plain one, the join is the submodule's and drops the check unless it is carried
    test-a-nulled-copy-of-a-checked-nixpkgs-submodule-beside-its-twin-is-enforced =
      let
        S = np.submodule { options.a = nixpkgsLib.mkOption { type = np.int; }; };
        Z = np.addCheck S not7 // {
          getSubModules = null;
        };
        M = gm.mkOptionType;
      in
      {
        expr = {
          beside = top [
            S
            (M Z)
          ];
          after = top [
            (M Z)
            S
          ];
          element = attrs [
            (gt.attrsOf S)
            (gt.attrsOf Z)
          ];
          elementDoor = attrs [
            (gt.attrsOf S)
            (gt.attrsOf (M Z))
          ];
        };
        expected = {
          beside = enforced;
          after = enforced;
          element = enforced;
          elementDoor = enforced;
        };
      };
  };
}
