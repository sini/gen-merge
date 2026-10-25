# A check on a nixpkgs `attrTag` TAG's type is enforced in gen's engine, at every arrangement and depth
# (den-hoag-8pjrq, owner-ruled 2026-10-10 P2 arm (F)).
#
# gen's engine calls `attrTag`'s own merge (`functor.binOp`, which re-merges a redeclared tag through
# `mergeOptionDecls`) and its rebuild (`substSubModules`, which rebuilds each tag over its module set). Both
# drop a wrapper over the tag's type, as nixpkgs' `fixupOptionType` drops one over an option's. The tag's
# option records are carried as an element is (`interface.rebuiltOverAt "options"`, `interface.carriedAtDepth`), and the
# declaration fold meets each held option (`rolesMet`). Each refusal is paired with its passing twin, whose
# value is nixpkgs' own, so a carriage that refused everything would not pass, and neither would one that
# served everything.

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

  sub = np.submodule { options.a = nixpkgsLib.mkOption { type = np.int; }; };
  p = v: !(builtins.isAttrs v) || (v.a or 0) != 1;
  forms = {
    add = np.addCheck sub p;
    ovr = sub // {
      check = x: sub.check x && p x;
    };
    ver = sub // {
      verify = v: if p v then null else "rejected by p";
    };
  };
  tagOf = t: np.attrTag { t = nixpkgsLib.mkOption { type = t; }; };
  read =
    ts: v:
    let
      x =
        (gm.evalModuleTree { } (map (t: { options.x = gm.mkOption { type = t; }; }) ts ++ [ { x = v; } ]))
        .config.x;
      r = tryEval (deepSeq x x);
    in
    if r.success then r.value else "REFUSED";
  # nixpkgs' value for the same definitions over the unchecked declarations
  nixpkgs =
    ts: v:
    (nixpkgsLib.evalModules {
      modules = map (t: { options.x = nixpkgsLib.mkOption { type = t; }; }) ts ++ [ { x = v; } ];
    }).config.x;
  arrangements = x: plain: {
    a = [ x ];
    LL = [
      x
      x
    ];
    TL = [
      plain
      x
    ];
    LT = [
      x
      plain
    ];
  };
  # every arrangement: the rejected value refused, the admitted one nixpkgs' value
  cells =
    mk: wrap: door: s: plain:
    builtins.mapAttrs (_: ts: {
      bad = read ts (wrap {
        a = 1;
      });
      ok =
        read ts (wrap {
          a = 2;
        }) == nixpkgs (map (_: mk plain) ts) (wrap {
          a = 2;
        });
    }) (arrangements (door (mk s)) (mk plain));
  all = {
    bad = "REFUSED";
    ok = true;
  };
  every = {
    a = all;
    LL = all;
    TL = all;
    LT = all;
  };
in
{
  flake.tests.attrtag-tag-carriage = {

    # the scout's twelve (den-hoag-8pjrq evaluation-owner scout): a checked submodule as a tag, raw and
    # through `defineType`, declared alone, twice and beside the plain tag
    test-a-tags-check-is-enforced =
      let
        w = v: { t = v; };
      in
      {
        expr =
          builtins.mapAttrs
            (_: door: builtins.mapAttrs (_: s: cells tagOf w door s sub) { inherit (forms) add ovr; })
            {
              raw = d: d;
              defineType = gt.defineType;
            };
        expected =
          builtins.mapAttrs
            (_: _: {
              add = every;
              ovr = every;
            })
            {
              raw = null;
              defineType = null;
            };
      };

    # the mount (`mkOptionType`, declared alone), a verify copy as the tag, a nixpkgs and a gen container
    # below the tag and above it, and a tag inside a tag: the carriage reads each as an element is read
    test-a-tags-check-is-enforced-at-every-depth = {
      expr = {
        mount = cells tagOf (v: { t = v; }) gm.mkOptionType forms.add sub;
        verifyCopy = cells tagOf (v: { t = v; }) (d: d) forms.ver sub;
        npElementInTag = cells (s: tagOf (np.attrsOf s)) (v: { t.k = v; }) (d: d) forms.add sub;
        genElementInTag = cells (s: tagOf (gt.attrsOf s)) (v: { t.k = v; }) (d: d) forms.add sub;
        tagInNpList = cells (s: np.listOf (tagOf s)) (v: [ { t = v; } ]) (d: d) forms.add sub;
        tagInTag = cells (s: np.attrTag { u = nixpkgsLib.mkOption { type = tagOf s; }; }) (v: {
          u.t = v;
        }) (d: d) forms.add sub;
      };
      expected = {
        mount = every;
        verifyCopy = every;
        npElementInTag = every;
        genElementInTag = every;
        tagInNpList = every;
        tagInTag = every;
      };
    };

    # a `// { verify }` copy of a NON-v2 type (nixpkgs' or a gen container) as the tag, redeclared or beside the plain
    # tag in either order: the verify is read
    # once, on the MERGED value, so two definitions whose merged value it admits are served (nixpkgs' value) and
    # one definition it rejects is refused; a reading per definition refused both
    test-a-non-v2-verify-copy-as-a-tag-reads-the-merged-value =
      let
        forms = {
          lines = {
            s = np.lines // {
              verify = v: if nixpkgsLib.hasInfix "b" v then null else "needs b";
            };
            plain = np.lines;
            split = [
              "a"
              "b"
            ];
            one = "a";
          };
          attrs = {
            s = np.attrs // {
              verify = v: if v ? b then null else "needs b";
            };
            plain = np.attrs;
            split = [
              { a = 1; }
              { b = 1; }
            ];
            one = {
              a = 1;
            };
          };
          # a GEN container copied with a verify: the tag's two declarations are met by the step, which hands the
          # meet the operands without the verify and reads it once on the merged list
          glist = {
            s = gt.listOf gt.int // {
              verify = v: if builtins.length v == 2 then null else "needs two";
            };
            plain = np.listOf np.int;
            split = [
              [ 1 ]
              [ 2 ]
            ];
            one = [ 1 ];
          };
        };
        readAll =
          ts: vs:
          let
            x =
              (gm.evalModuleTree { } (
                map (t: { options.x = gm.mkOption { type = t; }; }) ts ++ map (v: { x.t = v; }) vs
              )).config.x;
            r = tryEval (deepSeq x x);
          in
          if r.success then r.value else "REFUSED";
        nixpkgsAll =
          ts: vs:
          (nixpkgsLib.evalModules {
            modules =
              map (t: { options.x = nixpkgsLib.mkOption { type = t; }; }) ts ++ map (v: { x.t = v; }) vs;
          }).config.x;
        at =
          F: door:
          builtins.mapAttrs
            (_: ts: {
              split = readAll ts F.split == nixpkgsAll (map (_: tagOf F.plain) ts) F.split;
              one = readAll ts [ F.one ];
            })
            {
              LL = [
                (door (tagOf F.s))
                (door (tagOf F.s))
              ];
              TL = [
                (tagOf F.plain)
                (door (tagOf F.s))
              ];
              LT = [
                (door (tagOf F.s))
                (tagOf F.plain)
              ];
            };
        cell = {
          split = true;
          one = "REFUSED";
        };
      in
      {
        expr = builtins.mapAttrs (_: F: {
          raw = at F (d: d);
          defineType = at F gt.defineType;
        }) forms;
        expected = builtins.mapAttrs (_: _: {
          raw = {
            LL = cell;
            TL = cell;
            LT = cell;
          };
          defineType = {
            LL = cell;
            TL = cell;
            LT = cell;
          };
        }) forms;
      };

    # the held-option fast path decides tag-ness by operators alone, so it spells the carried roles' payload keys
    # as literals rather than reading them from `roleSpelling` (a read there costs every foreign rebuild an
    # evaluation the hub bench meters). The spelling is tied to the table here instead: every site that tests a
    # payload for `_type` tests exactly the payload keys `roleSpelling` states, so a role added to the table
    # with a new key reds this cell until each site names it
    test-the-held-option-fast-path-spells-every-carried-roles-payload-key =
      let
        lines = builtins.filter builtins.isString (
          builtins.split "\n" (builtins.readFile ../../lib/interface.nix)
        );
        n = builtins.length lines;
        at = i: builtins.elemAt lines i;
        stated = builtins.sort builtins.lessThan (
          nixpkgsLib.unique (
            builtins.concatMap (
              l:
              let
                m = builtins.match ".*payloadKey = \"([A-Za-z]+)\".*" l;
              in
              if m == null then [ ] else m
            ) lines
          )
        );
        # the keys a site tests: the `? <key>` reads on its line and the three after it
        tested =
          i:
          builtins.sort builtins.lessThan (
            nixpkgsLib.unique (
              builtins.concatMap (
                j:
                builtins.concatMap (x: if builtins.isList x then x else [ ]) (
                  builtins.split "(payload|[^A-Za-z]q) [?] ([A-Za-z_]+)" (at j)
                )
              ) (builtins.genList (k: i + k) (nixpkgsLib.min 4 (n - i)))
            )
          );
        sites = builtins.filter (i: builtins.match ".*(payload|[^A-Za-z]q) [?] _type.*" (at i) != null) (
          builtins.genList (i: i) n
        );
        keysOf =
          i: builtins.filter (k: k != "payload" && k != " q" && k != "(q" && k != "_type") (tested i);
      in
      {
        expr = {
          sites = builtins.length sites;
          each = nixpkgsLib.unique (map keysOf sites);
        };
        expected = {
          sites = 5;
          each = [ stated ];
        };
      };

    # A LEAF tag redeclared is MET (ADR-0039, the meet): `attrTag`'s `binOp` re-merges the tag by nixpkgs'
    # later-operand rule, which drops the check, and nixpkgs serves the rejected value; gen's fold meets it.
    # Declared alone, nixpkgs enforces it too.
    test-a-leaf-tags-check-is-met-redeclared =
      let
        q = v: v != 1;
        leaf = np.addCheck np.int q;
        w = v: { t = v; };
        at =
          ts: v:
          let
            r = read ts (w v);
          in
          if r == "REFUSED" then r else r == nixpkgs (map (_: tagOf np.int) ts) (w v);
      in
      {
        expr = builtins.mapAttrs (_: ts: {
          bad = at ts 1;
          ok = at ts 2;
        }) (arrangements (tagOf leaf) (tagOf np.int));
        expected = every;
      };

    # the same leaf held by a container that crossed `mkOptionType` (den-hoag-8uwxu R3): a tag, a list of tags, a
    # tag in a tag, and a `listOf` and an `attrsOf` element. The door's record keeps its author's relation, whose
    # witness takes the join on names, and the held role is met there as on the raw foreign arm
    test-a-leaf-held-through-mk-option-type-is-met-redeclared =
      let
        q = v: v != 1;
        leaf = np.addCheck np.int q;
        shapes = {
          tag = {
            mk = tagOf;
            w = v: { t = v; };
          };
          listTag = {
            mk = s: np.listOf (tagOf s);
            w = v: [ { t = v; } ];
          };
          tagTag = {
            mk = s: np.attrTag { u = nixpkgsLib.mkOption { type = tagOf s; }; };
            w = v: { u.t = v; };
          };
          list = {
            mk = np.listOf;
            w = v: [ v ];
          };
          attrs = {
            mk = np.attrsOf;
            w = v: { k = v; };
          };
        };
        at =
          s: ts: v:
          let
            r = read ts (s.w v);
          in
          if r == "REFUSED" then r else r == nixpkgs (map (_: s.mk np.int) ts) (s.w v);
      in
      {
        expr = builtins.mapAttrs (
          _: s:
          builtins.mapAttrs (_: ts: {
            bad = at s ts 1;
            ok = at s ts 2;
          }) (arrangements (gm.mkOptionType (s.mk leaf)) (s.mk np.int))
        ) shapes;
        expected = builtins.mapAttrs (_: _: every) shapes;
      };
  };
}
