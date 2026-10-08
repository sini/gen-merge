# The fixtures of `ci/tests/foreign-split-def-record.nix` and its `tests-error.nix` group
# (den-hoag-j5gfg). Two shapes, both on the gen-merge engine with nixpkgs types entering as foreign
# values:
#
# `readFiles pos rd kind`: a merge that READS its definitions' `file`, and what it observed.
#   kind  nest : coercedTo str _ (over (listOf (lazyAttrsOf (gen attrsOf sub)))), the threaded chain;
#                `over` adds to each element a key named by the reader's view of its definition
#         nid  : nest with an identity `over` (the control)
#   rd    obs (typeOf), sort (by `file`), cmp (`== "zz"`), str ("${file}"), dk (attribute names),
#         grp (`file` as an attribute name, through groupBy)
#   pos   top, gatt (gen attrsOf), natt (nixpkgs attrsOf), nlst (nixpkgs listOf), wrap (a step-free
#         coercedTo), nsub (nixpkgs submodule), ffree (freeformType)
#   Two modules define the option, `_file = "zz"` (a = 1) then `"aa"` (a = 2).
#
# `addresses pos mg rd order`: the 8hlo3 declaration address of each element below a foreign level.
#   pos   glist (gen listOf E, the control), nest (coercedTo str _ (over (listOf (lazyAttrsOf E)))),
#         wlazy (coercedTo str _ (over (lazyAttrsOf E))), ncoatt (coercedTo str _ (nixpkgs attrsOf E)),
#         ncogatt (coercedTo str _ (gen attrsOf E))
#   mg    stock, id, rev, drop, sortf (sort by `file`), grp (group by `file`), dk (keep only
#         `{ file; value; }` records), fileset (an attrset `file` written by the merge)
#   rd    at (each element's tag and `declAt`), val (tags only), atc (whether the `declAt` read
#         succeeds under `tryEval`), has (`d ? declAt`)
#   order ab: kA kB kC, ba: kC kB kA. kA (`zz`, p), kB (`aa`, q), kC (`zz`, r and s through mkMerge):
#         kA and kC share a file, so `file` alone does not identify a definition.
{ genMerge, nixpkgsLib }:
let
  gm = genMerge;
  nl = nixpkgsLib;
  nt = nl.types;
  t = gm.types;
  overWith =
    pre: a:
    a
    // {
      merge = {
        __functor =
          _: loc: defs:
          a.merge loc (pre defs);
        v2 =
          { loc, defs }:
          a.merge.v2 {
            inherit loc;
            defs = pre defs;
          };
      };
      substSubModules = m: overWith pre (a.substSubModules m);
    };
  coerced = nt.coercedTo nt.str (_: throw "unused");
in
{
  readFiles =
    pos: rd: kind:
    let
      R = {
        obs = map (d: builtins.typeOf d.file);
        sort = defs: map (d: d.file) (builtins.sort (a: b: a.file < b.file) defs);
        cmp = map (d: if d.file == "zz" then "eq" else "ne");
        str = map (d: "${d.file}");
        dk = map (d: builtins.concatStringsSep "," (builtins.attrNames d));
        grp =
          defs:
          let
            g = builtins.groupBy (x: x.file) defs;
          in
          map (d: "g" + toString (builtins.length g.${d.file})) defs;
      };
      pre =
        defs:
        let
          o = R.${rd} defs;
        in
        nl.imap0 (
          i: d:
          d
          // {
            value = map (
              x:
              x
              // {
                ${builtins.elemAt o i} = {
                  k.a = 0;
                };
              }
            ) d.value;
          }
        ) (if rd == "sort" then builtins.sort (a: b: a.file < b.file) defs else defs);
      sub = t.submodule [
        {
          options.a = gm.mkOption {
            type = t.int;
            default = 0;
          };
        }
      ];
      T = coerced (
        overWith (if kind == "nid" then (x: x) else pre) (nt.listOf (nt.lazyAttrsOf (t.attrsOf sub)))
      );
      v = n: [ { j.k.a = n; } ];
      P =
        {
          top = {
            t = T;
            d = n: { s = v n; };
            r = c: c.s;
          };
          gatt = {
            t = t.attrsOf T;
            d = n: { s.x = v n; };
            r = c: c.s.x;
          };
          natt = {
            t = nt.attrsOf T;
            d = n: { s.x = v n; };
            r = c: c.s.x;
          };
          nlst = {
            t = nt.listOf T;
            d = n: { s = [ (v n) ]; };
            r = c: builtins.concatLists c.s;
          };
          wrap = {
            t = nt.coercedTo nt.int (_: throw "unused") T;
            d = n: { s = v n; };
            r = c: c.s;
          };
          nsub = {
            t = nt.submodule { options.s = nl.mkOption { type = T; }; };
            d = n: { s.s = v n; };
            r = c: c.s.s;
          };
          ffree = {
            d = n: { s = v n; };
            r = c: c.s;
          };
        }
        .${pos};
      decl =
        if pos == "ffree" then
          { freeformType = nt.lazyAttrsOf T; }
        else
          { options.s = gm.mkOption { type = P.t; }; };
      cfg =
        (gm.evalModuleTree { } [
          decl
          {
            _file = "zz";
            config = P.d 1;
          }
          {
            _file = "aa";
            config = P.d 2;
          }
        ]).config;
    in
    map (e: {
      inherit (e.j.k) a;
      keys = builtins.attrNames e;
      leaves = builtins.mapAttrs (_: y: y.k.a) e;
    }) (P.r cfg);

  addresses =
    pos: mg: rd: order:
    let
      # declaration-address.nix's element type in shape: it records the `declAt` it was handed
      E =
        let
          sub = t.submodule [
            {
              options.tag = gm.mkOption {
                type = t.str;
                default = "";
              };
              options.seen = gm.mkOption {
                type = t.listOf t.anything;
                default = [ ];
              };
            }
          ];
          n = sub.nests;
        in
        t.defineType (
          sub
          // {
            nests = n // {
              entry = d: {
                imports = [ (n.entry { inherit (d) file value; }) ];
                config.seen = [ (if rd == "has" then d ? declAt else d.declAt or null) ];
              };
              declAt = true;
            };
          }
        );
      pre =
        {
          id = d: d;
          rev = nl.reverseList;
          drop = builtins.tail;
          sortf = builtins.sort (a: b: a.file < b.file);
          grp = d: builtins.concatLists (builtins.attrValues (builtins.groupBy (x: x.file) d));
          dk = builtins.filter (
            x:
            builtins.attrNames x == [
              "file"
              "value"
            ]
          );
          fileset = map (
            x:
            x
            // {
              file = {
                f = x.file;
              };
            }
          );
        }
        .${mg};
      over = a: if mg == "stock" then a else overWith pre a;
      keyed = tag: { ${tag} = { inherit tag; }; };
      P =
        {
          glist = {
            t = t.listOf E;
            d = tag: [ { inherit tag; } ];
            r = c: c.xs;
          };
          nest = {
            t = coerced (over (nt.listOf (nt.lazyAttrsOf E)));
            d = tag: [ (keyed tag) ];
            r = c: builtins.concatMap builtins.attrValues c.xs;
          };
          wlazy = {
            t = coerced (over (nt.lazyAttrsOf E));
            d = keyed;
            r = c: builtins.attrValues c.xs;
          };
          ncoatt = {
            t = coerced (nt.attrsOf E);
            d = keyed;
            r = c: builtins.attrValues c.xs;
          };
          ncogatt = {
            t = coerced (t.attrsOf E);
            d = keyed;
            r = c: builtins.attrValues c.xs;
          };
        }
        .${pos};
      defMods = [
        {
          key = "mA";
          _file = "zz";
          config.xs = P.d "p";
        }
        {
          key = "mB";
          _file = "aa";
          config.xs = P.d "q";
        }
        {
          key = "mC";
          _file = "zz";
          config.xs = gm.mkMerge [
            (P.d "r")
            (P.d "s")
          ];
        }
      ];
      cfg =
        (gm.evalModuleTree { } (
          [ { options.xs = gm.mkOption { type = P.t; }; } ]
          ++ (if order == "ba" then nl.reverseList defMods else defMods)
        )).config;
    in
    map (
      e:
      if rd == "val" then
        e.tag
      else if rd == "atc" then
        [
          e.tag
          (builtins.tryEval (builtins.deepSeq e.seen e.seen)).success
        ]
      else
        [
          e.tag
          e.seen
        ]
    ) (P.r cfg);
}
