# THE WALK'S RE-MINT KEEPS THE RECORD'S OWN FIELDS (den-hoag-f5twc, den-hoag-ofo98). Where gen's fix-up of a foreign
# root re-carries a container's element, it re-mints the container by its constructor over that element. The record
# it replaces is the one nixpkgs' fold reads there, so the re-mint keeps that record's fields that carry no check:
# `emptyValue` (an option nothing defined), and `deprecationMessage` with the `name` nixpkgs' warning prints.
#
# The shape: a nixpkgs `attrTag { a = submodule; b = B; }` whose tag `a` states a module set, so a fix-up runs, and
# whose tag `b` states none (`getSubModules = null`), so nixpkgs keeps `b` as written. Columns: `ge` gen's engine
# over the raw record, `gd` gen's engine through `defineType`, `np` nixpkgs' engine through `defineType`, `tw`
# nixpkgs' engine over the raw record (no gen code). A refusal reads "<R>".
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  try =
    e:
    let
      r = builtins.tryEval (builtins.deepSeq e e);
    in
    if r.success then r.value else "<R>";
  # the shapes over a nixpkgs library `lib` (one whose `warn` a cell replaces, for the deprecation cells)
  shapes =
    lib:
    let
      t = lib.types;
    in
    rec {
      inherit t;
      sub = t.submodule {
        options.a = lib.mkOption {
          type = t.str;
          default = "x";
        };
      };
      L = t.listOf sub;
      X = L // {
        emptyValue.value = "EV";
      };
      nulled = x: t.lazyAttrsOf x // { getSubModules = null; };
      B = nulled X;
      tag =
        b:
        t.attrTag {
          a = lib.mkOption { type = sub; };
          b = lib.mkOption { type = b; };
        };
      # a root whose own `substSubModules` hands tag `b` back as `b'`: a rebuild that is not nixpkgs' `attrTag`'s
      handsBack =
        T: b':
        let
          r = tag T;
        in
        r
        // {
          substSubModules =
            m:
            let
              x = r.substSubModules m;
            in
            t.attrTag {
              a = lib.mkOption { type = x.nestedTypes.a.type; };
              b = lib.mkOption { type = b'; };
            };
        };
      mods =
        roots: def: map (ty: { options.o = lib.mkOption { type = ty; }; }) roots ++ [ { config.o = def; } ];
      onNp = roots: def: (lib.evalModules { modules = mods roots def; }).config.o;
      onGen = roots: def: (gm.evalModuleTree { } (mods roots def)).config.o;
    };
  s = shapes nixpkgsLib;
  inherit (s) t;
  cols =
    {
      roots,
      def,
      at,
    }:
    let
      d = map gm.types.defineType roots;
    in
    {
      ge = try (at (s.onGen roots def));
      gd = try (at (s.onGen d def));
      np = try (at (s.onNp d def));
      tw = try (at (s.onNp roots def));
    };
  four = v: {
    ge = v;
    gd = v;
    np = v;
    tw = v;
  };
  pick =
    names: c:
    builtins.listToAttrs (
      map (n: {
        name = n;
        value = c.${n};
      }) names
    );
  emptyRead = {
    def.b.k = nixpkgsLib.mkIf false [ ];
    at = c: c.b.k;
  };
  kept = d: {
    def.b.k = d;
    at = c: c.b.k;
  };
  served = [ { a = "x"; } ];
  # nixpkgs' engine with its `warn` replaced: a warning whose text `p` matches refuses the read, so "<R>" is the
  # warning fired and a value (or "absent", a strict container's discharged key) is no such warning
  warnedOn =
    p:
    let
      lib' = nixpkgsLib.extend (_: _: { warn = msg: v: if p msg then throw "warned" else v; });
      w = shapes lib';
    in
    which: {
      np = try ((w.onNp [ (gm.types.defineType (w.tag (which w))) ] emptyRead.def).b.k or "absent");
      tw = try ((w.onNp [ (w.tag (which w)) ] emptyRead.def).b.k or "absent");
    };
  has = nixpkgsLib.hasInfix;
  deprecated = has "is deprecated.";
in
{
  flake.tests.re-mint-keeps-written-fields = {
    # the kept tag's `emptyValue` is read below it, served or refused
    test-kept-tag-emptyValue-value-is-served = {
      expr = cols (emptyRead // { roots = [ (s.tag s.B) ]; });
      expected = four "EV";
    };
    test-kept-tag-emptyValue-none-refuses = {
      expr = cols (emptyRead // { roots = [ (s.tag (s.nulled (s.L // { emptyValue = { }; }))) ]; });
      expected = four "<R>";
    };
    # the re-mint copies the slots and forces none: a thrown phrase, on the tag or on its handed-back element
    test-kept-tag-forces-no-description = {
      expr = pick [ "ge" "np" "tw" ] (
        cols (emptyRead // { roots = [ (s.tag (s.B // { description = throw "forced"; })) ]; })
      );
      expected = {
        ge = "EV";
        np = "EV";
        tw = "EV";
      };
    };
    test-handed-back-tag-forces-no-nested-description = {
      expr = pick [ "ge" "np" "tw" ] (
        cols (
          emptyRead
          // {
            roots = [
              (s.handsBack s.B (
                s.B
                // {
                  nestedTypes.elemType = s.X // {
                    description = throw "forced";
                  };
                }
              ))
            ];
          }
        )
      );
      expected = {
        ge = "EV";
        np = "EV";
        tw = "EV";
      };
    };
    # a tag handed back with a lambda `merge` and fresh `check`/`merge` slots reads alike on every evaluator
    test-handed-back-lambda-merge-tag-reads-emptyValue =
      let
        M = s.B // {
          merge = loc: defs: s.B.merge loc defs;
        };
      in
      {
        expr = {
          sel = cols (
            emptyRead
            // {
              roots = [
                (s.handsBack M (
                  M
                  // {
                    check = M.check;
                    merge = M.merge;
                  }
                ))
              ];
            }
          );
          as = cols (emptyRead // { roots = [ (s.tag M) ]; });
        };
        expected = {
          sel = four "EV";
          as = four "EV";
        };
      };
    # the root's own rebuild erases the tag's check, so the walk runs, and the tag's `emptyValue` is still the one read
    test-erasing-rebuild-tag-reads-emptyValue =
      let
        root = ev: s.handsBack (t.addCheck (s.nulled (s.L // ev)) (v: !(v ? bad))) (s.nulled (s.L // ev));
      in
      {
        expr = {
          value = cols (emptyRead // { roots = [ (root { emptyValue.value = "EV"; }) ]; });
          none = cols (emptyRead // { roots = [ (root { emptyValue = { }; }) ]; });
        };
        expected = {
          value = four "EV";
          none = four "<R>";
        };
      };
    # ...and the check that rebuild erased is enforced; nixpkgs' twin, past its own erasing rebuild, serves
    test-erasing-rebuild-tag-check-is-enforced =
      let
        B0 = s.nulled s.L;
        c = v: !(v ? bad);
        strip = s.handsBack (t.addCheck B0 c) B0;
        plain = s.tag (t.addCheck B0 c);
        at = cc: cc;
      in
      {
        expr = {
          stripRej = pick [ "ge" "gd" "np" ] (cols {
            roots = [ strip ];
            def.b.bad = [ ];
            inherit at;
          });
          stripPass = cols {
            roots = [ strip ];
            def.b.ok = [ { } ];
            inherit at;
          };
          plainRej = cols {
            roots = [ plain ];
            def.b.bad = [ ];
            inherit at;
          };
        };
        expected = {
          stripRej = {
            ge = "<R>";
            gd = "<R>";
            np = "<R>";
          };
          stripPass = four { b.ok = served; };
          plainRej = four "<R>";
        };
      };
    # a rebuild keeping `check` and `merge` by `//` but erasing the element from `functor.payload` and `nestedTypes`
    test-element-erasing-rebuild-check-is-enforced =
      let
        Lc = t.addCheck s.L (v: builtins.length v != 2);
        Bc = s.nulled Lc;
        erased = Bc // {
          functor = Bc.functor // {
            payload = Bc.functor.payload // {
              elemType = s.L;
            };
          };
          nestedTypes = Bc.nestedTypes // {
            elemType = s.L;
          };
        };
        root = s.handsBack Bc erased;
      in
      {
        expr = {
          rej = pick [ "ge" "gd" "np" ] (
            cols (
              kept [
                { }
                { }
              ]
              // {
                roots = [ root ];
              }
            )
          );
          ok = cols (kept [ { } ] // { roots = [ root ]; });
        };
        expected = {
          rej = {
            ge = "<R>";
            gd = "<R>";
            np = "<R>";
          };
          ok = four served;
        };
      };
    # a kept tag's `verify` is enforced through the door, and through gen's engine raw
    test-kept-tag-verify-is-enforced =
      let
        root = v: s.tag (s.nulled s.L // { verify = v; });
        go = v: pick [ "ge" "np" ] (cols (kept [ { } ] // { roots = [ (root v) ]; }));
      in
      {
        expr = {
          rej = go (_: "planted");
          acc = go (_: null);
        };
        expected = {
          rej = {
            ge = "<R>";
            np = "<R>";
          };
          acc = {
            ge = served;
            np = served;
          };
        };
      };
    # a leaf check at the tag, declared twice through the door: the join drops it and the walk restores it
    test-twice-declared-tag-leaf-check-is-enforced =
      let
        root = s.tag (t.addCheck t.int (v: v != 1));
        np = d: try (s.onNp [ (gm.types.defineType root) (gm.types.defineType root) ] { b = d; }).b;
      in
      {
        expr = {
          rej = np 1;
          pass = np 2;
        };
        expected = {
          rej = "<R>";
          pass = 2;
        };
      };
    # nixpkgs' engine warns for a kept tag's `deprecationMessage`, naming the record's own type
    test-kept-tag-deprecation-warns = {
      expr = warnedOn (has "is deprecated. DEPMARK") (w: w.B // { deprecationMessage = "DEPMARK"; });
      expected = {
        np = "<R>";
        tw = "<R>";
      };
    };
    test-kept-loaOf-tag-warning-names-loaOf = {
      expr = {
        named = warnedOn (has "The type `types.loaOf'") (w: w.t.loaOf w.X // { getSubModules = null; });
        any = warnedOn deprecated (w: w.t.loaOf w.X // { getSubModules = null; });
      };
      expected = {
        named = {
          np = "<R>";
          tw = "<R>";
        };
        any = {
          np = "<R>";
          tw = "<R>";
        };
      };
    };
    # controls: a tag stating a module set is rebuilt by nixpkgs, which drops the message, so neither engine warns
    test-control-rebuilt-tag-deprecation-is-dropped = {
      expr = {
        loaOf = warnedOn deprecated (w: w.t.loaOf w.X);
        lazyAttrsOf = warnedOn deprecated (w: w.t.lazyAttrsOf w.X // { deprecationMessage = "DEPMARK"; });
      };
      expected = {
        loaOf = {
          np = "absent";
          tw = "absent";
        };
        lazyAttrsOf = {
          np = [ ];
          tw = [ ];
        };
      };
    };
  };
}
