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
  # den-hoag-2632d: the completed records whose fold carries its completion record from its constructor (the five
  # constants and `deferredModule`) or from the door that completed it (`submodule`), and `raw`, a leaf
  records = {
    submodule = {
      t = gt.submodule {
        options.a = gm.mkOption {
          type = gt.int;
          default = 0;
        };
        options.b = gm.mkOption {
          type = gt.int;
          default = 0;
        };
      };
      n = noB;
      ok = {
        a = 1;
      };
    };
    deferredModule = {
      t = gt.deferredModule;
      n = builtins.isAttrs;
      ok = { };
    };
    attrs = {
      t = gt.attrs;
      n = noB;
      ok = {
        a = 1;
      };
    };
    anything = {
      t = gt.anything;
      n = builtins.isInt;
      ok = 1;
    };
    raw = {
      t = gt.raw;
      n = builtins.isInt;
      ok = 1;
    };
    unspecified = {
      t = gt.unspecified;
      n = builtins.isInt;
      ok = 1;
    };
    optionType = {
      t = gt.optionType;
      n = v: (v.name or null) == gt.int.name;
      ok = gt.int;
      view = v: v.name;
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
    # the same for the records whose fold carries its completion from its constructor or its first door, and for `raw`;
    # read against nixpkgs' `addCheck` of the record through the same door (the copy's twin), since a `deferredModule`
    # copy declared twice is refused through `defineType` as its twin is
    test-the-value-an-admits-rewrite-of-a-record-keeps-is-served-as-its-add-check-twin-serves-it = {
      expr = grid records (
        C: door: eng: k:
        (C.view or (v: v)) (run eng k (door (C.t // { admits = C.n; })) C.ok)
      );
      expected = grid records (
        C: door: eng: k:
        (C.view or (v: v)) (run eng k (door (nl.types.addCheck C.t C.n)) C.ok)
      );
    };
    # a door ties a nesting fold once: a doored `//` copy of a submodule keeps the fold of the record its constructor
    # completed, so its `admits` is judged against that record's, and two doored copies share one fold record, which
    # `==` reads without walking the cycle through `completed` (a door re-tying the fold on every copy hands each copy a
    # fresh fold record whose other fields are the constructor's, and a structural `==` of two such copies overflows the
    # stack, uncatchably)
    test-a-door-keeps-the-completion-a-nesting-fold-already-holds = {
      expr =
        let
          s = records.submodule.t;
        in
        {
          constructor = s.mergeDefs.completed ? z;
          doored = (gt.defineType (s // { z = 1; })).mergeDefs.completed ? z;
          imported =
            let
              r = gm.mkOptionType (s // { z = 1; });
            in
            r.mergeDefs ? completed && r.mergeDefs.completed ? z;
        };
      expected = {
        constructor = false;
        doored = false;
        imported = false;
      };
    };
    # a self-referential submodule copy narrowing its `admits` is enforced at its own nested position, and the plain
    # one reads as before (a door reading the completion stamp of a nesting record forces what it is still building)
    test-a-self-referential-submodule-admits-copy-is-enforced-where-it-nests = {
      expr =
        let
          sub =
            copy:
            let
              s = gt.defineType (
                gt.submodule {
                  options.n = gm.mkOption {
                    type = gt.nullOr s;
                    default = null;
                  };
                  options.k = gm.mkOption {
                    type = gt.int;
                    default = 0;
                  };
                }
                // (if copy then { admits = v: builtins.isAttrs v && !(v ? k && v.k == 9); } else { })
              );
            in
            s;
        in
        nl.genAttrs [ "gen" "np" ] (
          eng: nl.genAttrs [ "plain" "copy" ] (c: run eng 1 (sub (c == "copy")) { n.k = 9; })
        );
      expected = nl.genAttrs [ "gen" "np" ] (_: {
        plain = {
          k = 0;
          n = {
            k = 9;
            n = null;
          };
        };
        copy = "REFUSED";
      });
    };
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
