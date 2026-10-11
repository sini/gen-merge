# A check-rewritten gen nesting record through the `mkOptionType` door crosses as itself (den-hoag-n8ssa).
#
# `np.addCheck G p` and `G // { check }` over a gen nesting type G state a check on a record that is still
# a nesting record (`nests` + `mergeDefs.threaded`). `mkOptionType` of one used to rebuild it with the
# CALLED fold, which drops the threaded sibling, so below a gen union the member's called fold refused a
# value every declared check admits ("its called `mergeDefs' does not evaluate the nested tree"). It now
# crosses as itself, as `defineType` and the raw door return it, and the engine's `threadedAs` carries
# the rewritten check onto the threaded fold. Each served cell is paired with its refusing twin: a door
# that served everything would pass the first alone.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  gt = gm.types;
  np = nixpkgsLib.types;
  ac = np.addCheck;
  inherit (builtins) deepSeq tryEval mapAttrs;

  not1 = v: !(builtins.isAttrs v) || (v.a or 0) != 1;
  g = gt.submodule { options.a = gm.mkOption { type = gt.int; }; };
  # the two spellings of a rewritten check over a gen nesting constructor
  formsOf = G: {
    add = ac G not1;
    ovr = G // {
      check = x: G.check x && not1 x;
    };
  };
  forms = formsOf g;
  psBase = gm.partialSubmodule {
    options.a = gm.mkOption { type = gt.int; };
  };
  psForms = formsOf psBase;
  # the union shapes of the defect, each holding the door record D, with how a value sits in it
  shapes = {
    eL = {
      u = D: gt.either D gt.str;
      w = v: v;
    };
    o3 = {
      u =
        D:
        gt.oneOf [
          gt.int
          gt.str
          D
        ];
      w = v: v;
    };
    nE = {
      u = D: gt.nullOr (gt.either D gt.str);
      w = v: v;
    };
    cE = {
      u = D: gt.attrsOf (gt.either D gt.str);
      w = v: { k = v; };
    };
    # a nixpkgs union at the root holding the door record
    npE = {
      u = D: np.either D np.str;
      w = v: v;
    };
  };

  read =
    mods: pick:
    let
      v = pick (gm.evalModuleTree { } mods).config;
      o = tryEval (deepSeq v v);
    in
    if o.success then o.value else "REFUSED";
  decl = T: { options.x = gm.mkOption { type = T; }; };
  # declared once (a), twice (LL), and twice inside a gen submodule host (hLL)
  arrs = {
    a =
      T: v:
      read [
        (decl T)
        { x = v; }
      ] (c: c.x);
    LL =
      T: v:
      read [
        (decl T)
        (decl T)
        { x = v; }
      ] (c: c.x);
    hLL =
      T: v:
      read [
        {
          options.x = gm.mkOption {
            type = gt.submodule {
              imports = [
                { options.s = gm.mkOption { type = T; }; }
                { options.s = gm.mkOption { type = T; }; }
              ];
            };
          };
        }
        { x.s = v; }
      ] (c: c.x.s);
  };
  ok = {
    a = 2;
  };
  bad = {
    a = 1;
  };
  tableOf =
    forms: door: v:
    mapAttrs (_: X: mapAttrs (_: s: mapAttrs (_: arr: arr (s.u (door X)) (s.w v)) arrs) shapes) forms;
  table = tableOf forms;
  # what each form × shape × arrangement must read: the value the shape holds, or the refusal
  every = f: mapAttrs (_: _: mapAttrs (_: s: mapAttrs (_: _: f s) arrs) shapes) forms;
in
{
  flake.tests.check-rewritten-nesting-door = {
    # The value every declared check admits is served, at the value it holds in the shape.
    test-a-check-rewritten-gen-submodule-through-the-door-is-served-in-a-union = {
      expr = table gm.mkOptionType ok;
      expected = every (s: s.w ok);
    };
    # The value the rewritten check rejects stays refused in every shape. The carried check refuses
    # it, so a door that crossed the record without it would serve it.
    test-a-rejected-value-stays-refused-through-the-door = {
      expr = table gm.mkOptionType bad;
      expected = every (_: "REFUSED");
    };
    # The door agrees with the raw record and with `defineType` on both values.
    test-the-door-agrees-with-the-raw-record-and-define-type = {
      expr = {
        ok = table gm.mkOptionType ok;
        bad = table gm.mkOptionType bad;
      };
      expected = {
        ok = table (X: X) ok;
        bad = table (X: X) bad;
      };
    };
    test-define-type-agrees-with-the-raw-record = {
      expr = table gt.defineType ok;
      expected = table (X: X) ok;
    };

    # `partialSubmodule` is a gen nesting constructor the same arm reaches: served, refused, and agreeing
    # with the raw record, in every shape.
    test-a-check-rewritten-partial-submodule-through-the-door-is-served-in-a-union = {
      expr = tableOf psForms gm.mkOptionType ok;
      expected = every (s: s.w ok);
    };
    test-a-rejected-partial-submodule-stays-refused-through-the-door = {
      expr = tableOf psForms gm.mkOptionType bad;
      expected = every (_: "REFUSED");
    };

    # The door threads: the nested tree under the record is a child of the one evaluation that holds
    # it, so each module defining the option is read at its own declaration address (a second root
    # would read none), as the raw record and `defineType` read it.
    test-the-door-threads-the-nested-tree-of-a-check-rewritten-record =
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
        rec' = gt.defineType (
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
        X = ac rec' (_: true);
        decl = {
          _file = "/decl.nix";
          options.s = gm.mkOption { type = gt.either X gt.str; };
        };
        at =
          door:
          let
            T = gt.either (door X) gt.str;
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
      in
      {
        expr = {
          door = at gm.mkOptionType;
          raw = at (x: x);
          defineType = at gt.defineType;
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
            door = addrs;
            raw = addrs;
            defineType = addrs;
          };
      };

    # A submodule that reads its own config, or its position's name, folds through the threaded sibling.
    test-a-config-reading-submodule-through-the-door-is-served-in-a-union =
      let
        own = gt.submodule (
          { config, ... }:
          {
            options.a = gm.mkOption { type = gt.int; };
            options.b = gm.mkOption {
              type = gt.int;
              default = config.a + 10;
            };
          }
        );
        named = gt.submodule (
          { name, ... }:
          {
            options.a = gm.mkOption { type = gt.int; };
            options.n = gm.mkOption {
              type = gt.str;
              default = name;
            };
          }
        );
      in
      {
        expr = {
          own = arrs.a (gt.either (gm.mkOptionType (ac own not1)) gt.str) ok;
          name = arrs.a (gt.attrsOf (gt.either (gm.mkOptionType (ac named not1)) gt.str)) { k = ok; };
        };
        expected = {
          own = {
            a = 2;
            b = 12;
          };
          name = {
            k = {
              a = 2;
              n = "k";
            };
          };
        };
      };
    # The reach is the check-rewritten nesting record. A coercedTo over the union is p06j3's refusal
    # and stays one; the unrewritten door image keeps serving by the exported `merge`, so it is not
    # a threaded record, and the rewritten one is (the sibling is what the arm keeps).
    test-the-arm-does-not-reach-coercedTo-or-the-unrewritten-image = {
      expr = {
        unrewrittenKeepsCopiedFold = (gm.mkOptionType g) ? mergeDefs.threaded;
        rewrittenCrossesAsItself = (gm.mkOptionType forms.add) ? mergeDefs.threaded;
        coercedTo = arrs.a (np.coercedTo np.int (x: { a = x; }) (
          np.either (gm.mkOptionType forms.add) np.str
        )) ok;
        unrewritten = arrs.a (gt.either (gm.mkOptionType g) gt.str) ok;
      };
      expected = {
        unrewrittenKeepsCopiedFold = false;
        rewrittenCrossesAsItself = true;
        coercedTo = "REFUSED";
        unrewritten = ok;
      };
    };
  };
}
