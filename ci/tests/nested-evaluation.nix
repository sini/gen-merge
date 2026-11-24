# THE BRIDGE CHILD, RETAINED (den-hoag-t5ndo 1b): `evalNested type loc defs` returns `{ config; provenance; }`
# of the one root evaluation a nesting type's exported `merge` makes over `defs` at `loc`, taken through the
# record's own fold. Every value cell reads the route beside the exported `merge` (the value path a foreign engine
# reads) in the same run. The refusal TEXTS are `ci/tests-error.nix` `nested-evaluation`; the one-evaluation count
# (G3) is the spy's, `ci/tests-process.nix` block `engine-option-names`.
#
# The forged records (G4) are `//` copies of an instance-shaped type and a sibling with one more option (`o9`), so
# `o9` in a served value says whose child was evaluated. F2, F3, F5 and F6 are served the wrong child at the first
# prototype (gen-merge 4a59420, a position witness on `merge` and the child built from the completion): F2, F3 and F5
# are refused now, by the `merge` slot compared by pointer, and F6 forges its own completion and is served the
# child its own fold makes, which is what its exported `merge` serves. F7's refusal is the fold-identity conjunct's
# alone. Red at gen-merge main 38dff3c: `evalNested` is absent.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  t = gm.types;
  nl = nixpkgsLib;
  inherit (gm) mkOption;
  ok = e: (builtins.tryEval (builtins.deepSeq e e)).success;
  # the served value, or "refused" where the read throws catchably
  val =
    e:
    let
      r = builtins.tryEval (builtins.deepSeq e e);
    in
    if r.success then r.value else "refused";
  # an instance-shaped type: gen-schema's non-strict instance (`refusingSubmodule` with its three keys, a freeform
  # `attrsOf anything`), two declared options, and a type-own module defining `groups` at the band of an entry
  inst =
    mods:
    gm.refusingSubmodule null [ "config" "options" "prefix" ] (
      [
        {
          config._module.freeformType = t.attrsOf t.anything;
          options.shell = mkOption {
            type = t.str;
            default = "bash";
          };
          options.groups = mkOption {
            type = t.listOf t.str;
            default = [ ];
          };
        }
      ]
      ++ mods
    );
  schemaMod = {
    _file = "schema.nix";
    groups = [ "base" ];
  };
  userType = inst [ schemaMod ];
  siblingType = inst [
    schemaMod
    {
      options.o9 = mkOption {
        type = t.int;
        default = 9;
      };
    }
  ];
  loc = [
    "users"
    "tux"
  ];
  reg = [
    {
      file = "reg.nix";
      value = {
        shell = "zsh";
        groups = [ "wheel" ];
        ff = gm.mkForce 1;
        ff2.x = 1;
      };
    }
    {
      file = "reg2.nix";
      value = {
        ff = 2;
        ff2.y = gm.mkBefore 3;
      };
    }
  ];
  route =
    ty: l: ds:
    gm.evalNested ty l ds;
  # whose child a read served: "refused", "sibling" (it carries `o9`) or "user"
  who =
    e:
    let
      v = val e;
    in
    if v == "refused" then
      v
    else if v ? o9 then
      "sibling"
    else
      "user";
  row = X: {
    route = who (route X loc reg).config;
    merge = who (X.merge loc reg);
  };
  forged = {
    F0 = userType;
    F1 = userType // {
      inherit (siblingType) mergeDefs;
    };
    F2 = userType // {
      inherit (siblingType) mergeDefs nests;
    };
    F3 = siblingType // removeAttrs userType [ "merge" ];
    F4 = userType // {
      merge = siblingType.merge;
    };
    F5 = userType // builtins.intersectAttrs { merge = null; } siblingType;
    F6 =
      let
        x = siblingType // {
          inherit (userType) nests;
          mergeDefs = siblingType.mergeDefs // {
            completed = x;
          };
        };
      in
      x;
    F7 = userType // {
      mergeDefs = userType.mergeDefs // {
        inherit (siblingType.mergeDefs) threaded;
      };
    };
  };
  plainSub = t.submodule [
    {
      options.a = mkOption {
        type = t.str;
        default = "d";
      };
    }
  ];
  doorSub = gm.submodule [
    {
      options.a = mkOption {
        type = t.str;
        default = "d";
      };
    }
  ];
  subDefs = [
    {
      file = "s.nix";
      value.a = "x";
    }
  ];
  hostDefs = [
    {
      file = "host.nix";
      value = {
        shell = "fish";
        groups = [ "video" ];
        ff = 7;
      };
    }
  ];
  # nixpkgs' engine mounting the type under its own `attrsOf`, as den's host relation does. Its element is the
  # record nixpkgs' fix-up kept (`substSubModules`), whose fold orders the type's own modules first, where a hand
  # call of either library's submodule `merge` orders the definitions first; the route is read over that record
  npHost1 = nl.evalModules {
    modules = [
      {
        options.users = nl.mkOption {
          type = nl.types.attrsOf userType;
          default = { };
        };
      }
      {
        _file = "host.nix";
        users.tux = {
          shell = "fish";
          groups = [ "video" ];
          ff = 7;
        };
      }
    ];
  };
  npKept = npHost1.options.users.type.nestedTypes.elemType;
  poison = [
    {
      file = "p.nix";
      value = {
        shell = "zsh";
        groups = throw "POISON-declared-sibling";
      };
    }
  ];
  poisonFF = [
    {
      file = "p.nix";
      value = {
        shell = "zsh";
        ffPoison = throw "POISON-freeform-sibling";
      };
    }
  ];
  # G8: N declarations of one option, each a gen submodule (raw or door) adding one option, so the declarations
  # JOIN; every order, on nixpkgs' engine and on gen's. "same": the route served the engine's value
  subN =
    ctor: n:
    builtins.genList (
      i:
      ctor [
        {
          options."o${toString i}" = mkOption {
            type = t.int;
            default = i;
          };
        }
      ]
    ) n;
  perms =
    xs:
    if xs == [ ] then
      [ [ ] ]
    else
      builtins.concatMap (x: map (p: [ x ] ++ p) (perms (nl.remove x xs))) xs;
  nDefs = [
    {
      file = "host.nix";
      value.o0 = 10;
    }
  ];
  npHost =
    ts:
    nl.evalModules {
      modules = map (ty: { options.u = nl.mkOption { type = ty; }; }) ts ++ [
        {
          _file = "host.nix";
          u.o0 = 10;
        }
      ];
    };
  genHost =
    ts:
    gm.evalModuleTree { } (
      map (ty: { options.u = mkOption { type = ty; }; }) ts
      ++ [
        {
          _file = "host.nix";
          u.o0 = 10;
        }
      ]
    );
  tri =
    h:
    let
      v = val h.config.u;
      r = val (route h.options.u.type [ "u" ] nDefs).config;
    in
    if v == "refused" then
      "engine-refuses"
    else if r == "refused" then
      "refused"
    else if r == v then
      "same"
    else
      "DIFFERENT";
  nCell =
    ctor: engine: n:
    let
      ts = subN ctor n;
    in
    map (o: tri (engine (map (builtins.elemAt ts) o))) (perms (nl.range 0 (n - 1)));
  sameAll = n: builtins.genList (_: "same") (builtins.foldl' builtins.mul 1 (nl.range 1 n));
  npPartner = nl.types.submodule {
    options.np = nl.mkOption {
      type = nl.types.int;
      default = 1;
    };
  };
  joinGen = builtins.head (subN t.submodule 1);
in
{
  flake.tests.nested-evaluation = {
    # G1: the route's config is the value path's
    test-g1-instance-type-config-is-the-exported-merge = {
      expr = (route userType loc reg).config == userType.merge loc reg;
      expected = true;
    };
    test-g1-door-submodule = {
      expr = (route doorSub [ "s" ] subDefs).config == doorSub.merge [ "s" ] subDefs;
      expected = true;
    };
    test-g1-raw-submodule = {
      expr = (route plainSub [ "s" ] subDefs).config == plainSub.merge [ "s" ] subDefs;
      expected = true;
    };
    test-g1-no-definitions = {
      expr = (route userType loc [ ]).config == userType.merge loc [ ];
      expected = true;
    };
    test-g1-nixpkgs-engine-mount = {
      expr = (route npKept loc hostDefs).config == npHost1.config.users.tux;
      expected = true;
    };
    # G6: exactly the two projections, and the child's own provenance (the type-own `groups` beside the entry's)
    test-g6-published-key-set = {
      expr = builtins.attrNames (route userType loc reg);
      expected = [
        "config"
        "provenance"
      ];
    };
    test-g6-provenance-is-the-childs = {
      expr =
        let
          r = route userType loc reg;
        in
        {
          files = map (w: w.file) r.provenance.groups.winners;
          inherit (r.config) groups;
        };
      expected = {
        files = [
          "reg.nix"
          "schema.nix"
        ];
        groups = [
          "wheel"
          "base"
        ];
      };
    };
    # G4: the forged records. `route` is whose child the route served, `merge` whose the exported `merge` serves;
    # where both serve they serve the same child
    test-g4-F0-intact-record-is-served = {
      expr = row forged.F0;
      expected = {
        route = "user";
        merge = "user";
      };
    };
    test-g4-F1-fold-carried-from-sibling-refused = {
      expr = row forged.F1;
      expected = {
        route = "refused";
        merge = "user";
      };
    };
    test-g4-F2-fold-and-tree-carried-from-sibling-refused = {
      expr = row forged.F2;
      expected = {
        route = "refused";
        merge = "user";
      };
    };
    test-g4-F3-sibling-with-merge-removed-refused = {
      expr = row forged.F3;
      expected = {
        route = "refused";
        merge = "sibling";
      };
    };
    test-g4-F4-merge-new-literal-refused = {
      expr = row forged.F4;
      expected = {
        route = "refused";
        merge = "sibling";
      };
    };
    test-g4-F5-merge-slot-carried-from-sibling-refused = {
      expr = row forged.F5;
      expected = {
        route = "refused";
        merge = "sibling";
      };
    };
    test-g4-F6-self-knot-completion-served-its-own-folds-child = {
      expr = row forged.F6;
      expected = {
        route = "sibling";
        merge = "sibling";
      };
    };
    test-g4-F7-threaded-rewritten-inside-fold-refused = {
      expr = row forged.F7;
      expected = {
        route = "refused";
        merge = "user";
      };
    };
    test-g4-sibling-control-is-served-its-own-child = {
      expr = who (route siblingType loc reg).config;
      expected = "sibling";
    };
    test-g4-other-shapes-refused = {
      expr = map (ty: ok (route ty loc reg)) [
        t.str
        (t.attrsOf plainSub)
        null
        (userType // { merge = _: _: { shell = "over"; }; })
        (userType // { check = _: true; })
        (userType // { inherit (plainSub) mergeDefs; })
      ];
      expected = [
        false
        false
        false
        false
        false
        false
      ];
    };
    # G7: demand. A declared poisoned sibling: the route and the value path agree on what serves, and the live
    # control reads the poison on both. A freeform poisoned sibling: both throw on `config.shell`; provenance serves
    test-g7-declared-poison = {
      expr = {
        shell = [
          (ok (route userType loc poison).config.shell)
          (ok (userType.merge loc poison).shell)
        ];
        keys = [
          (ok (builtins.attrNames (route userType loc poison).config))
          (ok (builtins.attrNames (userType.merge loc poison)))
        ];
        prov = [
          (ok (route userType loc poison).provenance.shell.priority)
          (ok (route userType loc poison).provenance.shell.winners)
          (ok (builtins.attrNames (route userType loc poison).provenance))
        ];
        control = [
          (ok (route userType loc poison).config.groups)
          (ok (userType.merge loc poison).groups)
        ];
      };
      expected = {
        shell = [
          true
          true
        ];
        keys = [
          true
          true
        ];
        prov = [
          true
          true
          true
        ];
        control = [
          false
          false
        ];
      };
    };
    test-g7-freeform-poison = {
      expr = {
        shell = [
          (ok (route userType loc poisonFF).config.shell)
          (ok (userType.merge loc poisonFF).shell)
        ];
        prov = [
          (ok (route userType loc poisonFF).provenance.shell.priority)
          (ok (route userType loc poisonFF).provenance.ffPoison.defs)
        ];
      };
      expected = {
        shell = [
          false
          false
        ];
        prov = [
          true
          true
        ];
      };
    };
    # G8: N = 2, 3, 4 joined declarations, every order, raw and door, nixpkgs' engine and gen's
    test-g8-np-raw = {
      expr = map (nCell t.submodule npHost) [
        2
        3
        4
      ];
      expected = map sameAll [
        2
        3
        4
      ];
    };
    test-g8-np-door = {
      expr = map (nCell gm.submodule npHost) [
        2
        3
        4
      ];
      expected = map sameAll [
        2
        3
        4
      ];
    };
    test-g8-gen-raw = {
      expr = map (nCell t.submodule genHost) [
        2
        3
        4
      ];
      expected = map sameAll [
        2
        3
        4
      ];
    };
    test-g8-gen-door = {
      expr = map (nCell gm.submodule genHost) [
        2
        3
        4
      ];
      expected = map sameAll [
        2
        3
        4
      ];
    };
    # G8b (L1): a gen submodule joined with a nixpkgs `submodule` is nixpkgs' own evaluation, refused by name
    test-g8b-foreign-partner-refused-both-orders = {
      expr = map (o: tri (npHost o)) [
        [
          joinGen
          npPartner
        ]
        [
          npPartner
          joinGen
        ]
      ];
      expected = [
        "refused"
        "refused"
      ];
    };
    # G4b (spec v1): EVERY GUARD ANSWERS ALIKE on Nix, Determinate and Lix. A record holding its completion's own
    # value in a NEW slot (a `//` restatement, a `mapAttrs` copy) is told from its completion only by `==`, which
    # on Lix compares the function a slot holds and on Nix and Determinate the slot. Red at gen-merge a21b489: Lix
    # serves each restated record (`user`), Nix and Determinate refuse it.
    test-g4b-merge-restated-in-a-new-slot-refused = {
      expr = map (x: who (route x loc reg).config) [
        (userType // { merge = userType.merge; })
        (
          let
            m = userType.merge;
          in
          userType // { merge = m; }
        )
        (builtins.mapAttrs (_: v: v) userType)
      ];
      expected = [
        "refused"
        "refused"
        "refused"
      ];
    };
    test-g4b-fold-and-tree-restated-refused = {
      expr = map (x: who (route x loc reg).config) [
        (userType // { mergeDefs = builtins.mapAttrs (_: v: v) userType.mergeDefs; })
        (userType // { nests = builtins.mapAttrs (_: v: v) userType.nests; })
      ];
      expected = [
        "refused"
        "refused"
      ];
    };
    # the restated records' exported `merge` serves the user's child on every evaluator: the refusal is the route's
    test-g4b-restated-records-merge-serves-the-user = {
      expr = map (x: who (x.merge loc reg)) [
        (userType // { merge = userType.merge; })
        (builtins.mapAttrs (_: v: v) userType)
        (userType // { mergeDefs = builtins.mapAttrs (_: v: v) userType.mergeDefs; })
        (userType // { nests = builtins.mapAttrs (_: v: v) userType.nests; })
      ];
      expected = [
        "user"
        "user"
        "user"
        "user"
      ];
    };
    # A `check` carried from a sibling is the very function its completion's is (every submodule's is one), so it
    # is applied, not compared, and the record is served the child its `merge` serves. Red at a21b489: Nix and
    # Determinate refuse it (`rewritesCheck` compares the check by `==`), Lix serves it.
    test-g4b-check-carried-from-a-sibling-is-applied = {
      expr =
        let
          x = userType // builtins.intersectAttrs { check = null; } siblingType;
        in
        [
          (who (route x loc reg).config)
          (who (x.merge loc reg))
        ];
      expected = [
        "user"
        "user"
      ];
    };
    # A `check` carried from a completion over ANOTHER domain sits where every completion binds one, and refuses
    # what that domain refuses: applied, it serves a definition inside that domain and refuses one outside it, by
    # name, where gen's engine refuses it too. Red at a21b489: the first read is refused on every evaluator.
    test-g4b-check-carried-from-another-domain-is-applied = {
      expr =
        let
          d = t.defineType (siblingType // { admits = v: builtins.isAttrs v && (v.shell or "") != "fish"; });
          x = userType // builtins.intersectAttrs { check = null; } d;
          fish = [
            {
              file = "f.nix";
              value.shell = "fish";
            }
          ];
        in
        [
          (who (route x loc reg).config)
          (who (route x loc fish).config)
          (who
            (gm.evalModuleTree { } [
              { options.u = mkOption { type = x; }; }
              { u.shell = "fish"; }
            ]).config.u
          )
        ];
      expected = [
        "user"
        "refused"
        "refused"
      ];
    };
    # A door's rebuild of a record (`mkOptionType` over an admits copy, and over nixpkgs' `addCheck` twin) binds
    # `merge` and `check` where the door binds them: refused by position on every evaluator. Under the route at
    # a21b489 with its check conjunct deleted, Lix serves both and Nix and Determinate refuse them.
    test-g4b-door-rebuilds-refused = {
      expr =
        let
          n = v: builtins.isAttrs v && (v.shell or "") != "fish";
        in
        map (x: who (route x loc reg).config) [
          (gm.mkOptionType (userType // { admits = n; }))
          (gm.mkOptionType (nl.types.addCheck userType n))
        ];
      expected = [
        "refused"
        "refused"
      ];
    };
  };
}
