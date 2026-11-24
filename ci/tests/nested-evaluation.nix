# THE BRIDGE CHILD, RETAINED (den-hoag-t5ndo 1b): `evalNested type loc defs` returns `{ config; provenance; }`
# of the one root evaluation a nesting type's exported `merge` makes over `defs` at `loc`, taken through the
# record's own fold. Every value cell reads the route beside the exported `merge` (the value path a foreign engine
# reads) in the same run. The refusal TEXTS are `ci/tests-error.nix` `nested-evaluation`; the one-evaluation count
# (G3) is the spy's, `ci/tests-process.nix` block `engine-option-names`.
#
# The forged records (G4) are `//` copies of an instance-shaped type and a sibling with one more option (`o9`), so
# `o9` in a served value says whose child was evaluated. The route reads its child off the record's `merge` (a nesting
# export's `merge` carries the evaluation it makes), so every forged record is served the child its `merge` serves,
# by construction and with no field compared: the contract each G4 cell pins is route = merge. F2, F3, F5 and F6 were
# served the wrong child at the first prototype (gen-merge 4a59420); every guard that refused a forgery by comparing
# fields (the completion, the `merge` slot, `rewritesCheck`) split by evaluator on a re-celled field
# (den-hoag-t5ndo spec v1), and a position witness is ruled out (den-hoag-oeygp criterion (4)). Red at gen-merge main
# 38dff3c: `evalNested` is absent.
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
    # G4: the forged records. `route` is whose child the route served, `merge` whose the exported `merge` serves:
    # equal on every record whose `merge` is a nesting export's
    test-g4-F0-intact-record-is-served = {
      expr = row forged.F0;
      expected = {
        route = "user";
        merge = "user";
      };
    };
    test-g4-F1-fold-carried-from-sibling-served-its-merges-child = {
      expr = row forged.F1;
      expected = {
        route = "user";
        merge = "user";
      };
    };
    test-g4-F2-fold-and-tree-carried-from-sibling-served-its-merges-child = {
      expr = row forged.F2;
      expected = {
        route = "user";
        merge = "user";
      };
    };
    test-g4-F3-sibling-with-merge-removed-served-its-merges-child = {
      expr = row forged.F3;
      expected = {
        route = "sibling";
        merge = "sibling";
      };
    };
    test-g4-F4-merge-new-literal-served-its-merges-child = {
      expr = row forged.F4;
      expected = {
        route = "sibling";
        merge = "sibling";
      };
    };
    test-g4-F5-merge-slot-carried-from-sibling-served-its-merges-child = {
      expr = row forged.F5;
      expected = {
        route = "sibling";
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
    test-g4-F7-threaded-rewritten-inside-fold-served-its-merges-child = {
      expr = row forged.F7;
      expected = {
        route = "user";
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
        (userType // { check = _: false; })
      ];
      expected = [
        false
        false
        false
        false
        true
        true
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
    # Under arm (ii) (den-hoag-t5ndo spec v3) provenance is read THROUGH the merge's own application, out of the config
    # its function returns, so it is as strict as that config's WHNF: a freeform poisoned sibling, which the config's
    # WHNF forces (`recursiveUpdate freeform declared`), throws on a provenance read too. Arms (i) and (iii) read
    # provenance beside the function and serve it (`prov = [ true true ]`)
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
          false
          false
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
    # G4c (spec v2): EVERY OUTCOME IS THE SAME ON Nix, Determinate AND Lix, because no field is compared. A record
    # holding its own `merge`, fold or tree in a new cell (a `//` restatement, a variable, `inherit`, a `mapAttrs`
    # copy) is served the user's child, as its `merge` serves it. Red at gen-merge a21b489: Lix serves each, Nix and
    # Determinate refuse it (the `merge` slot and the completion compared by `==`).
    test-g4c-restated-fields-served-as-the-merge-serves = {
      expr = map (x: row x) [
        (userType // { merge = userType.merge; })
        (
          let
            m = userType.merge;
          in
          userType // { merge = m; }
        )
        (userType // { inherit (userType) merge; })
        (builtins.mapAttrs (_: v: v) userType)
        (userType // { mergeDefs = builtins.mapAttrs (_: v: v) userType.mergeDefs; })
      ];
      expected = builtins.genList (_: {
        route = "user";
        merge = "user";
      }) 5;
    };
    # A `check` carried from a sibling is applied, and accepts what the user's own accepts. Red at a21b489 on Nix and
    # Determinate (`rewritesCheck` compares it by `==`): refused there, served on Lix.
    test-g4c-check-carried-from-a-sibling-is-applied = {
      expr = row (userType // builtins.intersectAttrs { check = null; } siblingType);
      expected = {
        route = "user";
        merge = "user";
      };
    };
    # A `check` carried from a completion over ANOTHER domain is applied: it serves a definition inside that domain
    # and refuses one outside it, by name, where gen's engine refuses it too. Red at a21b489: refused ×3 inside.
    test-g4c-check-carried-from-another-domain-is-applied = {
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
    # C2 (spec v1 gate): a self-knot (F6's shape over the record itself) with no `admits`, or no `check`, is served
    # its `merge`'s child, catchably everywhere; the route applies a `check` only where the record states one
    test-g4c-self-knots-without-admits-or-check-served = {
      expr =
        let
          knot =
            drop:
            let
              x = removeAttrs userType drop // {
                mergeDefs = userType.mergeDefs // {
                  completed = x;
                };
              };
            in
            x;
        in
        map (drop: row (knot drop)) [
          [ ]
          [ "admits" ]
          [ "check" ]
        ];
      expected = builtins.genList (_: {
        route = "user";
        merge = "user";
      }) 3;
    };
    # A door's rebuild of a record (`mkOptionType` over an admits copy, and over nixpkgs' `addCheck` twin) is served
    # what its rebuilt `merge` serves, identically ×3. Under a21b489's route with its check conjunct deleted, Lix
    # serves both and Nix and Determinate refuse them.
    test-g4c-door-rebuilds-served-as-the-merge-serves = {
      expr =
        let
          n = v: builtins.isAttrs v && (v.shell or "") != "fish";
        in
        map (x: row x) [
          (gm.mkOptionType (userType // { admits = n; }))
          (gm.mkOptionType (nl.types.addCheck userType n))
        ];
      expected = builtins.genList (_: {
        route = "user";
        merge = "user";
      }) 2;
    };
    # The library's own `merge` record edited: its applied function replaced (the route takes the child THROUGH that
    # function, so it answers no evaluation and is refused by name), or its evaluation replaced (the function reads
    # it, so route and merge serve the same child). Red at the route that reads `nestedEvaluation` directly: the
    # first is served the user's child where its `merge` serves the sibling's, the second the sibling's where its
    # `merge` serves the user's.
    test-g4c-merge-record-edited-served-as-the-merge-serves-or-refused = {
      expr =
        if builtins.isAttrs userType.merge then
          [
            (row (
              userType
              // {
                merge = userType.merge // {
                  __functor = _: siblingType.merge;
                };
              }
            ))
            (row (
              userType
              // {
                merge = userType.merge // {
                  inherit (siblingType.merge) nestedEvaluation;
                };
              }
            ))
          ]
        else
          "the merge is not a functor record";
      expected = [
        {
          route = "refused";
          merge = "sibling";
        }
        {
          route = "sibling";
          merge = "sibling";
        }
      ];
    };
    # An evaluation's own type (`evalModuleTree … .type`), whose nesting fold reads its child's undeclared report
    # beside `config`: the route serves its `merge`'s value, and refuses an undeclared definition by name as its
    # `merge` does. Red at gen-merge a21b489: the route aborts uncatchably on all three evaluators
    # (`attribute 'undeclared' missing`; its accessor answered the child under `config` alone).
    test-g4c-an-evaluations-own-type = {
      expr =
        let
          T =
            (gm.evalModuleTree { } [
              {
                options.a = mkOption {
                  type = t.str;
                  default = "x";
                };
              }
            ]).type;
          d = [
            {
              file = "d.nix";
              value.a = "y";
            }
          ];
          u = [
            {
              file = "d.nix";
              value.zz = 1;
            }
          ];
        in
        [
          ((route T [ "x" ] d).config == T.merge [ "x" ] d)
          (ok (route T [ "x" ] u).config)
          (ok (T.merge [ "x" ] u))
        ];
      expected = [
        true
        false
        false
      ];
    };
    # L7 (spec v3): hand edits of the library's own `merge` record, `userType // { merge = userType.merge // e; }`. The
    # v2 gate's seven rows (its inst/l7x.nix): the route refuses by name, or serves what the edited `merge` serves.
    # Arm (i) serves L7c / L7e / L7f silently (route != merge) and aborts uncatchably on L7g; arm (iii) serves six of
    # the seven silently.
    test-l7-merge-record-edits-refused-or-served-as-the-merge = {
      expr =
        let
          m = userType.merge;
          ed = e: userType // { merge = m // e; };
          c =
            self: l: d:
            (self.nestedEvaluation l d).config;
          rows = [
            (ed { __functor = _: siblingType.merge; })
            (ed { inherit (siblingType.merge) nestedEvaluation; })
            (ed {
              __functor =
                self: l: d:
                c self l d // { shell = "ninety-nine"; };
            })
            (ed {
              __functor =
                self: l: d:
                builtins.removeAttrs (c self l d) [ "shell" ];
            })
            (ed {
              __functor =
                self: l: d:
                let
                  x = c self l d;
                in
                x // { b = x.shell; };
            })
            (ed {
              __functor =
                self: l: d:
                let
                  x = c self l d;
                in
                builtins.seq x.shell x;
            })
            (ed {
              __functor =
                self: l: d:
                c self l (map (x: x // { value.shell = "five"; }) d);
            })
          ];
          read =
            x:
            let
              r = val (route x loc reg).config;
              v = val (x.merge loc reg);
            in
            if r == "refused" then
              "refused"
            else if r == v then
              "same"
            else
              "DIFFERENT";
        in
        if builtins.isAttrs m then map read rows else "the merge is not a functor record";
      expected = [
        "refused"
        "same"
        "same"
        "same"
        "same"
        "same"
        "same"
      ];
    };
    # L7, arm (ii)'s own residue, PINNED NOT ENDORSED: a function observing its config's key set sees the carried key
    # (L7h), and a function forging the key with another evaluation (L7l) is served its config minus the key with
    # that evaluation's provenance. Each reads `DIFFERENT` (route != merge) on all three evaluators. Mapping every
    # value, or rebuilding the config from named fields, drops or rebinds the key and is refused by name (L7j, L7k).
    test-l7-arm-ii-residue-pinned = {
      expr =
        let
          m = userType.merge;
          ed = e: userType // { merge = m // e; };
          c =
            self: l: d:
            (self.nestedEvaluation l d).config;
          read =
            x:
            let
              r = val (route x loc reg).config;
              v = val (x.merge loc reg);
            in
            if r == "refused" then
              "refused"
            else if r == v then
              "same"
            else
              "DIFFERENT";
        in
        if builtins.isAttrs m then
          map read [
            (ed {
              __functor =
                self: l: d:
                let
                  x = c self l d;
                in
                x // { n = builtins.length (builtins.attrNames x); };
            })
            (ed {
              __functor =
                self: l: d:
                c self l d // { __evalNestedRecord = siblingType.merge.nestedEvaluation l d; };
            })
            (ed {
              __functor =
                self: l: d:
                builtins.mapAttrs (_: _: 0) (c self l d);
            })
            (ed {
              __functor =
                self: l: d:
                let
                  x = c self l d;
                in
                {
                  inherit (x) shell;
                };
            })
          ]
        else
          "the merge is not a functor record";
      expected = [
        "DIFFERENT"
        "DIFFERENT"
        "refused"
        "refused"
      ];
    };
    # D1 (Artemis outcome gate 01M86X5M; the door's own split is den-hoag-06010): the published `mkOptionType` door picks
    # its arm by `rewritesCheck` (a function `!=`), so for a record carrying a sibling's `check` it hands Lix a checked
    # import fold (`{ __functor; completed; unchecked; }`, the record's own merge riding on it as `unchecked`) and Nix and
    # Determinate a gen export. The route reads the evaluation either carries, so it serves the user's child, as the merge
    # does, on every evaluator. Red at 78a5b68 / a279ad9 without the `unchecked` read: served / served / refused.
    test-d1-door-split-route-serves-as-the-merge-serves = {
      expr =
        let
          x = gm.mkOptionType (userType // builtins.intersectAttrs { check = null; } siblingType);
          r = val (route x loc reg).config;
        in
        {
          invariant = r == "refused" || r == val (x.merge loc reg);
          route = who (route x loc reg).config;
          merge = who (x.merge loc reg);
        };
      expected = {
        invariant = true;
        route = "user";
        merge = "user";
      };
    };
  };
}
