# nixpkgs' `definition` record (`lib.mkDefinition { file; value; }`, den-hoag-m19bm): the record IS a
# definition, carrying its own file and its own value. nixpkgs unwraps it once, in `mergeDefinitions`'
# `defsNormalized`, right after `dischargeProperties`, so a record is legal under `mkIf` and `mkMerge`;
# below it only the one override level `filterOverrides'` strips is read, and the order pass sorts.
#
# Every parity cell asserts BOTH engines against literal expected values (`parity-surface.nix`'s
# idiom), with the record built by nixpkgs' own constructor, so an upstream change reds on the
# property. Before the definition arm landed, each gen side read the raw record, or a refusal, or
# `<unknown-file>`; the cell comments say which.
{
  genMerge,
  nixpkgsLib,
  prelude,
  ...
}:
let
  gm = genMerge;
  priority = import ../../lib/priority.nix { inherit prelude; };
  np = nixpkgsLib;
  d = file: value: np.mkDefinition { inherit file value; };

  gmP = {
    inherit (gm)
      mkOption
      mkIf
      mkMerge
      mkForce
      mkDefault
      mkBefore
      types
      ;
  };
  npP = {
    inherit (np)
      mkOption
      mkIf
      mkMerge
      mkForce
      mkDefault
      mkBefore
      types
      ;
  };
  both = fx: read: {
    gen = read (gm.evalModuleTree { } (fx gmP));
    nixpkgs = read (np.evalModules { modules = fx npP; });
  };
  x = r: r.config.x;
  opt = type: P: { options.x = P.mkOption { type = type P; }; };
  refuses = v: !(builtins.tryEval (builtins.deepSeq v v)).success;
  # The discharge's three spellings over records and their wrappers (`priority.nix`'s twins).
  twinFixtures = [
    (d "/r/a.nix" "a")
    (gm.mkIf true (d "/r/a.nix" "b"))
    (gm.mkMerge [
      "c"
      (d "/r/a.nix" (gm.mkForce "d"))
    ])
    (d "/r/a.nix" (gm.mkBefore "e"))
  ];
  vp = map (x: {
    inherit (x) value priority;
  });
  # A record as a whole submodule ELEMENT, where nixpkgs aborts uncatchably (as for the whole value
  # below): gen serves the checked element, and its planted twin (`y = "s"` on `int`) refuses.
  # gen's own containers and nixpkgs' containers over a gen submodule (the threaded fold) alike.
  sub = gm.types.submodule { options.y = gm.mkOption { type = gm.types.int; }; };
  element =
    type: read: v:
    let
      x =
        read
          (gm.evalModuleTree { } [
            { options.a = gm.mkOption { inherit type; }; }
            { config.a = v; }
          ]).config.a;
      r = builtins.tryEval (builtins.deepSeq x x);
    in
    if r.success then r.value else "refused";
  servesChecked = type: read: wrap: {
    serves = element type read (wrap (d "/r/a.nix" { y = 3; }));
    planted = element type read (wrap (d "/r/a.nix" { y = "s"; }));
  };
  inAttrs = r: { k = r; };
  readAttrs = a: a.k.y;
  readList = a: (builtins.head a).y;
  checked = {
    serves = 3;
    planted = "refused";
  };
in
{
  flake.tests.definition-record = {
    # Before: gen served the record itself, `{ _type = "definition"; file; value; }`.
    test-a-record-is-its-value = {
      expr = both (P: [
        { options.x = P.mkOption { }; }
        { config.x = d "/r/other.nix" true; }
      ]) x;
      expected = {
        gen = true;
        nixpkgs = true;
      };
    };
    # Before: refused, `not of the expected type` (the record reached `bool`).
    test-a-record-under-mkIf-is-its-value = {
      expr = both (P: [
        (opt (T: T.types.bool) P)
        { config.x = P.mkIf true (d "/r/other.nix" true); }
      ]) x;
      expected = {
        gen = true;
        nixpkgs = true;
      };
    };
    # Before: refused, `not of the expected type`.
    test-records-under-mkMerge-are-two-definitions = {
      expr = both (P: [
        (opt (T: T.types.listOf T.types.int) P)
        {
          config.x = P.mkMerge [
            (d "/r/a.nix" [ 1 ])
            (d "/r/b.nix" [ 2 ])
          ];
        }
      ]) x;
      expected = {
        gen = [
          1
          2
        ];
        nixpkgs = [
          1
          2
        ];
      };
    };
    # The one override level below a record is read. Before: refused.
    test-a-record-value-mkForce-wins = {
      expr = both (P: [
        (opt (T: T.types.bool) P)
        { config.x = d "/r/other.nix" (P.mkForce true); }
        { config.x = false; }
      ]) x;
      expected = {
        gen = true;
        nixpkgs = true;
      };
    };
    # And the order pass sorts a record's order marker. Before: refused.
    test-a-record-value-mkBefore-is-sorted = {
      expr = both (P: [
        (opt (T: T.types.listOf T.types.int) P)
        { config.x = [ 2 ]; }
        { config.x = d "/r/other.nix" (P.mkBefore [ 1 ]); }
      ]) x;
      expected = {
        gen = [
          1
          2
        ];
        nixpkgs = [
          1
          2
        ];
      };
    };
    # The record's file replaces the enclosing module's. Before: gen read `<unknown-file>`.
    test-a-record-names-its-own-file = {
      expr = both (P: [
        (opt (T: T.types.bool) P)
        { config.x = d "/r/other.nix" true; }
      ]) (r: r.options.x.files);
      expected = {
        gen = [ "/r/other.nix" ];
        nixpkgs = [ "/r/other.nix" ];
      };
    };
    # CONTROL: a plain definition names its module's `_file`, before and after.
    test-control-a-plain-definition-names-its-module-file = {
      expr = both (P: [
        (opt (T: T.types.bool) P)
        {
          _file = "/r/other.nix";
          config.x = true;
        }
      ]) (r: r.options.x.files);
      expected = {
        gen = [ "/r/other.nix" ];
        nixpkgs = [ "/r/other.nix" ];
      };
    };
    # Every fold that discharges reads the record: an element, a submodule option, a container's
    # whole value, a module argument. Before: refused (checked types) or the raw record.
    test-a-record-in-a-list-element = {
      expr = both (P: [
        (opt (T: T.types.listOf T.types.bool) P)
        { config.x = [ (d "/r/other.nix" true) ]; }
      ]) x;
      expected = {
        gen = [ true ];
        nixpkgs = [ true ];
      };
    };
    test-a-record-in-an-attrsOf-element = {
      expr = both (P: [
        (opt (T: T.types.attrsOf T.types.bool) P)
        { config.x.k = d "/r/other.nix" true; }
      ]) x;
      expected = {
        gen.k = true;
        nixpkgs.k = true;
      };
    };
    test-a-record-in-a-submodule-option = {
      expr = both (P: [
        (opt (T: T.types.submodule { options.y = T.mkOption { type = T.types.bool; }; }) P)
        { config.x.y = d "/r/other.nix" true; }
      ]) (r: r.config.x.y);
      expected = {
        gen = true;
        nixpkgs = true;
      };
    };
    test-a-record-as-an-attrsOf-submodule-value = {
      expr = both (P: [
        (opt (
          T: T.types.attrsOf (T.types.submodule { options.y = T.mkOption { type = T.types.bool; }; })
        ) P)
        { config.x = d "/r/other.nix" { k.y = true; }; }
      ]) (r: r.config.x.k.y);
      expected = {
        gen = true;
        nixpkgs = true;
      };
    };
    test-a-record-as-a-module-argument = {
      expr = both (P: [
        { options.x = P.mkOption { }; }
        { config._module.args.foo = d "/r/other.nix" 5; }
        (
          { foo, ... }:
          {
            config.x = foo;
          }
        )
      ]) x;
      expected = {
        gen = 5;
        nixpkgs = 5;
      };
    };
    # A record as a whole `submodule` value: nixpkgs aborts uncatchably here (its submodule merge
    # destructures `{ file, value }` and meets the record's `_type`), so only gen is asserted. Serving
    # is bounded by correctness (ADR-0039): the served value is checked, and the planted twin below,
    # whose value the declared check rejects, refuses.
    test-a-record-as-a-submodule-value-serves = {
      expr =
        (gm.evalModuleTree { } [
          (opt (T: T.types.submodule { options.y = T.mkOption { type = T.types.bool; }; }) gmP)
          { config.x = d "/r/other.nix" { y = true; }; }
        ]).config.x.y;
      expected = true;
    };
    test-control-a-record-as-a-submodule-value-is-checked = {
      expr =
        refuses
          (gm.evalModuleTree { } [
            (opt (T: T.types.submodule { options.y = T.mkOption { type = T.types.bool; }; }) gmP)
            { config.x = d "/r/other.nix" { y = 5; }; }
          ]).config.x.y;
      expected = true;
    };
    # The value-only discharge, the file-carrying one and the addressed one agree on every value and
    # priority, and the file-carrying one names the record's file. Before: the record was the value.
    test-the-discharge-twins-agree-on-records = {
      expr = map (v: {
        plain = vp (priority.dischargeProperties v);
        filed = map (x: { inherit (x) file value priority; }) (priority.dischargeIn "/m/outer.nix" v);
        at = vp (priority.dischargePropertiesAt v);
      }) twinFixtures;
      expected =
        let
          row = file: value: priority: {
            plain = [ { inherit value priority; } ];
            filed = [ { inherit file value priority; } ];
            at = [ { inherit value priority; } ];
          };
        in
        [
          (row "/r/a.nix" "a" 100)
          (row "/r/a.nix" "b" 100)
          {
            plain = [
              {
                value = "c";
                priority = 100;
              }
              {
                value = "d";
                priority = 50;
              }
            ];
            filed = [
              {
                file = "/m/outer.nix";
                value = "c";
                priority = 100;
              }
              {
                file = "/r/a.nix";
                value = "d";
                priority = 50;
              }
            ];
            at = [
              {
                value = "c";
                priority = 100;
              }
              {
                value = "d";
                priority = 50;
              }
            ];
          }
          (row "/r/a.nix" (gm.mkBefore "e") 100)
        ];
    };
    # nixpkgs' three limits, mirrored on an untyped option. There nixpkgs' own served value is a
    # LEAKED marker (`override`, `if`, `definition`), which is silent: the cells below assert gen serves
    # the SAME silent value, parity with nixpkgs rather than an endorsement of it. gen had no named
    # refusal on these rows to keep (before the arm it leaked `definition` on all three). The leftover
    # marker shows how deep the discharge read, so a deeper or shallower one changes it.
    # (1) Exactly one priority wrapper below the record is read: the second is nixpkgs' leak.
    test-one-override-level-below-a-record-serves-nixpkgs-value = {
      expr = both (P: [
        { options.x = P.mkOption { }; }
        { config.x = d "/r/a.nix" (P.mkForce (P.mkDefault 1)); }
      ]) (r: r.config.x._type);
      expected = {
        gen = "override";
        nixpkgs = "override";
      };
    };
    # (2) An `mkIf` inside the record's value is not discharged: the `if` marker is nixpkgs' leak.
    test-an-mkIf-inside-a-record-serves-nixpkgs-value = {
      expr = both (P: [
        { options.x = P.mkOption { }; }
        { config.x = d "/r/a.nix" (P.mkIf true true); }
      ]) (r: r.config.x._type);
      expected = {
        gen = "if";
        nixpkgs = "if";
      };
    };
    # And so, on a checked type, an `mkMerge` inside it refuses on both.
    test-control-an-mkMerge-inside-a-record-refuses = {
      expr = both (P: [
        (opt (T: T.types.listOf T.types.int) P)
        {
          config.x = d "/r/a.nix" (
            P.mkMerge [
              [ 1 ]
              [ 2 ]
            ]
          );
        }
      ]) (r: refuses r.config.x);
      expected = {
        gen = true;
        nixpkgs = true;
      };
    };
    # (3) `mkForce` AROUND a record is unsupported (nixpkgs' manual: it "would NOT work"): the override
    # is read, and the record under it is nixpkgs' leaked value (as for a nested record, and an
    # `mkMerge` inside a record).
    test-mkForce-around-a-record-serves-nixpkgs-value = {
      expr = both (P: [
        { options.x = P.mkOption { }; }
        { config.x = P.mkForce (d "/r/a.nix" true); }
      ]) (r: r.config.x._type);
      expected = {
        gen = "definition";
        nixpkgs = "definition";
      };
    };
    test-control-mkForce-around-a-record-refuses-on-a-checked-type = {
      expr = both (P: [
        (opt (T: T.types.bool) P)
        { config.x = P.mkForce (d "/r/a.nix" true); }
      ]) (r: refuses r.config.x);
      expected = {
        gen = true;
        nixpkgs = true;
      };
    };
    # The six container positions where gen serves a whole-submodule record element and nixpkgs
    # aborts. Before: each refused.
    test-a-record-as-an-attrsOf-submodule-element-is-checked = {
      expr = servesChecked (gm.types.attrsOf sub) readAttrs inAttrs;
      expected = checked;
    };
    test-a-record-as-a-listOf-submodule-element-is-checked = {
      expr = servesChecked (gm.types.listOf sub) readList (r: [ r ]);
      expected = checked;
    };
    test-a-record-as-a-nullOr-submodule-value-is-checked = {
      expr = servesChecked (gm.types.nullOr sub) (a: a.y) (r: r);
      expected = checked;
    };
    test-a-record-as-a-threaded-attrsOf-element-is-checked = {
      expr = servesChecked (np.types.attrsOf sub) readAttrs inAttrs;
      expected = checked;
    };
    test-a-record-as-a-threaded-lazyAttrsOf-element-is-checked = {
      expr = servesChecked (np.types.lazyAttrsOf sub) readAttrs inAttrs;
      expected = checked;
    };
    test-a-record-as-a-threaded-listOf-element-is-checked = {
      expr = servesChecked (np.types.listOf sub) readList (r: [ r ]);
      expected = checked;
    };
    # gen's constructor builds nixpkgs' record.
    test-mkDefinition-builds-the-nixpkgs-record = {
      expr = gm.mkDefinition {
        file = "/r/a.nix";
        value = 1;
      };
      expected = d "/r/a.nix" 1;
    };
    # CONTROL: a record whose value the type rejects is refused by both engines, before and after.
    test-control-a-record-value-is-checked = {
      expr = both (P: [
        (opt (T: T.types.bool) P)
        { config.x = d "/r/other.nix" 5; }
      ]) (r: refuses r.config.x);
      expected = {
        gen = true;
        nixpkgs = true;
      };
    };
  };
}
