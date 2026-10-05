# THE DECLARATION ADDRESS OF A SEED (den-hoag-8hlo3 U1; design 2026-09-30 §1; ADR-0034's rider,
# "identity is the declaring position, never the merged one"). A nesting type that declares
# `nests.declAt = true` receives, on each seed `nests.entry` is handed, the place that definition was
# declared: the declaring module's anchor, the option path, and the structural path the discharge
# took. The address never moves under a reorder of keyed or path modules, an `mkIf` beside the
# element, or a sibling module's discharged `mkIf` (A6); an anonymous module moves with its own
# position in its importer (design §1 item 2, OQ5). A child's own modules sit under the child's
# address, so two declarations never share one (gate K2). A type that does not declare the flag is
# handed `{ file; value; }` exactly as before (gate P1, ADR-0039: no nixpkgs-visible change).
{ genMerge, ... }:
let
  gm = genMerge;
  t = gm.types;
  # An element type whose `entry` records what it was handed: the attribute names of the seed record
  # (`handed`) and its `declAt` (`seen`). `own` is extra modules of the type itself.
  elemWith =
    flag: own:
    let
      sub = t.submodule (
        [
          {
            options.tag = gm.mkOption {
              type = t.str;
              default = "";
            };
            options.seen = gm.mkOption {
              type = t.listOf t.anything;
              default = [ ];
            };
            options.handed = gm.mkOption {
              type = t.listOf t.anything;
              default = [ ];
            };
            options.inner = gm.mkOption {
              type = t.listOf (elemWith true [ ]);
              default = [ ];
            };
          }
        ]
        ++ own
      );
      n = sub.nests;
    in
    t.defineType (
      sub
      // {
        nests =
          n
          // {
            entry = d: {
              imports = [ (n.entry { inherit (d) file value; }) ];
              config.seen = [ (d.declAt or null) ];
              config.handed = [ (builtins.attrNames d) ];
            };
          }
          // (if flag then { declAt = true; } else { });
      }
    );
  E = elemWith true [ ];
  hostOf = type: { options.xs = gm.mkOption { inherit type; }; };
  ev = type: mods: (gm.evalModuleTree { } ([ (hostOf type) ] ++ mods)).config;
  evList = elem: ev (t.listOf elem);
  seenOf = tag: cfg: map (e: e.seen) (builtins.filter (e: e.tag == tag) cfg.xs);
  mA = {
    config.xs = [ { tag = "p"; } ];
  };
  mB = {
    config.xs = [ { tag = "q"; } ];
  };
  kA = {
    key = "mA";
  }
  // mA;
  kB = {
    key = "mB";
  }
  // mB;
  fA = ./_fixtures/decl-address-a.nix;
  fB = ./_fixtures/decl-address-b.nix;
  ord = c: {
    config.xs = gm.mkMerge [
      (gm.mkIf c [ { tag = "r"; } ])
      [ { tag = "y"; } ]
    ];
  };
  # Definitions are collected last module first (nixpkgs' order), so the sibling's is discharged
  # ahead of the element's when it is the later module.
  sibling = c: [
    mA
    { config.xs = gm.mkIf c [ { tag = "z"; } ]; }
  ];
  # The element type's own module declares an inner element, so every element holds one.
  Own = elemWith true [ { config.inner = [ { tag = "own"; } ]; } ];
  innerSeen = cfg: map (e: map (i: i.seen) e.inner) cfg.xs;
in
{
  flake.tests.declaration-address = {
    # A6, keyed limb: the address names the module's key, in both orders.
    test-keyed-reorder-keeps-the-address = {
      expr = {
        ab = seenOf "p" (
          evList E [
            kA
            kB
          ]
        );
        ba = seenOf "p" (
          evList E [
            kB
            kA
          ]
        );
      };
      expected = {
        ab = [
          [
            [
              "kmA"
              "xs"
              0
            ]
          ]
        ];
        ba = [
          [
            [
              "kmA"
              "xs"
              0
            ]
          ]
        ];
      };
    };
    # A6, path limb: the address names the module's path, in both orders.
    test-path-reorder-keeps-the-address = {
      expr =
        let
          ab = seenOf "p" (
            evList E [
              fA
              fB
            ]
          );
          ba = seenOf "p" (
            evList E [
              fB
              fA
            ]
          );
        in
        {
          same = ab == ba;
          tail = map (map builtins.tail) ab;
          anchor = (builtins.head (builtins.head (builtins.head ab))) == "k${toString fA}";
        };
      expected = {
        same = true;
        tail = [
          [
            [
              "xs"
              0
            ]
          ]
        ];
        anchor = true;
      };
    };
    # A6, in-module limb: an `mkIf` beside the element moves its merge position, never its address.
    test-in-module-mkif-keeps-the-address = {
      expr = {
        on = seenOf "y" (evList E [ (ord true) ]);
        off = seenOf "y" (evList E [ (ord false) ]);
      };
      expected = {
        on = [
          [
            [
              "a:1"
              "xs"
              "contents"
              1
              0
            ]
          ]
        ];
        off = [
          [
            [
              "a:1"
              "xs"
              "contents"
              1
              0
            ]
          ]
        ];
      };
    };
    # A6, sibling limb: another module's `mkIf`, discharged ahead of the element's definition.
    test-sibling-mkif-keeps-the-address = {
      expr = {
        on = seenOf "p" (evList E (sibling true));
        off = seenOf "p" (evList E (sibling false));
      };
      expected = {
        on = [
          [
            [
              "a:1"
              "xs"
              0
            ]
          ]
        ];
        off = [
          [
            [
              "a:1"
              "xs"
              0
            ]
          ]
        ];
      };
    };
    # OQ5, the declared behaviour: an anonymous module's identity is its position in its importer,
    # so reordering two anonymous modules moves the modules and the element follows its own.
    test-anonymous-module-moves-with-its-position = {
      expr = {
        ab = seenOf "p" (
          evList E [
            mA
            mB
          ]
        );
        ba = seenOf "p" (
          evList E [
            mB
            mA
          ]
        );
      };
      expected = {
        ab = [
          [
            [
              "a:1"
              "xs"
              0
            ]
          ]
        ];
        ba = [
          [
            [
              "a:2"
              "xs"
              0
            ]
          ]
        ];
      };
    };
    # Control: two literals in one tree carry two addresses.
    test-two-declarations-two-addresses = {
      expr =
        let
          cfg = evList E [
            kA
            kB
          ];
        in
        seenOf "p" cfg != seenOf "q" cfg;
      expected = true;
    };
    # The address chains through every nesting: an inner element's runs through its outer one's.
    test-nested-address-chains-through-its-host = {
      expr = innerSeen (
        evList E [
          {
            config.xs = [
              {
                tag = "o";
                inner = [ { tag = "i"; } ];
              }
            ];
          }
        ]
      );
      expected = [
        [
          [
            [
              "a:1"
              "xs"
              0
              "imports"
              0
              "inner"
              0
            ]
          ]
        ]
      ];
    };
    # K2: the element type's own module declares an inner element in every element. Each sits under
    # its own element's address, so the two are two addresses; anchored on the child's own module
    # index alone, both read `[ "a:1" "inner" 0 ]`.
    test-own-module-sits-under-its-child = {
      expr = innerSeen (
        evList Own [
          {
            config.xs = [
              { tag = "a"; }
              { tag = "b"; }
            ];
          }
        ]
      );
      expected = [
        [
          [
            [
              "a:1"
              "xs"
              0
              { module = 1; }
              "inner"
              0
            ]
          ]
        ]
        [
          [
            [
              "a:1"
              "xs"
              1
              { module = 1; }
              "inner"
              0
            ]
          ]
        ]
      ];
    };
    # K2 at a position with two seeds: the own module sits under the position's `loc`.
    test-own-module-under-a-two-seed-position = {
      expr = map (e: map (i: i.seen) e.inner) (
        builtins.attrValues
          (ev (t.attrsOf Own) [
            { config.xs.a.tag = "a"; }
            { config.xs.a.seen = [ ]; }
          ]).xs
      );
      expected = [
        [
          [
            [
              {
                loc = [
                  "xs"
                  "a"
                ];
              }
              { module = 1; }
              "inner"
              0
            ]
          ]
        ]
      ];
    };
    # P1, ADR-0039 parity: a nesting type that does not declare `nests.declAt` is handed exactly
    # `{ file; value; }`, as before; one that declares it is handed `declAt` besides.
    test-unflagged-type-is-handed-no-address = {
      expr = {
        unflagged = map (e: e.handed) (evList (elemWith false [ ]) [ mA ]).xs;
        flagged = map (e: e.handed) (evList E [ mA ]).xs;
      };
      expected = {
        unflagged = [
          [
            [
              "file"
              "value"
            ]
          ]
        ];
        flagged = [
          [
            [
              "declAt"
              "file"
              "value"
            ]
          ]
        ];
      };
    };
    # A container node's elements (`lazyAttrsOf`, den-hoag-9d80v) take their addresses through the
    # container's own seeds, the discharged `mkIf` included.
    test-container-node-elements-are-addressed = {
      expr =
        builtins.mapAttrs (_: map (e: e.seen))
          (ev (t.lazyAttrsOf (t.listOf E)) [
            {
              key = "kc";
              config.xs.a = [ { tag = "x"; } ];
            }
            { config.xs.a = gm.mkIf true [ { tag = "y"; } ]; }
          ]).xs;
      expected.a = [
        [
          [
            "a:2"
            "xs"
            "a"
            "content"
            0
          ]
        ]
        [
          [
            "kkc"
            "xs"
            "a"
            0
          ]
        ]
      ];
    };
    # The freeform plane's positions take their declaring module's anchor and their own key.
    test-freeform-positions-are-addressed = {
      expr = builtins.mapAttrs (_: e: e.seen) (
        (gm.evalModuleTree { } [
          { freeformType = t.attrsOf E; }
          {
            key = "kf";
            config.foo.tag = "f";
          }
          { config.bar.tag = "b"; }
        ]).config
      );
      expected = {
        foo = [
          [
            "kkf"
            "foo"
          ]
        ];
        bar = [
          [
            "a:2"
            "bar"
          ]
        ];
      };
    };
  };
}
