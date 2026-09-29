# THE MODULE GRAPH (den-hoag-470xp, arm F): module imports are graph edges, a module is a node, and
# node identity is nixpkgs' key rule, in two namespaces (an explicit key or a path; an anonymous
# module keyed by its importer). A diamond is two edges into one node, so a module imported twice
# contributes once, by construction. The closure is breadth-first and the first occurrence reached
# wins, as nixpkgs' `filterModules`.
#
# Each cell reads `.config.l`. GREEN is nixpkgs 26.11's value on the same modules, except where a cell
# names a byte-mode boundary (README "Known byte-mode boundaries"): `a1` (the namespaces stay apart)
# and the four cycle cells (nixpkgs overflows the stack; the closure terminates).
#
# RED, evaluated at gen-merge f47c48a (the depth-first list collector): k1 `[x x]`, d1 `[leaf leaf]`,
# d2 `[leaf leaf]`, d4 `[fn fn]`, p1 `[alias leaf]`, s1 `[leaf leaf]`, k2 `[second first]`, b1
# `[shallow deep]`, i1 `[b child a]`, o1 `[B A C]`, o2 `[B C A D E]`; u1, d3 and ctl unchanged; every
# cycle cell aborts the suite (stack overflow), which `tryEval` does not contain. `a1` reads `[a]`
# against a closure whose anonymous group is folded into the key group.
{
  genMerge,
  genMergeCore,
  genScope,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  leaf = ./_fixtures/module-graph-leaf.nix;
  leafFn = ./_fixtures/module-graph-leaf-fn.nix;
  decl = {
    options.l = gm.mkOption {
      type = t.listOf t.str;
      default = [ ];
    };
  };
  l = modules: (gm.evalModuleTree { modules = [ decl ] ++ modules; }).config.l;
  cyA = {
    key = "a";
    l = [ "a" ];
    imports = [ cyB ];
  };
  cyB = {
    key = "b";
    l = [ "b" ];
    imports = [ cyA ];
  };
  cyS = {
    key = "s";
    l = [ "s" ];
    imports = [ cyS ];
  };
in
{
  flake.tests.module-graph = {
    # witness 1: two modules sharing an explicit key are one node
    test-k1-keyed-duplicates-are-one-node = {
      expr = l [
        {
          key = "k";
          l = [ "x" ];
        }
        {
          key = "k";
          l = [ "x" ];
        }
      ];
      expected = [ "x" ];
    };
    # witness 2: a path diamond is two edges into one node
    test-d1-path-diamond-is-one-node = {
      expr = l [
        { imports = [ leaf ]; }
        { imports = [ leaf ]; }
      ];
      expected = [ "leaf" ];
    };
    test-d2-a-path-twice-at-the-top-is-one-node = {
      expr = l [
        leaf
        leaf
      ];
      expected = [ "leaf" ];
    };
    # a function path module is identified by its path, before application
    test-d4-function-path-diamond-is-one-node = {
      expr = l [
        { imports = [ leafFn ]; }
        { imports = [ leafFn ]; }
      ];
      expected = [ "fn" ];
    };
    # an explicit key spelling a path is that path's module (one namespace)
    test-p1-a-key-spelling-a-path-is-that-path = {
      expr = l [
        leaf
        {
          key = toString leaf;
          l = [ "alias" ];
        }
      ];
      expected = [ "leaf" ];
    };
    # a nested tree has its own module graph: the diamond inside a submodule value is one node there
    test-s1-a-nested-tree-deduplicates-in-its-own-graph = {
      expr =
        (gm.evalModuleTree {
          modules = [
            { options.s = gm.mkOption { type = t.submodule decl; }; }
            { s = { ... }: { imports = [ leaf ]; }; }
            { s = { ... }: { imports = [ leaf ]; }; }
          ];
        }).config.s.l;
      expected = [ "leaf" ];
    };
    # the breadth-first winner: the first occurrence reached is the node's content
    test-k2-the-first-occurrence-reached-wins = {
      expr = l [
        {
          key = "k";
          l = [ "first" ];
        }
        {
          key = "k";
          l = [ "second" ];
        }
      ];
      expected = [ "first" ];
    };
    test-b1-the-shallow-occurrence-wins-over-the-deep-one = {
      expr = l [
        {
          imports = [
            {
              key = "k";
              l = [ "deep" ];
            }
          ];
        }
        {
          key = "k";
          l = [ "shallow" ];
        }
      ];
      expected = [ "shallow" ];
    };
    # an occurrence that loses takes its imports with it
    test-i1-a-losing-occurrence-drops-its-imports = {
      expr = l [
        {
          key = "k";
          l = [ "a" ];
        }
        {
          key = "k";
          imports = [ { l = [ "child" ]; } ];
          config.l = [ "b" ];
        }
      ];
      expected = [ "a" ];
    };
    # breadth-first order, no duplicate involved
    test-o1-order-is-breadth-first = {
      expr = l [
        {
          imports = [ { l = [ "C" ]; } ];
          config.l = [ "A" ];
        }
        { l = [ "B" ]; }
      ];
      expected = [
        "C"
        "B"
        "A"
      ];
    };
    test-o2-order-is-breadth-first-two-levels-deep = {
      expr = l [
        {
          imports = [
            {
              imports = [ { l = [ "E" ]; } ];
              config.l = [ "D" ];
            }
          ];
          config.l = [ "A" ];
        }
        {
          imports = [ { l = [ "C" ]; } ];
          config.l = [ "B" ];
        }
      ];
      expected = [
        "E"
        "C"
        "D"
        "B"
        "A"
      ];
    };
    # MUST NOT deduplicate: anonymous modules are distinct nodes, keyed by their importer
    test-u1-unkeyed-equal-modules-stay-two-nodes = {
      expr = l [
        { l = [ "x" ]; }
        { l = [ "x" ]; }
      ];
      expected = [
        "x"
        "x"
      ];
    };
    test-d3-an-anonymous-diamond-stays-two-nodes = {
      expr =
        let
          L = {
            l = [ "L" ];
          };
        in
        l [
          { imports = [ L ]; }
          { imports = [ L ]; }
        ];
      expected = [
        "L"
        "L"
      ];
    };
    test-ctl-plain-modules-keep-their-order = {
      expr = l [
        { l = [ "a" ]; }
        { l = [ "b" ]; }
      ];
      expected = [
        "b"
        "a"
      ];
    };
    # BOUNDARY: an explicit key spelled like an anonymous one stays apart from it (nixpkgs: `[ "a" ]`)
    test-a1-an-explicit-key-never-meets-an-anonymous-node = {
      expr = l [
        { l = [ "a" ]; }
        {
          key = ":anon-2";
          l = [ "b" ];
        }
      ];
      expected = [
        "b"
        "a"
      ];
    };
    # BOUNDARY (termination): a keyed or path import cycle closes over its finite set of node ids
    test-c1-a-keyed-two-cycle-terminates = {
      expr = l [ cyA ];
      expected = [
        "b"
        "a"
      ];
    };
    test-c2-a-keyed-self-import-terminates = {
      expr = l [ cyS ];
      expected = [ "s" ];
    };
    test-c3-a-path-two-cycle-terminates = {
      expr = l [ ./_fixtures/module-graph-cyc-a.nix ];
      expected = [
        "b"
        "a"
      ];
    };
    test-c4-a-path-self-import-terminates = {
      expr = l [ ./_fixtures/module-graph-cyc-self.nix ];
      expected = [ "s" ];
    };

    # WARM: a node reached from both a base root and an edited root has no single origin, so the
    # re-evaluation falls back to cold and says why; its config is the cold one.
    test-warm-refuses-a-node-shared-by-base-and-edit = {
      expr =
        let
          base = [
            decl
            { imports = [ leaf ]; }
          ];
          edited = [ { imports = [ leaf ]; } ];
          w = gm.evalModuleTree {
            modules = base ++ edited;
            warmFrom = gm.evalModuleTree { modules = base; };
            editedModules = edited;
          };
        in
        {
          inherit (w.warmDecision) mode reason;
          inherit (w.config) l;
        };
      expected = {
        mode = "cold";
        reason = "an edited module reaches a module node the base also reaches (warm refused)";
        l = [ "leaf" ];
      };
    };

    # THE AGREEMENT CHECK: a graph reader pairs the merge path's entries with the identity-keyed
    # closure by index, so every index is checked first. Two collections of the same modules in a
    # different order refuse; the same order passes (the control).
    test-the-graph-refuses-a-collection-in-another-order =
      let
        a = {
          m0 = {
            l = [ "a" ];
          };
          key = "a:0";
        };
        b = {
          m0 = {
            imports = [ ];
          };
          key = "a:1";
        };
        flatOf = map (x: {
          inherit (x) m0;
          content = x.m0;
        });
        refuses =
          f: g: !(builtins.tryEval (builtins.deepSeq (genMergeCore.alignedGraph "t" f g) null)).success;
      in
      {
        expr = {
          swapped =
            refuses
              (flatOf [
                a
                b
              ])
              [
                b
                a
              ];
          aligned =
            refuses
              (flatOf [
                a
                b
              ])
              [
                a
                b
              ];
          keyed = refuses (flatOf [ { m0 = leaf; } ]) [
            {
              m0 = leaf;
              key = "k/elsewhere.nix";
            }
          ];
        };
        expected = {
          swapped = true;
          aligned = false;
          keyed = true;
        };
      };

    # THE FAMILY: the diamond's leaf is ONE minted `modules` node with two import edges into it, and
    # every edge lands on a minted node.
    test-the-diamond-leaf-is-one-node-with-two-importers = {
      expr =
        let
          ev =
            (genMergeCore.evalModuleTreeExposed {
              modules = [
                decl
                { imports = [ leaf ]; }
                { imports = [ leaf ]; }
              ];
            })._evaluation;
          ids = [
            "module-tree"
          ]
          ++ builtins.filter (i: (genScope.decodeNta i).name or null == "modules") ev.allNodeIds;
          leafId = genScope.mintNtaId {
            host = "module-tree";
            name = "modules";
            group = "key";
            key = toString leaf;
          };
          edges = builtins.concatMap (i: ev.get i "imports") ids;
        in
        {
          # the node's content is the module the tree collected at that node
          leafContent = (ev.get leafId "result").content.l;
          nodes = builtins.length ids - 1;
          leafNodes = builtins.length (builtins.filter (i: i == leafId) ids);
          intoLeaf = builtins.length (builtins.filter (e: e == leafId) edges);
          edgesResolve = builtins.all (e: builtins.elem e ids) edges;
        };
      expected = {
        leafContent = [ "leaf" ];
        nodes = 4;
        leafNodes = 1;
        intoLeaf = 2;
        edgesResolve = true;
      };
    };
  };
}
