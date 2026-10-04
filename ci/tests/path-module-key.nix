# A PATH-imported module is identified by the `key` its own content sets, else by its path, as in
# nixpkgs' `loadModule`/`unifyModuleSyntax` (`key = toString m.key or key`, `key` the path for a path
# module; den-hoag-mw1bg, ADR-0039), and an ATTRSET module's `_file` given as a PATH value is a string
# in every reader (`_file = toString m._file or file`; den-hoag-3y4hb). One identity rule, four
# spellings that must agree (`moduleKeyOf`, `nodeKeyOf`, `keyedDrop`, lint's `collect`), and one `_file`
# origin with three branches (`moduleEntries`). The `config.y`/`config.x` of two modules sharing a key
# is one module's under nixpkgs: `x` is a plain int, so a surviving pair would REFUSE (1 against 2).
{
  genMerge,
  genMergeCore,
  genScope,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  fx = ./_fixtures;
  pa = fx + "/path-key-a.nix";
  pb = fx + "/path-key-b.nix";
  fa = fx + "/path-key-fn-a.nix";
  fb = fx + "/path-key-fn-b.nix";
  plain = fx + "/path-key-plain.nix";
  spells = fx + "/path-key-spells.nix";
  la = fx + "/path-key-lint-a.nix";
  lb = fx + "/path-key-lint-b.nix";
  ea = fx + "/path-key-eq-a.nix";
  eb = fx + "/path-key-eq-b.nix";
  en = fx + "/path-key-eq-no.nix";
  declOf = L: {
    options.x = L.mkOption {
      type = L.types.int;
      default = 0;
    };
    options.y = L.mkOption {
      type = L.types.listOf L.types.str;
      default = [ ];
    };
  };
  # the tree's modules at a position; a scoped importer has no nixpkgs counterpart (its reference is
  # the unscoped shape)
  imp = ms: { imports = ms; };
  scoped = ms: {
    __reservedKeys.names = { };
    imports = ms;
  };
  positions = sc: a: b: {
    root = [
      a
      b
    ];
    unscoped = [
      (imp [
        a
        b
      ])
    ];
    scoped = [
      (sc [
        a
        b
      ])
    ];
    split = [
      a
      (imp [ b ])
    ];
    splitScoped = [
      a
      (sc [ b ])
    ];
    # the keyed occurrence reached SHALLOWER is the one kept
    deepFirst = [
      (imp [ a ])
      b
    ];
  };
  gen =
    mods:
    let
      r = gm.evalModuleTree { } ([ (declOf gm) ] ++ mods);
      v = builtins.tryEval (builtins.deepSeq [ r.config.x r.config.y ] [ r.config.x r.config.y ]);
    in
    if v.success then v.value else "REFUSED";
  np =
    mods:
    let
      r = nixpkgsLib.evalModules { modules = [ (declOf nixpkgsLib) ] ++ mods; };
      v = builtins.tryEval (builtins.deepSeq [ r.config.x r.config.y ] [ r.config.x r.config.y ]);
    in
    if v.success then v.value else "REFUSED";
  # every position through both engines; the scoped arms read the unscoped nixpkgs value
  atAll =
    a: b:
    let
      gp = positions scoped a b;
      np' = positions imp a b;
    in
    builtins.mapAttrs (n: ms: {
      gen = gen ms;
      nixpkgs = np np'.${n};
    }) gp;
  both = v: {
    gen = v;
    nixpkgs = v;
  };
  survives = {
    root = both [
      1
      [ "a" ]
    ];
    unscoped = both [
      1
      [ "a" ]
    ];
    scoped = both [
      1
      [ "a" ]
    ];
    split = both [
      1
      [ "a" ]
    ];
    splitScoped = both [
      1
      [ "a" ]
    ];
    deepFirst = both [
      2
      [ "b" ]
    ];
  };
in
{
  flake.tests.path-module-key = {
    # mw1bg — two path modules with one in-file `key` are one module, at every level a closure reaches
    test-attrset-path-modules-sharing-a-key-are-one-module = {
      expr = atAll pa pb;
      expected = survives;
    };
    test-function-path-modules-sharing-a-key-are-one-module = {
      expr = atAll fa fb;
      expected = survives;
    };
    # the string-path spelling (`isPathString`) is the same arm
    test-string-path-modules-sharing-a-key-are-one-module = {
      expr = atAll (toString pa) (toString pb);
      expected = survives;
    };
    # a path module and an inline module sharing a key, in both orders
    test-a-path-module-and-an-inline-module-sharing-a-key-are-one-module = {
      expr = {
        pathFirst = atAll pa {
          key = "pk";
          config.x = 2;
          config.y = [ "b" ];
        };
        inlineFirst = atAll {
          key = "pk";
          config.x = 1;
          config.y = [ "a" ];
        } pb;
      };
      expected = {
        pathFirst = survives;
        inlineFirst = survives;
      };
    };
    # a path module's in-file key that SPELLS another path module's path is that module
    test-a-path-modules-key-spelling-another-path-is-that-module = {
      expr = {
        keyedFirst = atAll spells plain;
        plainFirst = atAll plain spells;
      };
      expected = {
        keyedFirst = builtins.mapAttrs (
          n: _:
          both (
            if n == "deepFirst" then
              [
                0
                [ "plain" ]
              ]
            else
              [
                0
                [ "spells" ]
              ]
          )
        ) survives;
        plainFirst = builtins.mapAttrs (
          n: _:
          both (
            if n == "deepFirst" then
              [
                0
                [ "spells" ]
              ]
            else
              [
                0
                [ "plain" ]
              ]
          )
        ) survives;
      };
    };
    # controls: no `key` keeps both (two paths), one path twice is one module, inline keyed dedups
    test-control-path-modules-without-a-key-are-two-modules = {
      expr = {
        two = gen [
          pa
          plain
        ];
        twice = gen [
          plain
          plain
        ];
      };
      expected = {
        two = [
          1
          [
            "plain"
            "a"
          ]
        ];
        twice = [
          0
          [ "plain" ]
        ];
      };
    };
    # the node graph reads one node per key: the closure's own spelling (`moduleKeyOf`) agrees with
    # the merge path's (`nodeKeyOf`), or `alignedGraph` refuses by name
    test-the-graph-reads-one-node-for-a-shared-path-key =
      let
        ev =
          (genMergeCore.evalModuleTreeExposed {
            modules = [
              (declOf gm)
              pa
              pb
            ];
          })._evaluation;
        ids = builtins.filter (i: (genScope.decodeNta i).name or null == "modules") ev.allNodeIds;
        keyId = genScope.mintNtaId {
          host = "module-tree";
          name = "modules";
          group = "key";
          key = "pk";
        };
      in
      {
        expr = {
          nodes = builtins.length ids;
          keyed = builtins.elem keyId ids;
          content = (ev.get keyId "result").content.config.y;
        };
        expected = {
          # the declaration module and the one keyed node
          nodes = 2;
          keyed = true;
          content = [ "a" ];
        };
      };
    # lint mirrors the engine's identity: the second keyed path module is not linted, as it is not merged
    test-lint-reads-a-path-modules-own-key = {
      expr = {
        lint = map (f: f.file) (
          gm.lint [
            (declOf gm)
            la
            lb
          ]
        );
        engine = map (d: d.file) (
          builtins.filter (d: d.file != "<default>")
            (gm.evalModuleTree { } [
              (declOf gm)
              la
              lb
            ]).provenance.y.defs
        );
      };
      expected = {
        lint = [ (toString la) ];
        engine = [ (toString la) ];
      };
    };
    # BOUNDARY: lint != engine for a FUNCTION path module's key. The lint applies no module, so a key that
    # exists only after application is invisible to it (lint.nix `collect` RESIDUE): an opaque function
    # path module is keyed apart, so two sharing a key are one node to the engine and two to the lint,
    # which reports the finding of each. Over-report only, never under-report.
    test-lint-function-path-modules-sharing-a-key-are-two-nodes-where-the-engine-has-one = {
      expr =
        let
          mods = [
            (declOf gm)
            (fx + "/path-key-lint-fn-a.nix")
            (fx + "/path-key-lint-fn-b.nix")
          ];
        in
        {
          lintFindings = builtins.length (gm.lint mods);
          engine = (gm.evalModuleTree { } mods).config.y;
        };
      expected = {
        lintFindings = 2;
        engine = [ "a" ];
      };
    };
    # the boundary's other direction: an inline module whose key SPELLS a function path module's path is
    # a second module to the engine (the path module is its in-file key), so lint keeps it too. Keyed by
    # its path, the opaque function module would swallow the inline one and its finding would vanish.
    test-lint-keeps-an-inline-module-spelling-a-function-path-modules-path =
      let
        fu = fx + "/path-key-lint-under.nix";
        arm = L: ikey: [
          (declOf L)
          fu
          {
            key = ikey;
            config.y = L.mkBefore [ "i" ];
          }
        ];
        read = ikey: {
          lint = map (f: f.kind) (gm.lint (arm gm ikey));
          gen = (gm.evalModuleTree { } (arm gm ikey)).config.y;
          nixpkgs = (nixpkgsLib.evalModules { modules = arm nixpkgsLib ikey; }).config.y;
        };
        kept = {
          lint = [ "order-pass" ];
          gen = [
            "i"
            "f"
          ];
          nixpkgs = [
            "i"
            "f"
          ];
        };
      in
      {
        expr = {
          spellsPath = read (toString fu);
          # control: a key that spells nothing
          other = read "other";
        };
        expected = {
          spellsPath = kept;
          other = kept;
        };
      };
    # `__keyEq` over path modules: one file twice stays one module (test-path-keyed-twice-is-one-module);
    # two DIFFERENT files sharing a key are decided by the comparison, as two content modules are
    test-two-keyed-path-files-are-decided-by-their-key-comparison =
      let
        l =
          ms:
          let
            v = builtins.tryEval (builtins.deepSeq (gen ms) (gen ms));
          in
          if v.success then v.value else "REFUSED";
      in
      {
        expr = {
          equal = l [
            ea
            eb
          ];
          # the kept entry's comparison decides: `en` kept answers false
          unequal = l [
            en
            ea
          ];
        };
        expected = {
          equal = [
            0
            [ "a" ]
          ];
          unequal = "REFUSED";
        };
      };
  };
}
