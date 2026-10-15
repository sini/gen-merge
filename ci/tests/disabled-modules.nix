# MODULE REMOVAL (`disabledModules`, den-hoag-7o7i9): the reference's `collectModules`, in the one
# collection (`lib/modules.nix`, `removal`). Every cell evaluates one module set on both engines and
# reads both values: GREEN is gen-merge's value equal to the reference's, and to the literal the cell
# states. The removal's refusals and the load checks it runs on removed and losing modules are the
# error plane's `disabled-modules` group, beside its reference arm here
# (`test-the-reference-refuses-the-error-plane-shapes`).
#
# RED, evaluated at gen-merge e3e1305 (the presence refusal): every cell that states `disabledModules`
# on a kept module refuses; `dropped` and `droppedsub` serve `[ "k1" "b" ]` (the list on a losing
# occurrence, or under it, was never read); `dedup-*` serve where the reference refuses (error plane).
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  fx = ./_fixtures/disabled-modules;
  b = fx + "/b.nix";
  declOf = L: {
    options.x = L.mkOption {
      type = L.types.listOf L.types.str;
      default = [ ];
    };
  };
  # `x` under both engines, `modulesPath` the fixture directory, as the reference's `evalModules` passes it.
  both = ms: {
    gen =
      (gm.evalModuleTree {
        specialArgs.modulesPath = fx;
      } ([ (declOf gm) ] ++ ms)).config.x;
    nixpkgs =
      (nixpkgsLib.evalModules {
        modules = [ (declOf nixpkgsLib) ] ++ ms;
        specialArgs.modulesPath = fx;
      }).config.x;
  };
  is = v: {
    gen = v;
    nixpkgs = v;
  };
  graphOf =
    r:
    let
      go = n: {
        inherit (n) key disabled;
        imports = map go n.imports;
      };
    in
    map go r.graph;
  bothGraph = ms: {
    gen = graphOf (
      gm.evalModuleTree {
        specialArgs.modulesPath = fx;
      } ([ (declOf gm) ] ++ ms)
    );
    nixpkgs = graphOf (
      nixpkgsLib.evalModules {
        modules = [ (declOf nixpkgsLib) ] ++ ms;
        specialArgs.modulesPath = fx;
      }
    );
  };
  refuses = v: !(builtins.tryEval (builtins.deepSeq v v)).success;
  # the error plane's shapes, under the reference (`readsconfig` and `notlist` are not catchable there:
  # the reference recurses infinitely, and a list type error is no `throw`)
  npX =
    args: ms:
    (nixpkgsLib.evalModules (
      {
        modules = [ (declOf nixpkgsLib) ] ++ ms;
        specialArgs.modulesPath = fx;
      }
      // args
    )).config.x;
in
{
  flake.tests.disabled-modules = {
    # The control: no `disabledModules` anywhere.
    test-a-set-stating-no-removal-is-unchanged = {
      expr = both [
        b
        { x = [ "a" ]; }
      ];
      expected = is [
        "a"
        "b"
      ];
    };
    # A path value names the path module.
    test-a-path-item-removes-the-path-module = {
      expr = both [
        b
        { disabledModules = [ b ]; }
      ];
      expected = is [ ];
    };
    # A relative string resolves against `specialArgs.modulesPath`.
    test-a-relative-string-resolves-against-modules-path = {
      expr = both [
        b
        { disabledModules = [ "b.nix" ]; }
      ];
      expected = is [ ];
    };
    # An anonymous module is named by its reference key, `<importer>:anon-<n>`, 1-based, the top
    # importer `""`; the control names an index nothing holds.
    test-an-anonymous-module-is-named-by-its-reference-key = {
      expr = {
        named = both [
          { x = [ "a" ]; }
          { disabledModules = [ { key = ":anon-2"; } ]; }
        ];
        control = both [
          { x = [ "a" ]; }
          { disabledModules = [ { key = ":anon-9"; } ]; }
        ];
      };
      expected = {
        named = is [ ];
        control = is [ "a" ];
      };
    };
    # A disabled anonymous module's imports go with it, named by the nested reference key.
    test-an-anonymous-import-is-named-under-its-importer = {
      expr = both [
        { imports = [ { x = [ "n" ]; } ]; }
        { disabledModules = [ { key = ":anon-2:anon-1"; } ]; }
      ];
      expected = is [ ];
    };
    # Matching is string equality: an item whose key is the integer 123 names nothing, where the
    # convertible item `123` names the module keyed `123`.
    test-a-non-string-key-names-nothing = {
      expr = {
        intKey = both [
          {
            key = 123;
            x = [ "k" ];
          }
          { disabledModules = [ { key = 123; } ]; }
        ];
        convertible = both [
          {
            key = 123;
            x = [ "k" ];
          }
          { disabledModules = [ 123 ]; }
        ];
      };
      expected = {
        intKey = is [ "k" ];
        convertible = is [ ];
      };
    };
    # A module removing itself is removed, and its own list still applies.
    test-a-module-removing-itself-is-removed = {
      expr = both [ (fx + "/self.nix") ];
      expected = is [ ];
    };
    # Every occurrence of a removed module goes, and with it the imports of the module that imported
    # it, never the importer itself.
    test-every-occurrence-of-a-removed-module-goes = {
      expr = {
        twice = both [
          { imports = [ b ]; }
          { imports = [ b ]; }
          { disabledModules = [ b ]; }
        ];
        withImports = both [
          (fx + "/imp.nix")
          { disabledModules = [ (fx + "/imp.nix") ]; }
        ];
        importerKept = both [
          (fx + "/imp.nix")
          { disabledModules = [ b ]; }
        ];
      };
      expected = {
        twice = is [ ];
        withImports = is [ ];
        importerKept = is [ "i" ];
      };
    };
    # A path module whose file states its own key is named by that key, not by its path.
    test-a-keyed-path-module-is-named-by-its-key = {
      expr = {
        byKey = both [
          (fx + "/kp.nix")
          { disabledModules = [ { key = "P"; } ]; }
        ];
        byPath = both [
          (fx + "/kp.nix")
          { disabledModules = [ (fx + "/kp.nix") ]; }
        ];
      };
      expected = {
        byKey = is [ ];
        byPath = is [ "p" ];
      };
    };
    # THE GATHERING DOMAIN IS EVERY OCCURRENCE (OQ1): a list on the losing occurrence of a key, or on
    # that occurrence's import, is read. The control puts the list on the winning occurrence.
    test-a-losing-occurrence-and-its-imports-are-read = {
      expr = {
        dropped = both [
          b
          {
            key = "K";
            x = [ "k1" ];
          }
          {
            key = "K";
            disabledModules = [ b ];
          }
        ];
        droppedsub = both [
          b
          {
            key = "K";
            x = [ "k1" ];
          }
          {
            key = "K";
            imports = [ { disabledModules = [ b ]; } ];
          }
        ];
        control = both [
          b
          {
            key = "K";
            disabledModules = [ b ];
          }
          {
            key = "K";
            x = [ "k1" ];
          }
        ];
      };
      expected = {
        dropped = is [ "k1" ];
        droppedsub = is [ "k1" ];
        control = is [ ];
      };
    };
    # The graph marks a removed node `disabled`, path and anonymous alike, and keeps it in the graph.
    test-the-graph-marks-the-removed-node = {
      expr = {
        path = bothGraph [
          b
          { disabledModules = [ b ]; }
        ];
        anon = bothGraph [
          { x = [ "a" ]; }
          { disabledModules = [ { key = ":anon-2"; } ]; }
        ];
      };
      expected =
        let
          node = key: disabled: {
            inherit key disabled;
            imports = [ ];
          };
          rows = path: [
            (node ":anon-1" false)
            (if path then node (toString b) true else node ":anon-2" true)
            (node ":anon-3" false)
          ];
        in
        {
          path = is (rows true);
          anon = is (rows false);
        };
    };
    # A removed module's declarations are gone from every declaration read, as from config.
    test-a-removed-module-declares-nothing = {
      expr =
        let
          keyed = {
            key = "B";
            options.y = gm.mkOption { default = 0; };
          };
          dis = {
            disabledModules = [ { key = "B"; } ];
          };
        in
        {
          declared = builtins.attrNames (
            gm.declaredOptions { } [
              keyed
              dis
            ]
          );
          options =
            builtins.attrNames
              (gm.evalModuleTree { } [
                keyed
                dis
              ]).options;
          control = builtins.attrNames (gm.declaredOptions { } [ keyed ]);
        };
      expected = {
        declared = [ "_module" ];
        options = [ "_module" ];
        control = [
          "_module"
          "y"
        ];
      };
    };
    # The reference refuses each shape the error plane's `disabled-modules` group pins gen-merge's
    # refusal of, so those are refusals the reference makes too.
    test-the-reference-refuses-the-error-plane-shapes = {
      expr = builtins.mapAttrs (_: refuses) {
        badsyntax = npX { } [
          (fx + "/bad.nix")
          { disabledModules = [ (fx + "/bad.nix") ]; }
        ];
        classdis = npX { class = "nixos"; } [
          (fx + "/cls.nix")
          { disabledModules = [ (fx + "/cls.nix") ]; }
        ];
        fnitem = npX { } [
          b
          { disabledModules = [ (x: x) ]; }
        ];
        ambig = npX { } [
          b
          {
            disabledModules = [
              {
                outPath = b;
                key = "other";
              }
            ];
          }
        ];
        unkeyed = npX { } [
          b
          { disabledModules = [ { x = 1; } ]; }
        ];
        dedupbad = npX { } [
          {
            key = "K";
            x = [ "k1" ];
          }
          {
            key = "K";
            config = { };
            foo = 1;
          }
        ];
        dedupclass = npX { class = "nixos"; } [
          {
            key = "K";
            x = [ "k1" ];
          }
          {
            key = "K";
            _class = "darwin";
            x = [ "k2" ];
          }
        ];
      };
      expected = {
        badsyntax = true;
        classdis = true;
        fnitem = true;
        ambig = true;
        unkeyed = true;
        dedupbad = true;
        dedupclass = true;
      };
    };
  };
}
