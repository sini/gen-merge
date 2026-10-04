# A module's `_file` given as a PATH VALUE is a string in every reader, as in nixpkgs' `unifyModuleSyntax`
# (`_file = toString m._file or file`; den-hoag-3y4hb, ADR-0039). The ATTRSET arm of `moduleEntries`
# is the origin (the path-module arm is `path-module-own-file.nix`): three `_file` branches (the tree's
# root, an unscoped importer, a scoped importer), a function module's applied result, and the child
# that INHERITS its importer's file. A path value is the only `_file` whose type survives to a reader:
# every text reader interpolates it, so only a type or an equality sees the difference.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  inherit (gm) evalModuleTree lint;
  pv = ./_fixtures/path-key-plain.nix;
  sv = "/real/S.nix";
  declOf = L: {
    options.y = L.mkOption {
      type = L.types.listOf L.types.int;
      default = [ ];
    };
    options.w = L.mkOption {
      type = L.types.int;
      default = 3;
    };
  };
  # the three `moduleEntries` branches, as importers of one module `m`
  branches = {
    root = m: [ m ];
    unscoped = m: [ { imports = [ m ]; } ];
    scoped = m: [
      {
        __reservedKeys.names = { };
        imports = [ m ];
      }
    ];
  };
  # the module shapes: an attrset, a function, and a wrapper whose CHILD inherits the wrapper's `_file`
  shapes = {
    attrset = {
      _file = pv;
      config.y = [ 1 ];
    };
    function =
      { ... }:
      {
        _file = pv;
        config.y = [ 1 ];
      };
    wrapper = {
      _file = pv;
      imports = [ { config.y = [ 1 ]; } ];
    };
  };
  gen =
    mods:
    map (d: builtins.typeOf d.file) (
      builtins.filter (d: d.file != "<default>")
        (evalModuleTree { modules = [ (declOf gm) ] ++ mods; }).provenance.y.defs
    );
  np =
    mods:
    map (d: builtins.typeOf d.file) (
      builtins.filter (d: d.file != "<default>")
        (nixpkgsLib.evalModules { modules = [ (declOf nixpkgsLib) ] ++ mods; })
        .options.y.definitionsWithLocations
    );
  # the reference has no reservation scope: its scoped arm is the unscoped shape
  ref = n: if n == "scoped" then branches.unscoped else branches.${n};
  perBranch =
    shape:
    builtins.mapAttrs (n: wrap: {
      gen = gen (wrap shape);
      nixpkgs = np (ref n shape);
    }) branches;
  string = {
    gen = [ "string" ];
    nixpkgs = [ "string" ];
  };
  allString = {
    root = string;
    unscoped = string;
    scoped = string;
  };
in
{
  flake.tests.file-path-value = {
    test-attrset-module-with-a-path-value-file-reads-a-string = {
      expr = perBranch shapes.attrset;
      expected = allString;
    };
    test-function-module-with-a-path-value-file-reads-a-string = {
      expr = perBranch shapes.function;
      expected = allString;
    };
    # the child has no `_file`: it inherits the wrapper's, which must already be a string
    test-child-of-a-wrapper-with-a-path-value-file-inherits-a-string = {
      expr = perBranch shapes.wrapper;
      expected = allString;
    };
    test-undeclared-and-declarations-and-lint-read-a-string-file = {
      expr = {
        undeclared =
          map (u: builtins.typeOf u.file)
            (evalModuleTree {
              modules = [
                {
                  _file = pv;
                  config.bogus = 1;
                }
              ];
              check = false;
            }).undeclared;
        declarations = {
          gen =
            map builtins.typeOf
              (evalModuleTree {
                modules = [
                  {
                    _file = pv;
                    options.w = gm.mkOption { type = gm.types.int; };
                  }
                ];
              }).options.w.declarations;
          nixpkgs =
            map builtins.typeOf
              (nixpkgsLib.evalModules {
                modules = [
                  {
                    _file = pv;
                    options.w = nixpkgsLib.mkOption { type = nixpkgsLib.types.int; };
                  }
                ];
              }).options.w.declarations;
        };
        lint = map (f: builtins.typeOf f.file) (lint {
          modules = [
            (declOf gm)
            {
              _file = pv;
              config.y = {
                _type = "order";
                priority = 1500;
                content = [ 1 ];
              };
            }
          ];
        });
      };
      expected = {
        undeclared = [ "string" ];
        declarations = {
          gen = [ "string" ];
          nixpkgs = [ "string" ];
        };
        lint = [ "string" ];
      };
    };
    # controls: a string `_file` is untouched, and the file read is the named one
    test-control-string-file-is-read-as-set = {
      expr = gen [
        {
          _file = sv;
          config.y = [ 1 ];
        }
      ];
      expected = [ "string" ];
    };
  };
}
