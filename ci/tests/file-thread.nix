# File threading through the import flatten (ADR-0025 item 1): a module's `_file` is an INHERITED
# attribute of the import tree. An imported module with no `_file` of its own is attributed to its
# importer (`collectModulesFrom`'s `parentFile`), never to the `"<gen-merge>"` root fallback, so a
# real file is not dropped without a diagnostic when content passes through
# `setDefaultModuleLocation F m` (`{ _file = F; imports = [ m ]; }`) or a hand-written wrapper of the
# same shape.
#
# Every wrapped arm reads `F`; each has a DIRECT-`_file` control that reads `F` without any
# flatten involved. The refusal-TEXT arms (`declared in …`, `defined in …`) assert an error message
# and so live on `testsError` (`../tests-error.nix`, `file-thread`).
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  inherit (gm) evalModuleTree mkOption lint;
  t = gm.types;
  F = "/real/F.nix";
  # The body of `lib/modules.nix` `setDefaultModuleLocation` (not on the public surface).
  sdml = file: m: {
    _file = file;
    imports = [ m ];
  };
  body = {
    config.bogus = 1;
  };
  und =
    mods:
    map (u: u.file)
      (evalModuleTree {
        modules = mods;
        check = false;
      }).undeclared;
  declX = {
    options.x = mkOption { type = t.int; };
  };
  provFiles =
    mods:
    let
      p = (evalModuleTree { modules = [ declX ] ++ mods; }).provenance.x;
    in
    {
      defs = map (d: d.file) p.defs;
      winners = map (d: d.file) p.winners;
    };
  pathMod = ./_fixtures/file-thread-path.nix;

  # A nested tree, for the moduleTree arm (U1) and the `.config` fence (C).
  tree = evalModuleTree {
    modules = [
      {
        _file = "/real/T.nix";
        options.a = mkOption {
          type = t.int;
          default = 0;
        };
      }
    ];
  };

  # nixpkgs order marker, built directly (gen-merge exports no `mkOrder`; see lint.nix).
  mkAfter = content: {
    _type = "order";
    priority = 1500;
    inherit content;
  };
  xsDecl = {
    options.xs = mkOption {
      type = t.listOf t.str;
      default = [ ];
    };
  };
  lintFiles =
    mods:
    map
      (f: {
        inherit (f) kind file;
      })
      (lint {
        modules = [ xsDecl ] ++ mods;
      });

  # Laziness fixture: a wrapper whose own `_file` throws. Reading `.config` must not force it.
  zDecl = {
    options.a = mkOption { type = t.int; };
  };
  zWrapped = {
    _file = throw "parent file forced";
    imports = [ { config.a = 1; } ];
  };

  # F1: the same def through nixpkgs' `evalModules` (the reference side) and through gen-merge. Both
  # read the file of the one definition of the declared option `x`.
  nixpkgsFiles =
    mods:
    map (d: d.file)
      (nixpkgsLib.evalModules {
        modules = [ { options.x = nixpkgsLib.mkOption { type = nixpkgsLib.types.int; }; } ] ++ mods;
      }).options.x.definitionsWithLocations;
  genMergeFiles = mods: (provFiles mods).defs;
  deferredOf =
    evalModules: mkOpt: types:
    (evalModules {
      modules = [
        { options.d = mkOpt { type = types.deferredModule; }; }
        {
          _file = F;
          config.d = {
            config.x = 1;
          };
        }
      ];
    }).config.d;
  f1Arms = {
    direct = [
      {
        _file = F;
        config.x = 1;
      }
    ];
    sdmlAttrs = [ (sdml F { config.x = 1; }) ];
    sdmlFn = [ (sdml F ({ ... }: { config.x = 1; })) ];
    manualWrapper = [
      {
        _file = F;
        imports = [ { config.x = 1; } ];
      }
    ];
  };
in
{
  flake.tests.file-thread = {
    # S1 — the undeclared report's `file`, top level: a wrapped attrset child, a wrapped function
    # child, and a hand-written `{ _file; imports }` wrapper all read the wrapper's file.
    test-undeclared-wrapped-attrs-reads-importer-file = {
      expr = und [ (sdml F body) ];
      expected = [ F ];
    };
    test-undeclared-wrapped-function-reads-importer-file = {
      expr = und [ (sdml F ({ ... }: body)) ];
      expected = [ F ];
    };
    test-undeclared-hand-written-wrapper-reads-importer-file = {
      expr = und [
        {
          _file = F;
          imports = [ body ];
        }
      ];
      expected = [ F ];
    };
    test-undeclared-direct-file-control = {
      expr = und [
        {
          _file = F;
          config.bogus = 1;
        }
      ];
      expected = [ F ];
    };
    # P — a PATH child is its own attribution (as in nixpkgs): it reads its path string, not `F`.
    test-path-child-keeps-its-own-path = {
      expr = und [ (sdml F pathMod) ];
      expected = [ (toString pathMod) ];
    };
    # Precedence — a child that names its own `_file` keeps it over the inherited one.
    test-child-own-file-beats-inherited = {
      expr = und [
        (sdml F {
          _file = "/real/OWN.nix";
          config.bogus = 1;
        })
      ];
      expected = [ "/real/OWN.nix" ];
    };
    # S2 — provenance `defs[].file` and `winners[].file`.
    test-provenance-wrapped-reads-importer-file = {
      expr = provFiles [ (sdml F { config.x = 1; }) ];
      expected = {
        defs = [ F ];
        winners = [ F ];
      };
    };
    test-provenance-direct-file-control = {
      expr = provFiles [
        {
          _file = F;
          config.x = 1;
        }
      ];
      expected = {
        defs = [ F ];
        winners = [ F ];
      };
    };
    # S3 — a `deferredModule` value's defs carry the defining file (`lib/types.nix` wraps each def
    # as `setDefaultModuleLocation "<file>, via option <loc>"`).
    test-deferred-module-reads-defining-file = {
      expr =
        let
          outer = evalModuleTree {
            modules = [
              { options.d = mkOption { type = t.deferredModule; }; }
              {
                _file = F;
                config.d = body;
              }
            ];
          };
        in
        und [ outer.config.d ];
      expected = [ "/real/F.nix, via option d" ];
    };
    # U1 — a moduleTree leaf's dropped key bubbles up with the def's file.
    test-module-tree-dropped-key-reads-def-file = {
      expr =
        map
          (u: {
            inherit (u) file path;
          })
          (evalModuleTree {
            check = false;
            modules = [
              { options.t = mkOption { type = tree.type; }; }
              {
                _file = F;
                config.t = {
                  bogus = 1;
                };
              }
            ];
          }).undeclared;
      expected = [
        {
          file = F;
          path = [
            "t"
            "bogus"
          ];
        }
      ];
    };
    # L1 — lint's `collect` threads the same rule: a wrapped order marker's finding reads `F`; the
    # direct control reads `F`; a child's own `_file` beats the inherited one.
    test-lint-wrapped-reads-importer-file = {
      expr = lintFiles [ (sdml F { config.xs = mkAfter [ "z" ]; }) ];
      expected = [
        {
          kind = "order-pass";
          file = F;
        }
      ];
    };
    test-lint-direct-file-control = {
      expr = lintFiles [
        {
          _file = F;
          config.xs = mkAfter [ "z" ];
        }
      ];
      expected = [
        {
          kind = "order-pass";
          file = F;
        }
      ];
    };
    test-lint-child-own-file-beats-inherited = {
      expr = lintFiles [
        (sdml F {
          _file = "/real/OWN.nix";
          config.xs = mkAfter [ "z" ];
        })
      ];
      expected = [
        {
          kind = "order-pass";
          file = "/real/OWN.nix";
        }
      ];
    };
    # C — `.config` does not depend on `_file`: wrappers, a function child, an `mkOverride`
    # conflict, own content plus imports, and a nested tree. Priority and merge order key on the
    # module INSTANCE, never on the file; a change to the flatten ORDER moves this digest.
    test-config-digest-unmoved-by-file-threading = {
      expr = builtins.hashString "sha256" (
        builtins.toJSON
          (evalModuleTree {
            modules = [
              {
                options.p = mkOption { type = t.int; };
                options.q = mkOption {
                  type = t.listOf t.str;
                  default = [ ];
                };
                options.t = mkOption { type = tree.type; };
              }
              (sdml "/real/P1.nix" { config.p = gm.mkOverride 90 1; })
              (sdml "/real/P2.nix" ({ ... }: { config.p = 2; }))
              {
                _file = "/real/Q.nix";
                config.q = [ "own" ];
                imports = [
                  { config.q = [ "a" ]; }
                  (sdml "/real/Q2.nix" { config.q = [ "b" ]; })
                ];
              }
              {
                _file = "/real/T.nix";
                config.t = {
                  a = 7;
                };
              }
            ];
          }).config
      );
      expected = "50408482045a0ad4c0f25031ea5a9cf0e500a659ce8d8b9b6d4b8dc8fbbb5a64";
    };
    # Z1 — the threaded parent file is a THUNK: reading `.config` through a wrapper whose `_file`
    # throws does not force it. An eager thread reads `false` here.
    test-config-read-does-not-force-parent-file = {
      expr =
        (builtins.tryEval
          (evalModuleTree {
            modules = [
              zDecl
              zWrapped
            ];
          }).config.a
        ).value;
      expected = 1;
    };
    # F1 — nixpkgs equivalence over the same arms: the file each engine attributes the definition
    # to agrees string for string, wrapped or direct, and through `deferredModule`. Scope: this is
    # the IMPORT-site attribution of content passed through an unattributed wrapper. A PATH module
    # whose own content names `_file` diverges (gen-merge names the path, nixpkgs the declared
    # `_file`), a pre-existing precedence difference this threading leaves unmoved.
    test-nixpkgs-equivalence-wrapped-and-direct = {
      expr = builtins.mapAttrs (_: mods: genMergeFiles mods == nixpkgsFiles mods) f1Arms // {
        deferred =
          genMergeFiles [ (deferredOf evalModuleTree mkOption t) ]
          == nixpkgsFiles [ (deferredOf nixpkgsLib.evalModules nixpkgsLib.mkOption nixpkgsLib.types) ];
        referenceReadsF = map (mods: nixpkgsFiles mods) (builtins.attrValues f1Arms);
      };
      expected = {
        direct = true;
        sdmlAttrs = true;
        sdmlFn = true;
        manualWrapper = true;
        deferred = true;
        referenceReadsF = [
          [ F ]
          [ F ]
          [ F ]
          [ F ]
        ];
      };
    };
  };
}
