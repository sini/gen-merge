# A PATH-imported module is named by the `_file` its own content sets, else by its path, as in
# nixpkgs' `unifyModuleSyntax` (`toString m._file or file`; den-hoag-6fqay, ADR-0039). The importer's
# file is never consulted for a path module. One origin, `moduleEntries`, with three `_file` branches
# (the tree's root, an unscoped importer, a scoped importer): one cell per branch, since a revert of
# one branch alone is invisible to a cell that only imports at the root. The refusal-TEXT arms live on
# `testsError` (`../tests-error.nix`, `path-module-own-file`).
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  inherit (gm) evalModuleTree mkOption lint;
  t = gm.types;
  fx = ./_fixtures;
  pDef = fx + "/own-file-def.nix";
  pBogus = fx + "/own-file-bogus.nix";
  pDecl = fx + "/own-file-decl.nix";
  pChain = fx + "/own-file-chain.nix";
  pLint = fx + "/own-file-lint.nix";
  pLintFn = fx + "/own-file-lint-fn.nix";
  pValue = fx + "/own-file-path-value.nix";
  # The same content with no `_file`: the path is the file.
  pPlain = fx + "/own-file-plain.nix";
  PF = "/real/PF.nix";

  declX = {
    options.x = mkOption { type = t.int; };
  };
  xsDecl = {
    options.xs = mkOption {
      type = t.listOf t.str;
      default = [ ];
    };
  };
  # The three `moduleEntries` branches, as importers of one module `m`.
  atRoot = m: [ m ];
  underUnscoped = m: [ { imports = [ m ]; } ];
  underScoped = m: [
    {
      __reservedKeys.names = { };
      imports = [ m ];
    }
  ];
  branches = {
    root = atRoot;
    unscoped = underUnscoped;
    scoped = underScoped;
  };
  defsOf = mods: map (d: d.file) (evalModuleTree { modules = [ declX ] ++ mods; }).provenance.x.defs;
  winnersOf =
    mods: map (d: d.file) (evalModuleTree { modules = [ declX ] ++ mods; }).provenance.x.winners;
  und =
    mods:
    map (u: u.file)
      (evalModuleTree {
        modules = mods;
        check = false;
      }).undeclared;
  lintFiles =
    mods:
    map (f: f.file) (lint {
      modules = [ xsDecl ] ++ mods;
    });
  # The engine's definition files of `xs`, less the option's own default.
  xsDefs =
    mods:
    builtins.filter (f: f != "<default>") (
      map (d: d.file) (evalModuleTree { modules = [ xsDecl ] ++ mods; }).provenance.xs.defs
    );
  # The reference side: the same path module through nixpkgs' `evalModules`.
  nixpkgsDefs =
    mods:
    map (d: d.file)
      (nixpkgsLib.evalModules {
        modules = [ { options.x = nixpkgsLib.mkOption { type = nixpkgsLib.types.int; }; } ] ++ mods;
      }).options.x.definitionsWithLocations;
  nixpkgsLintDefs =
    mods:
    map (d: d.file)
      (nixpkgsLib.evalModules {
        modules = [
          {
            options.xs = nixpkgsLib.mkOption {
              type = nixpkgsLib.types.listOf nixpkgsLib.types.str;
              default = [ ];
            };
          }
        ]
        ++ mods;
      }).options.xs.definitionsWithLocations;
  declsOf =
    ev: mo: ty:
    (ev {
      modules = [ pDecl ];
      specialArgs = {
        mkOption = mo;
        types = ty;
      };
    }).options.x.declarations;
in
{
  flake.tests.path-module-own-file = {
    # Branch 1 / 2 / 3 — the definition's file, per `moduleEntries` branch. A revert of one branch
    # leaves the other two cells green.
    test-root-path-module-defs-read-its-own-file = {
      expr = {
        defs = defsOf (branches.root pDef);
        winners = winnersOf (branches.root pDef);
      };
      expected = {
        defs = [ PF ];
        winners = [ PF ];
      };
    };
    test-unscoped-importer-path-module-defs-read-its-own-file = {
      expr = {
        defs = defsOf (branches.unscoped pDef);
        winners = winnersOf (branches.unscoped pDef);
      };
      expected = {
        defs = [ PF ];
        winners = [ PF ];
      };
    };
    test-scoped-importer-path-module-defs-read-its-own-file = {
      expr = {
        defs = defsOf (branches.scoped pDef);
        winners = winnersOf (branches.scoped pDef);
      };
      expected = {
        defs = [ PF ];
        winners = [ PF ];
      };
    };
    # The string-path arm (`isPathString`): a string naming an absolute path is loaded as a path.
    test-string-path-module-reads-its-own-file-in-every-branch = {
      expr = builtins.mapAttrs (_: wrap: defsOf (wrap (toString pDef))) branches;
      expected = {
        root = [ PF ];
        unscoped = [ PF ];
        scoped = [ PF ];
      };
    };
    # Reference equivalence: nixpkgs reads the same file for the same module, in each branch.
    test-path-module-file-equals-nixpkgs = {
      # nixpkgs has no reservation scope: the scoped branch has no reference arm.
      expr = {
        root = defsOf (branches.root pDef) == nixpkgsDefs (branches.root pDef);
        unscoped = defsOf (branches.unscoped pDef) == nixpkgsDefs (branches.unscoped pDef);
        referenceReadsPF = nixpkgsDefs [ pDef ];
      };
      expected = {
        root = true;
        unscoped = true;
        referenceReadsPF = [ PF ];
      };
    };
    # `undeclared[].file`, per branch.
    test-undeclared-reads-the-path-modules-own-file = {
      expr = builtins.mapAttrs (_: wrap: und (wrap pBogus)) branches;
      expected = {
        root = [ PF ];
        unscoped = [ PF ];
        scoped = [ PF ];
      };
    };
    # An option declared by a path module: `declarations` reads its `_file`, as nixpkgs'.
    test-declarations-read-the-path-modules-own-file = {
      expr = {
        genMerge = declsOf evalModuleTree mkOption t;
        nixpkgs = declsOf nixpkgsLib.evalModules nixpkgsLib.mkOption nixpkgsLib.types;
      };
      expected = {
        genMerge = [ "/real/PD.nix" ];
        nixpkgs = [ "/real/PD.nix" ];
      };
    };
    # A child with no `_file` of its own, imported by a path module that names itself, inherits the
    # path module's `_file` (nixpkgs' `parentFile` is the unified module's `_file`).
    test-unattributed-child-inherits-the-path-modules-own-file = {
      expr = und [ pChain ];
      expected = [ "/real/CH.nix" ];
    };
    # Controls: the same content with no `_file` is named by its path; as an attrset, by its `_file`.
    test-control-path-module-without-file-is-named-by-its-path = {
      expr = {
        genMerge = defsOf [ pPlain ];
        nixpkgs = nixpkgsDefs [ pPlain ];
      };
      expected = {
        genMerge = [ (toString pPlain) ];
        nixpkgs = [ (toString pPlain) ];
      };
    };
    test-control-attrset-module-with-file-is-named-by-its-file = {
      expr = defsOf [
        {
          _file = PF;
          config.x = 1;
        }
      ];
      expected = [ PF ];
    };
    # `_file` given as a PATH VALUE naming a different file: the file read is that path as a string
    # (the HEAD reading is the module's own path, a different string).
    test-path-module-file-given-as-a-path-value-reads-that-path = {
      expr =
        let
          fs = defsOf [ pValue ];
        in
        {
          types = map builtins.typeOf fs;
          equalsTheNamedPath = fs == [ (toString pDef) ];
          notItsOwnPath = fs != [ (toString pValue) ];
        };
      expected = {
        types = [ "string" ];
        equalsTheNamedPath = true;
        notItsOwnPath = true;
      };
    };
    # lint: an attrset path module's finding reads its `_file`, equal to the engine's.
    test-lint-attrset-path-module-reads-its-own-file = {
      expr = {
        lint = lintFiles [ pLint ];
        engine = xsDefs [ pLint ];
        nixpkgs = nixpkgsLintDefs [ pLint ];
      };
      expected = {
        lint = [ "/real/LN.nix" ];
        engine = [ "/real/LN.nix" ];
        nixpkgs = [ "/real/LN.nix" ];
      };
    };
    # P1 — lint != engine for a FUNCTION path module that sets `_file`: the lint applies no module,
    # so it names the path where the engine (and nixpkgs) name the `_file`. A stated boundary
    # (lint.nix `collect` RESIDUE), pinned here so a change to either side moves a cell.
    test-lint-function-path-module-names-its-path-where-the-engine-names-its-file = {
      expr = {
        lint = lintFiles [ pLintFn ];
        engine = xsDefs [ pLintFn ];
        nixpkgs = nixpkgsLintDefs [ pLintFn ];
      };
      expected = {
        lint = [ (toString pLintFn) ];
        engine = [ "/real/LF.nix" ];
        nixpkgs = [ "/real/LF.nix" ];
      };
    };
  };
}
