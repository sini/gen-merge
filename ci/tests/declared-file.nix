# THE DECLARING FILE on the evaluation's surface (den-hoag-5q139, den-hoag-fhggb): where nixpkgs'
# `evalModules` names the file that declared an option, gen-merge names the same one.
#
# - A once-declared option whose type states a module set is served that type located at its
#   declaring file (nixpkgs' `mergeOptionDecls` → `fixupOptionType`), so a sub-option read through
#   the served type names the file, at `submodule`, `attrsOf`, `listOf`, `attrTag` and gen's own types.
# - The declared default's definition names the declaring file wherever definitions leave the fold
#   for a reader (nixpkgs' `evalOptionValue`, `head opt.declarations`): the type's own merge, in both
#   of the order pass's arms. The engine's own `_module.*` keys name `lib/modules.nix`, as nixpkgs
#   names its `internalModule`. The untyped and leaf folds' refusals are ci/tests-error.nix's
#   `declared-default-file`.
# - The nested evaluation a nixpkgs module-set type's merge runs reads its modules located at the file
#   of the declaration that carries the type (the fold's mount, `homedRootFixed`), so the inner
#   module's own `options` argument names it, an untyped declaration before it included; the served
#   type takes the same typed declaration. The nested conflicts are ci/tests-error.nix's
#   `nested-declaring-file`.
#
# Every twin cell is one expression read on both engines with nixpkgs' `mkOption` and types: `expr` is
# gen-merge's reading and `expected` is nixpkgs'. A refusal reads as `"refused"` on either side.
{
  evalRequest,
  genMerge,
  nixpkgsLib,
  ...
}:
let
  L = nixpkgsLib;
  TY = L.types;
  read =
    x:
    let
      r = builtins.tryEval (builtins.deepSeq x x);
    in
    if r.success then r.value else "refused";
  decl = m: m // { _file = "decl.nix"; };
  # the inner module states no `_file`: its declarations are the declaring module's
  sub = TY.submodule { options.addr = L.mkOption { type = TY.str; }; };
  subDecl = o: (o.type.getSubOptions [ ]).addr.declarations;
  filesType = L.mkOptionType {
    name = "files";
    merge = _loc: defs: map (d: d.file) defs;
  };

  cells =
    ev:
    let
      opts = ms: (ev { modules = ms; }).options;
      defaultFiles =
        default:
        read
          (ev {
            modules = [
              (decl {
                options.files = L.mkOption {
                  type = filesType;
                  inherit default;
                };
              })
              {
                _file = "def.nix";
                config.files = L.mkOptionDefault "x";
              }
            ];
          }).config.files;
      attrTagDocs =
        let
          o = opts [
            (decl {
              options.submodules = L.mkOption {
                type = TY.attrsOf (
                  TY.attrTag {
                    foo = L.mkOption {
                      type = TY.submodule { options.bar = L.mkOption { type = TY.int; }; };
                    };
                  }
                );
              };
            })
          ];
        in
        builtins.filter (d: d.name == "submodules.<name>.foo.bar") (L.optionAttrSetToDocList o);
      # declared twice, by `d1.nix` and `d2.nix`, with a type whose module set throws when read
      throwingTwice = opts [
        {
          _file = "d1.nix";
          options.t = L.mkOption {
            type = L.mkOptionType {
              name = "ts2";
              getSubModules = throw "getSubModules forced";
            };
          };
        }
        {
          _file = "d2.nix";
          options.t = L.mkOption { };
        }
      ];
      ownCheck = {
        _file = "E";
        options._module.check = L.mkOption { type = TY.bool; };
      };
      # the inner module states no `_file` and reads its own `options` argument
      inner =
        { options, ... }:
        {
          options.inner = L.mkOption {
            type = TY.int;
            default = 3;
          };
          options.seen = L.mkOption { default = options.inner.declarations; };
        };
      typedAt = f: {
        _file = f;
        options.s = L.mkOption {
          type = TY.submodule inner;
          default = { };
        };
      };
      untypedAt = f: {
        _file = f;
        options.s = L.mkOption { description = "untyped"; };
      };
      cfg = ms: (ev { modules = ms; }).config;
      nested = cfg [
        (decl {
          options.at = L.mkOption {
            type = TY.attrsOf (TY.submodule inner);
            default = { };
          };
          options.ls = L.mkOption {
            type = TY.listOf (TY.submodule inner);
            default = [ ];
          };
          options.g.s = L.mkOption {
            type = TY.submodule inner;
            default = { };
          };
        })
        (typedAt "decl.nix")
        {
          _file = "def.nix";
          config.at.k = { };
          config.ls = [ { } ];
        }
      ];
      # declared in `decl.nix` and in `decl2.nix`, each with its own module: the redeclared path, whose
      # modules are located per declaration (`fixupModuleSets`)
      redeclared = cfg [
        (typedAt "decl.nix")
        {
          _file = "decl2.nix";
          options.s = L.mkOption {
            type = TY.submodule (
              { options, ... }:
              {
                options.inner2 = L.mkOption {
                  type = TY.int;
                  default = 9;
                };
                options.seen2 = L.mkOption { default = options.inner2.declarations; };
              }
            );
          };
        }
      ];
    in
    {
      subDeclSubmodule = read (
        subDecl (opts [ (decl { options.one = L.mkOption { type = sub; }; }) ]).one
      );
      subDeclAttrsOf = read (
        subDecl (opts [ (decl { options.hosts = L.mkOption { type = TY.attrsOf sub; }; }) ]).hosts
      );
      subDeclListOf = read (
        subDecl (opts [ (decl { options.lst = L.mkOption { type = TY.listOf sub; }; }) ]).lst
      );
      subDeclAttrTag = read (map (d: d.declarations) attrTagDocs);
      # the type's own fold, in the order pass's unmarked arm and its `mkOrder` arm
      defaultFileToType = defaultFiles "d";
      defaultFileToTypeOrdered = defaultFiles (L.mkBefore "d");
      # the engine's own declaration of `_module.check` comes first, beside the redeclaring file
      defaultRedeclaredCheck = read (opts [ ownCheck ])._module.check.files;
      # the served type of a redeclared option reads its module set: one that throws refuses the read,
      # as nixpkgs' `mergeOptionDecls` does
      redeclaredThrowingSubModules = read throwingTwice.t.type.name;
      # the nested evaluation's own `options` argument
      optionsArgSubmodule = read nested.s.seen;
      optionsArgAttrsOf = read nested.at.k.seen;
      optionsArgListOf = read (map (x: x.seen) nested.ls);
      optionsArgGroup = read nested.g.s.seen;
      optionsArgRedeclared = read redeclared.s.seen2;
      # an untyped declaration first: the typed one's file, not the first declarer's
      optionsArgUntypedFirst =
        read
          (cfg [
            (untypedAt "decl.nix")
            (typedAt "decl2.nix")
          ]).s.seen;
      optionsArgTypedFirst =
        read
          (cfg [
            (typedAt "decl.nix")
            (untypedAt "decl2.nix")
          ]).s.seen;
      servedUntypedFirst = read (
        (
          (opts [
            (untypedAt "decl.nix")
            (typedAt "decl2.nix")
          ]).s.type.getSubOptions
            [ ]
        ).inner.declarations
      );
    };
  gen = cells evalRequest;
  nixpkgs = cells L.evalModules;

  # gen-merge's own types, declared once in `decl.nix`: no nixpkgs reading, so the expected file is
  # stated
  native =
    let
      gm = genMerge;
      gsub = gm.types.submodule { options.addr = gm.mkOption { type = gm.types.str; }; };
      o =
        (gm.evalModuleTree { } [
          {
            _file = "decl.nix";
            options.hosts = gm.mkOption { type = gm.types.attrsOf gsub; };
            options.one = gm.mkOption { type = gsub; };
          }
        ]).options;
    in
    {
      expr = read {
        hosts = subDecl o.hosts;
        one = subDecl o.one;
      };
      expected = {
        hosts = [ "decl.nix" ];
        one = [ "decl.nix" ];
      };
    };
in
{
  flake.tests.declared-file =
    builtins.listToAttrs (
      map (name: {
        name = "test-${name}-equals-nixpkgs";
        value = {
          expr = gen.${name};
          expected = nixpkgs.${name};
        };
      }) (builtins.attrNames gen)
    )
    // {
      test-subDeclGenNative-names-the-declaring-file = native;
    };
}
