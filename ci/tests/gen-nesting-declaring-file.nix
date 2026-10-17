# GEN'S OWN NESTING TYPES NAME THE DECLARING FILE (den-hoag-fhggb OQ-A): where nixpkgs' `evalModules`
# over a nixpkgs nesting type labels the type's own modules with the file of the declaration carrying
# it (`mergeOptionDecls` → `fixupOptionType`, `collectStructuredModules`' `parentFile`), gen-merge's
# engine over gen's twin type labels them the same. The file enters as the nested tree's ROOT
# importer entry (`nestedGroups`' `root`), so no module node and no declaration address moves
# (ci/tests/nesting-keys-children.nix, ci/tests/declaration-address.nix).
#
# - Every forwarding container over a gen nesting type, gen's or a stock one (`interface.forwardsModuleSet`):
#   `attrsOf`, `lazyAttrsOf`, `listOf`, `nullOr`, a nixpkgs `attrsOf` above or below gen's, nixpkgs'
#   `addCheck`, nixpkgs' `attrListOf` (RED at gen-merge 1d5741e: `[ "<unknown-file>" ]`, its stock arm stepping
#   only the containers it named; den-hoag-j2ryo); never through a union (`either`), as nixpkgs' `either` forwards no module set.
# - Every gen nesting constructor: `submodule`, an evaluation's own `.type`, `withArgs`, a type stating
#   `nests.declAt`, depth two, and an option declared inside one.
# - Every collection of the nested tree: the empty child (a lazy key whose definitions are all
#   discharged), a set stating `disabledModules` (the removal walk), and a set whose declarations
#   the guard's staged passes resolve. Their refusals are ci/tests-error.nix's `gen-nesting-declaring-file`.
#
# Every twin cell is one expression read on both engines: `expr` is gen-merge's engine over gen's types and
# `expected` is nixpkgs' engine over nixpkgs' types. RED (no root entry): `[ "<unknown-file>" ]` where
# nixpkgs reads `[ "decl.nix" ]`.
{ genMerge, nixpkgsLib, ... }:
let
  read =
    x:
    let
      r = builtins.tryEval (builtins.deepSeq x x);
    in
    if r.success then r.value else "refused";
  cells =
    eng:
    let
      gen = eng == "gen";
      L = if gen then genMerge else nixpkgsLib;
      T = L.types;
      NT = nixpkgsLib.types;
      inherit (L) mkOption;
      ev =
        mods: if gen then genMerge.evalModuleTree { } mods else nixpkgsLib.evalModules { modules = mods; };
      # the inner module states no `_file` and reads its own `options` argument
      inner =
        { options, ... }:
        {
          options.inner = mkOption {
            type = T.int;
            default = 3;
          };
          options.seen = mkOption { default = options.inner.declarations; };
        };
      sub = T.submodule inner;
      mid =
        { options, ... }:
        {
          options.d = mkOption {
            type = sub;
            default = { };
          };
          options.dDecl = mkOption { default = options.d.declarations; };
        };
      outer =
        { options, ... }:
        {
          options.t = mkOption {
            type = T.int;
            default = 1;
          };
          options.tDecl = mkOption { default = options.t.declarations; };
        };
      treeType =
        (
          if gen then
            genMerge.evalModuleTree { } [ inner ]
          else
            nixpkgsLib.evalModules { modules = [ inner ]; }
        ).type;
      withArgsType =
        if gen then
          sub.withArgs { a = 1; }
        else
          T.submoduleWith {
            modules = [ inner ];
            specialArgs.a = 1;
          };
      # nixpkgs has no declaration address, so the twin of a type stating `nests.declAt` is the plain type
      declAtType =
        if gen then
          T.defineType (
            sub
            // {
              nests = sub.nests // {
                declAt = true;
              };
            }
          )
        else
          sub;
      # a gen nesting type under a nixpkgs container, in gen's engine; the twin is all nixpkgs
      mx1 = if gen then T.attrsOf (NT.attrsOf sub) else NT.attrsOf (NT.attrsOf sub);
      mx2 = NT.attrsOf sub;
      # an option node whose leafness reads `options': the guard's spine does not resolve, the staged passes do
      staged =
        { options, ... }:
        {
          options.extra = if options ? inner then mkOption { default = 1; } else { };
        };
      decl = {
        _file = "decl.nix";
        options = {
          s = mkOption {
            type = sub;
            default = { };
          };
          at = mkOption {
            type = T.attrsOf sub;
            default = { };
          };
          lz = mkOption {
            type = T.lazyAttrsOf sub;
            default = { };
          };
          ls = mkOption {
            type = T.listOf sub;
            default = [ ];
          };
          no = mkOption {
            type = T.nullOr sub;
            default = null;
          };
          tr = mkOption {
            type = treeType;
            default = { };
          };
          wa = mkOption {
            type = withArgsType;
            default = { };
          };
          d2 = mkOption {
            type = T.submodule mid;
            default = { };
          };
          dg = mkOption {
            type = T.submodule outer;
            default = { };
          };
          ow = mkOption {
            type = T.submodule {
              _file = "own.nix";
              imports = [ inner ];
            };
            default = { };
          };
          ei = mkOption {
            type = T.either T.int sub;
            default = { };
          };
          ei2 = mkOption {
            type = T.either (T.attrsOf sub) T.str;
            default = { };
          };
          ne = mkOption {
            type = T.nullOr (T.either T.int sub);
            default = null;
          };
          rd = mkOption {
            type = sub;
            default = { };
          };
          ut = mkOption { default = { }; };
          dm = mkOption {
            type = T.submodule {
              disabledModules = [ "/nowhere/x.nix" ];
              imports = [ inner ];
            };
            default = { };
          };
          mx1 = mkOption {
            type = mx1;
            default = { };
          };
          mx2 = mkOption {
            type = mx2;
            default = { };
          };
          mx3 = mkOption {
            type = T.listOf (T.nullOr (T.attrsOf sub));
            default = [ ];
          };
          ac = mkOption {
            type = NT.addCheck sub (_: true);
            default = { };
          };
          # nixpkgs' `attrListOf` forwards its element's module set as `listOf` does (den-hoag-j2ryo's table)
          al = mkOption {
            type = NT.attrListOf sub;
            default = { };
          };
          da = mkOption {
            type = declAtType;
            default = { };
          };
          em = mkOption {
            type = T.lazyAttrsOf sub;
            default = { };
          };
          st = mkOption {
            type = T.submodule {
              imports = [
                inner
                staged
              ];
            };
            default = { };
          };
        };
      };
      decl2 = {
        _file = "decl2.nix";
        options.rd = mkOption { type = T.submodule { }; };
        options.ut = mkOption { type = sub; };
      };
      parent = {
        _file = "parent.nix";
        imports = [
          {
            options.ih = mkOption {
              type = sub;
              default = { };
            };
          }
        ];
      };
      freeform = {
        _file = "ff.nix";
        freeformType = T.attrsOf sub;
      };
      def = {
        _file = "def.nix";
        config = {
          at.k = { };
          lz.k = { };
          ls = [ { } ];
          no = { };
          ei = { };
          ei2.k = { };
          ne = { };
          fr = { };
          mx1.k.j = { };
          mx2.k = { };
          mx3 = [ { k = { }; } ];
          al.k = { };
          em.k = L.mkIf false { };
        };
      };
      r = ev [
        decl
        decl2
        parent
        freeform
        def
      ];
      c = r.config;
    in
    {
      S = read c.s.seen;
      At = read c.at.k.seen;
      Lz = read c.lz.k.seen;
      Ls = read (builtins.head c.ls).seen;
      No = read c.no.seen;
      Tr = read c.tr.seen;
      Wa = read c.wa.seen;
      D2 = read c.d2.d.seen;
      D2decl = read c.d2.dDecl;
      Dg = read c.dg.tDecl;
      Ut = read c.ut.seen;
      Dm = read c.dm.seen;
      Mx1 = read c.mx1.k.j.seen;
      Mx2 = read c.mx2.k.seen;
      Mx3 = read (builtins.head c.mx3).k.seen;
      Ac = read c.ac.seen;
      Al = read (builtins.head c.al).k.seen;
      Ih = read c.ih.seen;
      DeclAt = read c.da.seen;
      Empty = read c.em.k.seen;
      Staged = read c.st.seen;
      # controls: a module's own `_file`, a redeclared option, the served type, and every shape where nixpkgs
      # locates nothing (a union member, a union over a container, a freeform type)
      Ow = read c.ow.seen;
      Rd = read c.rd.seen;
      ServedS = read ((r.options.s.type.getSubOptions [ ]).inner.declarations);
      Ei = read c.ei.seen;
      Ei2 = read c.ei2.k.seen;
      Ne = read c.ne.seen;
      Fr = read c.fr.seen;
    };
  gen = cells "gen";
  nixpkgs = cells "nixpkgs";
in
{
  flake.tests.gen-nesting-declaring-file =
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
      # the reference arm is live: no twin cell agrees by both engines refusing it
      test-nixpkgs-serves-every-cell = {
        expr = builtins.filter (name: nixpkgs.${name} == "refused") (builtins.attrNames nixpkgs);
        expected = [ ];
      };
    };
}
