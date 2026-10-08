# A PARTIAL SUBMODULE keeps its declared options' priorities (den-hoag-5ov3p), the declared-plane twin of
# `partialAttrsOf` (./partial-fold.nix): each declared option's value is its winning definitions merged,
# under the priority that selected them, and a default-only option is its declared default at
# `mkOptionDefault`. So folding the evaluation's value with further definitions is the fold over all of them.
#
# ★ THE REFERENCE IS nixpkgs OVER ALL THE DEFINITIONS AT ONCE, and each cell runs it. The gen arm folds the
# first group through a `partialSubmodule`'s declared `listOf str` option, then folds that value with the
# second group under `anything`. Lists are compared as sets: which definitions win is the cell's subject,
# and the order axis is den-hoag-3849t P4's bound.
#
# RED: the realizer's partial `mergeOption` returning the bare value gives both groups where the first
# group's `mkForce` should win (`force`, `twoInA`), both where its `mkDefault` should lose (`default`), the
# second group alone where both are forced (`tie`), and the empty default where the second group's
# `mkDefault` should win (`defaultOnly`, `emptySeed`). The empty-seed arm on a full knot gives the last.
{
  genMerge,
  genTypes,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  np = nixpkgsLib;
  t = gm.types;
  inherit (builtins) deepSeq tryEval;
  # the two groups, written with constructor set `L`; `a` is a list of module definitions of `x`, or
  # `null` for an option nothing defines (the evaluation's empty seed)
  fx = L: {
    force = {
      a = [ { l = L.mkForce [ "Q" ]; } ];
      b = [ { l = [ "X" ]; } ];
    };
    default = {
      a = [ { l = L.mkDefault [ "Q" ]; } ];
      b = [ { l = [ "X" ]; } ];
    };
    tie = {
      a = [ { l = L.mkForce [ "Q" ]; } ];
      b = [ { l = L.mkForce [ "X" ]; } ];
    };
    twoInA = {
      a = [
        { l = L.mkForce [ "Q" ]; }
        { l = [ "R" ]; }
      ];
      b = [ { l = [ "X" ]; } ];
    };
    plain = {
      a = [ { l = [ "Q" ]; } ];
      b = [ { l = [ "X" ]; } ];
    };
    # the first group never writes `l`: the declared default is its only definition
    defaultOnly = {
      a = [ { } ];
      b = [ { l = L.mkDefault [ "X" ]; } ];
    };
    # the first group never defines `x` at all: the child is evaluated over an empty seed
    emptySeed = {
      a = null;
      b = [ { l = L.mkDefault [ "X" ]; } ];
    };
  };
  lopt = L: {
    options.l = L.mkOption {
      type = L.types.listOf L.types.str;
      default = [ ];
    };
  };
  # group a through the partial submodule: the evaluation's value at `x`
  partialOf =
    c:
    removeAttrs
      (gm.evalModuleTree { } (
        [ { options.x = gm.mkOption { type = gm.partialSubmodule (lopt gm); }; } ]
        ++ map (d: { x = d; }) (if c.a == null then [ ] else c.a)
      )).config.x
      [ "_module" ];
  gen =
    n:
    let
      c = (fx gm).${n};
    in
    (t.anything.merge [ "o" ] (
      map (value: {
        file = "f";
        inherit value;
      }) ([ (partialOf c) ] ++ c.b)
    )).l;
  nixpkgs =
    n:
    let
      c = (fx np).${n};
    in
    (np.evalModules {
      modules = [ (lopt np) ] ++ (if c.a == null then [ ] else c.a) ++ c.b;
    }).config.l;
  sort = builtins.sort builtins.lessThan;
  ref = {
    force = [ "Q" ];
    default = [ "X" ];
    tie = [
      "Q"
      "X"
    ];
    twoInA = [ "Q" ];
    plain = [
      "Q"
      "X"
    ];
    defaultOnly = [ "X" ];
    emptySeed = [ "X" ];
  };
  mods = [ (lopt gm) ];
  # a declared `listOf str` with no default
  mopt = L: { options.m = L.mkOption { type = L.types.listOf L.types.str; }; };
  # a module set declaring one `partialSubmodule` option `x` over `m`, evaluated with one definition of `x`
  # (`null`: none), and its value
  partialOf' =
    m: def:
    removeAttrs
      (gm.evalModuleTree { } (
        [ { options.x = gm.mkOption { type = gm.partialSubmodule (m gm); }; } ]
        ++ (if def == null then [ ] else [ { x = def; } ])
      )).config.x
      [ "_module" ];
  # the partial value folded later with one more definition under `anything`
  laterFold =
    v: second:
    t.anything.merge
      [ "o" ]
      [
        {
          file = "a";
          value = v;
        }
        {
          file = "b";
          value = second;
        }
      ];
  # a module declaring option `k` of type `outer (partialSubmodule? lopt)`: `nestedIn' k outer` nests a
  # `partialSubmodule`; `nestedIn outer` is the module function `partialOf'` takes, nesting at `y`
  nestedIn' =
    k: outer: outer { options.${k} = gm.mkOption { type = gm.partialSubmodule (lopt gm); }; };
  nestedIn = outer: L: { options.y = L.mkOption { type = outer (lopt gm); }; };
  bopt = {
    options.b = gm.mkOption {
      type = t.bool;
      default = false;
    };
  };
  refused = e: !(tryEval (deepSeq e e)).success;
  mixed =
    first: second:
    (gm.evalModuleTree { } [
      { options.x = gm.mkOption { type = first (lopt gm); }; }
      { options.x = gm.mkOption { type = second bopt; }; }
      { x.l = gm.mkForce [ "a" ]; }
    ]).config.x;
in
{
  flake.tests.partial-submodule =
    builtins.listToAttrs (
      map (n: {
        name = "test-${n}";
        value = {
          expr = {
            gen = sort (gen n);
            nixpkgs = sort (nixpkgs n);
          };
          expected = {
            gen = ref.${n};
            nixpkgs = ref.${n};
          };
        };
      }) (builtins.attrNames ref)
    )
    // {
      # the partial value's shape: a definition at the winning priority, the plain value at the default, the
      # declared default at `mkOptionDefault` when nothing else is defined, with one empty definition or none
      test-the-partial-value-is-a-definition = {
        expr = builtins.mapAttrs (n: _: (partialOf (fx gm).${n}).l) {
          force = null;
          default = null;
          plain = null;
          defaultOnly = null;
          emptySeed = null;
        };
        expected = {
          force = {
            _type = "override";
            priority = 50;
            content = [ "Q" ];
          };
          default = {
            _type = "override";
            priority = 1000;
            content = [ "Q" ];
          };
          plain = [ "Q" ];
          defaultOnly = {
            _type = "override";
            priority = 1500;
            content = [ ];
          };
          emptySeed = {
            _type = "override";
            priority = 1500;
            content = [ ];
          };
        };
      };
      # Its identity (ADR-0034): the constructor tag enters the mint, so a `partialSubmodule` and a
      # `submodule` over one module set are two types, while the name, which both keep, is `submodule`.
      test-identity-is-the-constructors = {
        expr = {
          same = genTypes.typeEq (gm.partialSubmodule mods) (gm.partialSubmodule mods);
          mixed = genTypes.typeEq (t.submodule mods) (gm.partialSubmodule mods);
          control = genTypes.typeEq (t.submodule mods) (t.submodule mods);
          name = (gm.partialSubmodule mods).name;
        };
        expected = {
          same = true;
          mixed = false;
          control = true;
          name = "submodule";
        };
      };
      # A mixed redeclaration has no union (one value would be definitions, the other data), so it refuses
      # catchably in both orders; two partial declarations union as two submodules do. The message is
      # pinned in ../tests-error.nix (`partial-submodule`).
      test-mixed-redeclaration-refuses-in-both-orders = {
        expr = {
          plainFirst = refused (mixed t.submodule gm.partialSubmodule);
          partialFirst = refused (mixed gm.partialSubmodule t.submodule);
          bothPartial = mixed gm.partialSubmodule gm.partialSubmodule;
        };
        expected = {
          plainFirst = true;
          partialFirst = true;
          bothPartial = {
            b = {
              _type = "override";
              priority = 1500;
              content = false;
            };
            l = {
              _type = "override";
              priority = 50;
              content = [ "a" ];
            };
          };
        };
      };
      # THE BOUND (den-hoag-5ov3p landing gate K1, the identity ruled; README): an option with neither a
      # definition nor a declared default moves nothing, so a later fold that supplies none serves no key,
      # where nixpkgs serves the type's empty value. Pinned as the stated divergence.
      # RED: the no-winners arm emitting the empty value as a definition gives `m` beside nixpkgs' `[ ]`.
      test-no-definition-and-no-default-moves-nothing = {
        expr = {
          partial = partialOf' mopt null;
          later = (laterFold (partialOf' mopt null) { }) ? m;
          nixpkgs = (np.evalModules { modules = [ (mopt np) ]; }).config.m;
        };
        expected = {
          partial.m = {
            _type = "if";
            condition = false;
            content = { };
          };
          later = false;
          nixpkgs = [ ];
        };
      };
      # A nested tree keeps its priorities only when it is itself declared `partialSubmodule` (README): a
      # `submodule` inside a partial tree folds fully, so its declared default, carried as data at the default
      # priority, beats a later `mkDefault`; a nested `partialSubmodule` carries it at `mkOptionDefault`, and the
      # later `mkDefault` wins as it does in nixpkgs over all the definitions at once.
      test-a-nested-tree-keeps-its-priorities-only-when-partial = {
        expr = {
          full =
            (laterFold (partialOf' (nestedIn t.submodule) { y = { }; }) { y.l = gm.mkDefault [ "X" ]; }).y.l;
          partial =
            (laterFold (partialOf' (nestedIn gm.partialSubmodule) { y = { }; }) { y.l = gm.mkDefault [ "X" ]; })
            .y.l;
          nixpkgs =
            (np.evalModules {
              modules = [
                { options.y = np.mkOption { type = np.types.submodule (lopt np); }; }
                { y = { }; }
                { y.l = np.mkDefault [ "X" ]; }
              ];
            }).config.y.l;
        };
        expected = {
          full = [ ];
          partial = [ "X" ];
          nixpkgs = [ "X" ];
        };
      };
      # The nixpkgs mount serves the FULL fold: nothing folds a foreign evaluation's value again, so a
      # definition there would be read as data (lib/modules.nix `nestedTreeAt`). gen's own evaluation
      # serves the partial value.
      test-the-nixpkgs-mount-serves-the-full-fold = {
        expr = {
          nixpkgs =
            (np.evalModules {
              modules = [
                { options.x = np.mkOption { type = gm.partialSubmodule (lopt gm); }; }
                { x.l = np.mkForce [ "Q" ]; }
              ];
            }).config.x.l;
          gen =
            (gm.evalModuleTree { } [
              { options.x = gm.mkOption { type = gm.partialSubmodule (lopt gm); }; }
              { x.l = gm.mkForce [ "Q" ]; }
            ]).config.x.l;
        };
        expected = {
          nixpkgs = [ "Q" ];
          gen = {
            _type = "override";
            priority = 50;
            content = [ "Q" ];
          };
        };
      };
      # ... at the mounted option's own type only (README): a `partialSubmodule` nested below it is a child of
      # the mounted evaluation and stays partial, so a nixpkgs consumer at depth 1 reads its definition.
      # RED: a partial knot propagated to every depth of the bridge moves the depth-0 value; one dropped from
      # `childTree` moves this one.
      test-the-nixpkgs-mount-is-full-at-depth-0-only = {
        expr = {
          depth0 =
            (np.evalModules {
              modules = [
                { options.x = np.mkOption { type = gm.partialSubmodule (lopt gm); }; }
                { x.l = np.mkForce [ "Q" ]; }
              ];
            }).config.x.l;
          depth1 =
            (np.evalModules {
              modules = [
                { options.w = np.mkOption { type = nestedIn' "x" t.submodule; }; }
                { w.x.l = np.mkForce [ "Q" ]; }
              ];
            }).config.w.x.l;
        };
        expected = {
          depth0 = [ "Q" ];
          depth1 = {
            _type = "override";
            priority = 50;
            content = [ "Q" ];
          };
        };
      };
    };
}
