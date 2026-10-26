# A DECLARED RECORD FOLDS BY ITS COMPLETION'S FOLD (den-hoag-d2myd, ADR-0039 serve half). A `//` copy that restates a
# record's fold (`mergeDefs`) and keeps its `merge` states two folds that disagree, and nixpkgs' `evalModules` runs the
# `merge`. Where gen-merge's engine picks a declared record's fold (an option's type, the freeform plane, a gen
# container's element on the threaded twin, also when a consumer's container hands that twin the engine's accessor), it
# runs the fold of the record the fold was completed with. Each cell below serves nixpkgs' value over the same record;
# gen-merge served the restated fold's (`{ }`, `[ 1 ]`, the last definition). The intact records are the control. The
# refusals the completion's check owes are pinned on `testsError` (`../tests-error.nix`, group `fold-rewrite-check`).
#
# The keep-test and the completion are spelled inline at every site (a bound lambda costs a thunk per process), so
# `test-every-inline-copy-is-the-one-text` reads them back out of `lib/` and holds every copy to one text.
#
# RED: any site handing the record on as it is (its keep-test `true`) serves the restated fold's value at that site's
# cells; editing one copy's text reds the source cell.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  gt = gm.types;
  l = nixpkgsLib;
  lastVal = _loc: defs: (l.last defs).value;
  threadedRewrite =
    t:
    t
    // {
      mergeDefs = t.mergeDefs // {
        threaded = _: lastVal;
      };
    };
  replaced =
    t:
    t
    // {
      mergeDefs = {
        __functor = _: lastVal;
        threaded = _: lastVal;
      };
    };
  sub = gt.submodule {
    options.a = gm.mkOption {
      type = gt.int;
      default = 0;
    };
  };
  evt =
    (gm.evalModuleTree { } [
      {
        options.a = gm.mkOption {
          type = gt.int;
          default = 0;
        };
      }
    ]).type;
  read =
    type: vs:
    (gm.evalModuleTree { } (
      [ { options.x = gm.mkOption { inherit type; }; } ] ++ map (v: { x = v; }) vs
    )).config.x;
  # hub `ci/perf-bench.nix` `steppedRegistry`'s root (gen-aspects `aspectsRootWith`'s fold), restated: a consumer's
  # container folding each element through the called `genMerge.mergeDefs` with the element's threaded fold and the
  # engine's accessor
  stepRoot =
    elemType:
    let
      split =
        _loc: defs:
        map (k: {
          step = [ k ];
          loc = [ k ];
          defs = builtins.concatMap (
            d:
            if d.value ? ${k} then
              [
                {
                  inherit (d) file;
                  value = d.value.${k};
                }
              ]
            else
              [ ]
          ) defs;
          type = elemType;
        }) (builtins.attrNames (builtins.foldl' (acc: d: acc // d.value) { } defs));
      foldWith =
        foldElement: loc: defs:
        builtins.listToAttrs (
          map (e: {
            name = builtins.head e.step;
            value = foldElement e;
          }) (split loc defs)
        );
    in
    gt.defineType {
      name = "steppedRoot";
      inherit elemType split;
      carries.element = elemType;
      recarry = c: stepRoot c.element;
      substructure = {
        declares = prefix: elemType.getSubOptions (prefix ++ [ "<name>" ]);
        modules = elemType.getSubModules or null;
        rebuild = m: stepRoot (if elemType ? substSubModules then elemType.substSubModules m else elemType);
      };
      mergeDefs = {
        __functor = _: foldWith (e: gm.mergeDefs e.loc e.type e.defs);
        threaded =
          ev:
          foldWith (
            e:
            gm.mergeDefs e.loc (
              if builtins.isAttrs e.type && e.type ? mergeDefs.threaded then
                e.type // { mergeDefs = e.type.mergeDefs.threaded (ev // { position = ev.position ++ e.step; }); }
              else
                e.type
            ) e.defs
          );
      };
    };

  # the source with every run of whitespace removed, so the formatter's layout is not read
  flat = s: l.concatStrings (builtins.filter builtins.isString (builtins.split "[[:space:]]+" s));
  source = flat (
    l.concatMapStrings builtins.readFile [
      ../../lib/interface.nix
      ../../lib/modules.nix
      ../../lib/types.nix
    ]
  );
  occurrences = needle: builtins.length (l.splitString needle source) - 1;
  keep =
    x:
    flat "!(${x} ? mergeDefs) || (if ${x} ? mergeDefs.completed then ${x}.mergeDefs == ${x}.mergeDefs.completed.mergeDefs else if (${x}.__typeSelf or null) != null then (${x}.__typeSelf null) ? mergeDefs && ${x}.mergeDefs == (${x}.__typeSelf null).mergeDefs else !(${x} ? merge.completed) || ${x}.merge.completed ? mergeDefs && ${x}.mergeDefs == ${x}.merge.completed.mergeDefs)";
  completion =
    x:
    flat "if ${x} ? mergeDefs.completed then ${x} // { inherit (${x}.mergeDefs.completed) mergeDefs merge; } else if (${x}.__typeSelf or null) != null then (if (${x}.__typeSelf null) ? mergeDefs then ${x} // { inherit (${x}.__typeSelf null) mergeDefs merge; } else removeAttrs ${x} [ \"mergeDefs\" ] // { inherit (${x}.__typeSelf null) merge; }) else if ${x}.merge.completed ? mergeDefs then ${x} // { inherit (${x}.merge.completed) mergeDefs merge; } else removeAttrs ${x} [ \"mergeDefs\" ] // { inherit (${x}.merge.completed) merge; }";
  # the completion whose stamp arm also brings the stamp's check witness pair where the record kept its check
  witnessed =
    x:
    flat "if ${x} ? mergeDefs.completed then ${x} // { inherit (${x}.mergeDefs.completed) mergeDefs merge; } else if (${x}.__typeSelf or null) != null then (if (${x}.__typeSelf null) ? mergeDefs then ${x} // (if ${x} ? _checkWitness && ${x}.check == ${x}._checkWitness then { inherit (${x}.__typeSelf null) mergeDefs merge _checkWitness check; } else { inherit (${x}.__typeSelf null) mergeDefs merge; }) else removeAttrs ${x} [ \"mergeDefs\" ] // { inherit (${x}.__typeSelf null) merge; }) else if ${x}.merge.completed ? mergeDefs then ${x} // { inherit (${x}.merge.completed) mergeDefs merge; } else removeAttrs ${x} [ \"mergeDefs\" ] // { inherit (${x}.merge.completed) merge; }";
  # every site's subject, and how many copies of each text it holds
  sites = {
    "e.type" = {
      keep = 3;
      completion = 0;
      witnessed = 3;
    };
    element = {
      keep = 1;
      completion = 1;
      witnessed = 0;
    };
    freeform = {
      keep = 2;
      completion = 1;
      witnessed = 0;
    };
    freeformType = {
      keep = 0;
      completion = 0;
      witnessed = 1;
    };
    "optDecl.type" = {
      keep = 3;
      completion = 1;
      witnessed = 2;
    };
    "t.carries.element" = {
      keep = 2;
      completion = 0;
      witnessed = 0;
    };
    type = {
      keep = 1;
      completion = 0;
      witnessed = 1;
    };
  };
in
{
  flake.tests.declared-fold-completion = {
    test-a-threaded-rewritten-submodule-over-no-definitions-is-its-module-sets-value = {
      expr = read (threadedRewrite sub) [ { } ];
      expected.a = 0;
    };
    test-a-replaced-submodule-through-define-type-over-no-definitions-is-its-module-sets-value = {
      expr = read (gt.defineType (replaced sub)) [ { } ];
      expected.a = 0;
    };
    test-a-threaded-rewritten-submodule-inside-a-submodule-folds-two-definitions = {
      expr = read (gt.submodule { options.y = gm.mkOption { type = threadedRewrite sub; }; }) [
        { y.a = 1; }
        { y = { }; }
      ];
      expected.y.a = 1;
    };
    test-an-evaluations-threaded-rewritten-type-as-a-list-element-is-its-module-sets-value = {
      expr = read (gt.listOf (threadedRewrite evt)) [ [ { } ] ];
      expected = [ { a = 0; } ];
    };
    test-a-replaced-list-concatenates = {
      expr = read (replaced (gt.listOf gt.int)) [
        [ 1 ]
        [ 2 ]
      ];
      expected = [
        2
        1
      ];
    };
    test-a-replaced-list-as-an-attrs-element-concatenates = {
      expr = read (gt.attrsOf (replaced (gt.listOf gt.int))) [
        { k = [ 1 ]; }
        { k = [ 2 ]; }
      ];
      expected.k = [
        2
        1
      ];
    };
    test-gen-attrs-with-its-fold-replaced-merges = {
      expr = read (gt.attrs // { mergeDefs = lastVal; }) [
        { a = 1; }
        { b = 2; }
      ];
      expected = {
        a = 1;
        b = 2;
      };
    };
    test-a-replaced-attrs-as-a-freeform-type-merges = {
      expr = read (gt.submodule { freeformType = replaced (gt.attrsOf gt.int); }) [
        { a = 1; }
        { b = 2; }
      ];
      expected = {
        a = 1;
        b = 2;
      };
    };
    # a consumer's container reaching the engine's threaded twin with the engine's accessor (owner ruling (W))
    test-a-consumers-stepped-list-of-a-threaded-rewritten-submodule-is-its-module-sets-value = {
      expr = read (stepRoot (gt.listOf (threadedRewrite sub))) [ { g = [ { } ]; } ];
      expected.g = [ { a = 0; } ];
    };
    test-a-consumers-stepped-attrs-of-a-replaced-list-concatenates = {
      expr = read (stepRoot (gt.attrsOf (replaced (gt.listOf gt.int)))) [
        { g.k = [ 1 ]; }
        { g.k = [ 2 ]; }
      ];
      expected.g.k = [
        2
        1
      ];
    };
    test-the-intact-records-are-unmoved = {
      expr = {
        sub = read sub [ { } ];
        list = read (gt.listOf gt.int) [
          [ 1 ]
          [ 2 ]
        ];
      };
      expected = {
        sub.a = 0;
        list = [
          2
          1
        ];
      };
    };
    test-every-inline-copy-is-the-one-text = {
      expr = {
        keep = builtins.mapAttrs (x: _: occurrences (keep x)) sites;
        completion = builtins.mapAttrs (x: _: occurrences (completion x)) sites;
        witnessed = builtins.mapAttrs (x: _: occurrences (witnessed x)) sites;
        # every keep-test and every completion in `lib/` is one of the copies above
        unlisted = {
          keep = occurrences "?mergeDefs)||(if" - l.foldl' (n: s: n + s.keep) 0 (builtins.attrValues sites);
          completion =
            occurrences "mergeDefs.completed)mergeDefsmerge;}"
            - l.foldl' (n: s: n + s.completion + s.witnessed) 0 (builtins.attrValues sites);
        };
      };
      expected = {
        keep = builtins.mapAttrs (_: s: s.keep) sites;
        completion = builtins.mapAttrs (_: s: s.completion) sites;
        witnessed = builtins.mapAttrs (_: s: s.witnessed) sites;
        unlisted = {
          keep = 0;
          completion = 0;
        };
      };
    };
  };
}
