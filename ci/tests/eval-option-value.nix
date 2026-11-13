# nixpkgs' `lib.modules.evalOptionValue loc opt defs`, on this engine (den-hoag-ien5k T3, spec
# `specs/2026-11-01-ien5k-t3-syntactic-membership-spec.md` §2.1, §3a GM1, GM2, GM4): the evaluated option record
# over a caller's definitions, by the engine's own option fold.
#   GM1 · the lone case: one property-free definition outranks the declared default; a lone override that does not
#         outrank it, and a `readOnly` option, keep the default in the fold.
#   GM2 · the record equals the same option evaluated by `evalModuleTree` (`value`, `isDefined`, `highestPrio`,
#         `definitions`) and nixpkgs' `evalOptionValue` on the twin (those and `files`), shape by shape.
#   GM4 · the single-survivor statement: where every priority is visible and one definition survives, the value
#         is that survivor's, in every order of `defs`, and `files` holds the one survivor.
# A refusal reads as "REFUSED" on both engines (the readOnly and refusal texts are gen's own, pinned in
# `ci/tests-error.nix` `eval-option-value`).
# Red at gen-merge main 99ddac8: `evalOptionValue` is absent, so every cell aborts on the missing attribute.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  nl = nixpkgsLib;
  inherit (builtins)
    concatMap
    deepSeq
    genList
    length
    listToAttrs
    mapAttrs
    tryEval
    ;
  safe =
    v:
    let
      r = tryEval (deepSeq v v);
    in
    if r.success then r.value else "REFUSED";
  isGen = M: M ? evalModuleTree;
  rev = l: genList (i: builtins.elemAt l (length l - 1 - i)) (length l);
  eov = M: if isGen M then M.evalOptionValue else M.modules.evalOptionValue;
  # the record's keys a comparison reads; `files` only against nixpkgs (module files differ from `defs`' files)
  readRec =
    withFiles: r:
    {
      value = safe r.value;
      isDefined = safe r.isDefined;
      highestPrio = safe r.highestPrio;
      definitions = safe r.definitions;
    }
    // (if withFiles then { files = safe r.files; } else { });
  defsOf = map (v: {
    file = "f";
    value = v;
  });
  # `opt` is the declaration's attributes, `defs` the definition values; both built per engine
  direct =
    M: s:
    let
      o = M.mkOption s.opt // {
        declarations = [ "decl" ];
      };
    in
    readRec true (eov M [ "x" ] o (defsOf s.defs));
  viaTree =
    s:
    readRec false (
      # the module list is collected in reverse, so `defs` enter it reversed to reach the fold in `defs`' order
      (gm.evalModuleTree { } ([ { options.x = gm.mkOption s.opt; } ] ++ map (v: { x = v; }) (rev s.defs)))
      .options.x
    );

  # as `direct`, each definition in its own file, so `files` shows the survivors' order
  directIx =
    M: s:
    readRec true (
      eov M [ "x" ] (M.mkOption s.opt // { declarations = [ "decl" ]; }) (
        genList (i: {
          file = "d${toString i}";
          value = builtins.elemAt s.defs i;
        }) (length s.defs)
      )
    );
  # every ordering of a list
  perms =
    l:
    if l == [ ] then
      [ [ ] ]
    else
      concatMap (
        i:
        map (p: [ (builtins.elemAt l i) ] ++ p) (
          perms (genList (j: builtins.elemAt l (if j < i then j else j + 1)) (length l - 1))
        )
      ) (genList (i: i) (length l));
  # every ordered selection of `k` of `l`'s elements
  choose =
    k: l:
    if k == 0 then
      [ [ ] ]
    else if l == [ ] then
      [ ]
    else
      map (c: [ (builtins.head l) ] ++ c) (choose (k - 1) (builtins.tail l))
      ++ choose k (builtins.tail l);
  ordered = k: l: concatMap perms (choose k l);
  named =
    tag: xs:
    listToAttrs (
      genList (i: {
        name = "${tag}-${toString i}";
        value = builtins.elemAt xs i;
      }) (length xs)
    );

  # GM2's shapes, per engine `M`
  shapes =
    M:
    let
      T = M.types;
      ls = T.listOf T.str;
      lsd = {
        type = ls;
        default = [ "d" ];
      };
      four = [
        [ "a" ]
        (M.mkDefault [ "b" ])
        (M.mkForce [ "c" ])
        [ "e" ]
      ];
    in
    {
      one-plain = {
        opt = lsd;
        defs = [ [ "x" ] ];
      };
      one-force = {
        opt = lsd;
        defs = [ (M.mkForce [ "x" ]) ];
      };
      one-default = {
        opt = lsd;
        defs = [ (M.mkDefault [ "x" ]) ];
      };
      one-merge = {
        opt = lsd;
        defs = [
          (M.mkMerge [
            [ "x" ]
            [ "y" ]
          ])
        ];
      };
      one-before = {
        opt = lsd;
        defs = [ (M.mkBefore [ "x" ]) ];
      };
      default-only = {
        opt = lsd;
        defs = [ ];
      };
      neither = {
        opt.type = ls;
        defs = [ ];
      };
      apply = {
        opt = lsd // {
          apply = v: v ++ [ "applied" ];
        };
        defs = [ [ "x" ] ];
      };
      enum-outside = {
        opt.type = T.enum [
          "a"
          "b"
        ];
        defs = [ "c" ];
      };
      door-built = {
        opt = lsd // {
          type = M.mkOptionType {
            name = "strs";
            inherit (ls) check merge;
          };
        };
        defs = [
          [ "x" ]
          [ "y" ]
        ];
      };
      raw-form = {
        opt = lsd;
        defs = [
          [ "x" ]
          [ "y" ]
        ];
      };
    }
    //
      mapAttrs
        (_: defs: {
          opt = lsd;
          inherit defs;
        })
        (named "two" (ordered 2 four) // named "three" (ordered 3 four) // named "four" (ordered 4 four));

  # the declaration met from two declarations: the served record of an evaluation declaring it twice. A leaf
  # chain: a nested type an evaluation serves is a child of that evaluation, and its fold is refused by name
  # outside it (`threadedIn`), where nixpkgs' evaluates it again.
  twoDecls =
    M:
    let
      T = M.types;
      mods = [
        {
          options.x = M.mkOption {
            type = T.listOf T.str;
            default = [ "d" ];
          };
        }
        { options.x = M.mkOption { type = T.listOf T.str; }; }
      ];
      opt = (if isGen M then M.evalModuleTree { } mods else M.evalModules { modules = mods; }).options.x;
    in
    eov M [ "x" ] opt (defsOf [
      [ "x" ]
      [ "y" ]
    ]);

  # GM1 and GM4, per engine: declared default `[ "d" ]`
  survivor =
    M: defs:
    let
      r = eov M [ "x" ] (
        M.mkOption {
          type = M.types.listOf M.types.str;
          default = [ "d" ];
        }
        // {
          declarations = [ "decl" ];
        }
      ) (defsOf defs);
    in
    {
      value = safe r.value;
      survivors = safe (length r.files);
    };
  gm4 =
    M:
    let
      k = [ "k" ];
      n = [ "n" ];
      every = tag: defs: named tag (perms defs);
    in
    mapAttrs (_: survivor M) (
      every "default-plain" [
        (M.mkDefault k)
        n
      ]
      // every "force-plain" [
        (M.mkForce k)
        n
      ]
      // every "default-force" [
        (M.mkDefault k)
        (M.mkForce n)
      ]
      // every "default-default" [
        (M.mkDefault k)
        (M.mkDefault n)
      ]
    );
  # ADR-0039 parity-defect rule (1): a definition the priority pass discards is never read, so a throw under a
  # losing `mkDefault` serves the winner as nixpkgs does, in either order and beside a property; `forceOfIfFalse`, a
  # survivor whose content is a property, is still refused by type as nixpkgs refuses it
  losers =
    M:
    let
      F = M.mkForce [ "forced" ];
      X = M.mkDefault (throw "a losing definition's content was read");
    in
    mapAttrs
      (_: defs: {
        opt = {
          type = M.types.listOf M.types.str;
          default = [ ];
        };
        inherit defs;
      })
      {
        b2 = [
          F
          X
        ];
        b2r = [
          X
          F
        ];
        ordLast = [
          F
          X
          (M.mkBefore [ "b" ])
        ];
        ifLast = [
          F
          X
          (M.mkIf false (throw "an mkIf false content was read"))
        ];
        forceOfIfFalse = [
          (M.mkForce (M.mkIf false [ "z" ]))
          [ "p" ]
        ];
      };
  # several survivors whose content is a property: the record (`files` included) is nixpkgs', which sorts an `mkOrder`
  # content and keeps an override or `mkIf` content as the definition
  survivorContent =
    M:
    mapAttrs
      (_: defs: {
        opt = {
          type = M.types.listOf M.types.str;
          default = [ ];
        };
        inherit defs;
      })
      {
        two-order = [
          (M.mkForce [ "a" ])
          (M.mkForce (M.mkBefore [ "b" ]))
        ];
        two-nested = [
          (M.mkForce (M.mkDefault [ "a" ]))
          (M.mkForce [ "b" ])
        ];
        two-if-false = [
          (M.mkForce [ "a" ])
          (M.mkForce (M.mkIf false [ "b" ]))
        ];
      };
  readOnlyLone =
    M:
    safe
      (eov M [ "x" ] (
        M.mkOption {
          type = M.types.listOf M.types.str;
          default = [ "d" ];
          readOnly = true;
        }
        // {
          declarations = [ "decl" ];
        }
      ) (defsOf [ [ "x" ] ])).value;
in
{
  flake.tests.eval-option-value = {
    # GM1: the lone case keeps both guards (a property, `readOnly`); the plain lone definition is the control
    test-gm1-the-lone-case-keeps-its-guards = {
      expr = {
        lone-override-not-outranking = (survivor gm [ (gm.mkOverride 1600 [ "x" ]) ]).value;
        lone-plain = (survivor gm [ [ "x" ] ]).value;
        read-only = readOnlyLone gm;
      };
      expected = {
        lone-override-not-outranking = [ "d" ];
        lone-plain = [ "x" ];
        read-only = "REFUSED";
      };
    };
    test-gm1-equals-nixpkgs = {
      expr = [
        (survivor gm [ (gm.mkOverride 1600 [ "x" ]) ])
        (survivor gm [ [ "x" ] ])
        (readOnlyLone gm)
      ];
      expected = [
        (survivor nl [ (nl.mkOverride 1600 [ "x" ]) ])
        (survivor nl [ [ "x" ] ])
        (readOnlyLone nl)
      ];
    };
    # GM2: against the same option evaluated by this engine's module evaluation
    test-gm2-equals-the-served-option = {
      expr = mapAttrs (_: s: removeAttrs (direct gm s) [ "files" ]) (shapes gm);
      expected = mapAttrs (_: viaTree) (shapes gm);
    };
    # GM2: against nixpkgs' `evalOptionValue` on the twin, `files` (the survivor list) included
    test-gm2-equals-nixpkgs = {
      expr = mapAttrs (_: direct gm) (shapes gm);
      expected = mapAttrs (_: direct nl) (shapes nl);
    };
    test-gm2-two-declarations-equal-nixpkgs = {
      expr = readRec true (twoDecls gm);
      expected = readRec true (twoDecls nl);
    };
    # the population the two GM2 cells quantify over, so a generator that went empty reds here
    test-gm2-shape-count = {
      expr = length (builtins.attrNames (shapes gm));
      expected = 11 + 12 + 24 + 24;
    };
    # GM4: the widened statement, every order; the survivor count is asserted beside the value
    test-gm4-one-survivor-is-the-merge = {
      expr = gm4 gm;
      expected =
        let
          one = v: {
            value = v;
            survivors = 1;
          };
        in
        named "default-plain" [
          (one [ "n" ])
          (one [ "n" ])
        ]
        // named "force-plain" [
          (one [ "k" ])
          (one [ "k" ])
        ]
        // named "default-force" [
          (one [ "n" ])
          (one [ "n" ])
        ]
        // named "default-default" [
          {
            value = [
              "k"
              "n"
            ];
            survivors = 2;
          }
          {
            value = [
              "n"
              "k"
            ];
            survivors = 2;
          }
        ];
    };
    # the priority a bare definition takes, published as nixpkgs publishes it (`lib.modules.defaultOverridePriority`):
    # gen-schema's registry-level membership test reads it, so it restates no priority law. A literal on the
    # surface: it equals nixpkgs' and the priority the engine's own fold gives a bare definition (the lone case's
    # `highestPrio`)
    test-default-override-priority-is-nixpkgs = {
      expr = {
        published = gm.defaultOverridePriority;
        engine =
          (gm.evalOptionValue [ "x" ] (gm.mkOption { type = gm.types.listOf gm.types.str; }) [
            {
              file = "f";
              value = [ "a" ];
            }
          ]).highestPrio;
      };
      expected = {
        published = nl.modules.defaultOverridePriority;
        engine = nl.modules.defaultOverridePriority;
      };
    };
    test-gm4-equals-nixpkgs = {
      expr = gm4 gm;
      expected = gm4 nl;
    };
    test-a-losing-content-is-never-read = {
      expr = mapAttrs (_: s: (direct gm s).value) (losers gm);
      expected = {
        b2 = [ "forced" ];
        b2r = [ "forced" ];
        ordLast = [ "forced" ];
        ifLast = [ "forced" ];
        forceOfIfFalse = "REFUSED";
      };
    };
    test-a-losing-content-is-never-read-equals-nixpkgs = {
      expr = mapAttrs (_: directIx gm) (losers gm // survivorContent gm);
      expected = mapAttrs (_: directIx nl) (losers nl // survivorContent nl);
    };
  };
}
