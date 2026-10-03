# CYCLIC TYPES (den-hoag-iaram): every structural reader of a type that holds a cycle answers or
# refuses by name. Every cycle here is CONTRACTIVE (each back-edge sits under a constructor that
# consumes the value), so its value observations serve; two observations of the TYPE walked it
# without consuming anything and never returned:
#   - the SPINE, a container's `getSubModules`/`getSubOptions`, which forward to its element; on a
#     cycle through containers alone (`r = nullOr (listOf r)`) they abort uncatchably, in nixpkgs as
#     here (`lib/interface.nix` `spineModules`, `spineDeclares`);
#   - the RELATION, a redeclaration's type merge, which descends one carried role per call; on ANY
#     cyclic type declared twice it overflows the stack, nixpkgs' twin likewise (`lib/interface.nix`
#     `typeMergeRelWithin`, the pre-flight every entry to a gen relation takes).
# Both now take `importedTypeWalkFuel` and refuse by name at exhaustion. Which refusal fired is a
# claim about the message and lives in `../tests-error.nix` (`cyclic-types`); this file holds the
# booleans, the values the engine now serves, the price at its boundary, and the live controls.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  np = nixpkgsLib.types;
  caught = v: !(builtins.tryEval (builtins.deepSeq v v)).success;
  # a cycle through containers alone, and a cycle closed through a union (the json shape)
  spine = t.nullOr (t.listOf spine);
  json = t.nullOr (
    t.oneOf [
      t.int
      (t.attrsOf json)
      (t.listOf json)
    ]
  );
  # the same spine with a stock nixpkgs container on each lap, and with each stock nixpkgs record
  # that forwards both reads to one element (`coercedTo`'s `finalType`, `uniq`, `functionTo`)
  mixed = t.nullOr (np.listOf mixed);
  mixedCoerced = t.nullOr (np.coercedTo np.str (_: null) mixedCoerced);
  mixedUniq = t.nullOr (np.uniq mixedUniq);
  mixedFunctionTo = t.nullOr (np.functionTo mixedFunctionTo);
  nest =
    n: c: x:
    if n == 0 then x else c (nest (n - 1) c x);
  sub = t.submodule {
    options.y = gm.mkOption {
      type = t.int;
      default = 0;
    };
  };
  npsub = np.submodule {
    options.y = nixpkgsLib.mkOption {
      type = np.int;
      default = 0;
    };
  };
  # a stock nixpkgs container whose sub-protocol was overridden after construction
  overridden = np.listOf npsub // {
    getSubOptions = _: { overridden = 1; };
    getSubModules = [ ];
  };
  # the declared leaf's location, past the `_module` options nixpkgs' submodule declares beside it
  locs =
    o:
    builtins.filter (l: nixpkgsLib.last l == "y") (
      map (x: x.loc) (nixpkgsLib.collect (x: x ? _type && x._type == "option") o)
    );
  npEval =
    ty: defs:
    (nixpkgsLib.evalModules {
      modules = [
        { options.s = nixpkgsLib.mkOption { type = ty; }; }
      ]
      ++ map (d: { config.s = d; }) defs;
    }).config.s;
  npDocs =
    ty:
    map (o: o.type) (
      builtins.filter (o: o.visible && !o.internal) (
        nixpkgsLib.optionAttrSetToDocList
          (nixpkgsLib.evalModules { modules = [ { options.s = nixpkgsLib.mkOption { type = ty; }; } ]; })
          .options
      )
    );
  genEval =
    ty: defs:
    (gm.evalModuleTree {
      modules = [ { options.s = gm.mkOption { type = ty; }; } ] ++ map (d: { s = d; }) defs;
    }).config.s;
  declaredTwice =
    ty:
    (gm.evalModuleTree {
      modules = [
        { options.x = gm.mkOption { type = ty; }; }
        { options.x = gm.mkOption { type = ty; }; }
      ];
    }).options.x.type.name;
in
{
  flake.tests.cyclic-types = {
    # The spine's two reads and every nixpkgs reader that takes them refuse catchably: nixpkgs'
    # `fixupOptionType` reads `getSubModules` on every option, and its docs read `getSubOptions`.
    test-a-cycle-through-containers-alone-refuses-its-spine-catchably = {
      expr = {
        getSubModules = caught spine.getSubModules;
        getSubOptions = caught (spine.getSubOptions [ ]);
        npAccept = caught (npEval spine [ [ null ] ]);
        npDocs = caught (npDocs spine);
        mixedGetSubModules = caught mixed.getSubModules;
      };
      expected = {
        getSubModules = true;
        getSubOptions = true;
        npAccept = true;
        npDocs = true;
        mixedGetSubModules = true;
      };
    };
    # A lap through a stock nixpkgs record that forwards both reads to one element is a step of the
    # same walk, so the cycle is bounded however often it crosses the import boundary.
    test-a-cycle-through-a-stock-forwarding-record-refuses-its-spine-catchably = {
      expr =
        map
          (r: {
            getSubModules = caught r.getSubModules;
            getSubOptions = caught (r.getSubOptions [ ]);
            npAccept = caught (npEval r [ null ]);
          })
          [
            mixedCoerced
            mixedUniq
            mixedFunctionTo
          ];
      expected = builtins.genList (_: {
        getSubModules = true;
        getSubOptions = true;
        npAccept = true;
      }) 3;
    };
    # Gen's own evaluation SERVES the same type: its fold never reads the spine, and the union-mark
    # walk that did (`mayFoldUnion`) is bounded, answering `true` at exhaustion.
    test-gen-serves-a-cycle-through-containers-alone = {
      expr = {
        accept = genEval spine [
          [
            null
            [ null ]
          ]
        ];
        refusal = caught (genEval spine [ "s" ]);
      };
      expected = {
        accept = [
          null
          [ null ]
        ];
        refusal = true;
      };
    };
    # THE PRICE AT ITS BOUNDARY: 33 nested containers over a submodule still answer the spine; 34
    # refuse (33 forwarding steps below the container asked exceed the fuel of 32). A redeclaration
    # takes the boundary's own walk: 31 nested containers merge, 32 refuse. THE ESCAPE HATCH: a
    # container whose `substructure` states no `forward` answers for itself, so 40 containers with
    # such a record at the 20th answer, each walk 20 steps long.
    test-the-fuel-prices-a-deep-finite-chain-at-its-boundary = {
      expr = {
        spine33 = builtins.length (nest 33 t.listOf sub).getSubModules;
        spine34 = caught (nest 34 t.listOf sub).getSubModules;
        redeclare31 = declaredTwice (nest 31 t.listOf t.int);
        redeclare32 = caught (declaredTwice (nest 32 t.listOf t.int));
        hatch40 =
          let
            inner = nest 20 t.listOf sub;
          in
          builtins.length
            (nest 20 t.listOf (
              inner // { substructure = builtins.removeAttrs inner.substructure [ "forward" ]; }
            )).getSubModules;
      };
      expected = {
        spine33 = 1;
        spine34 = true;
        redeclare31 = "listOf";
        redeclare32 = true;
        hatch40 = 1;
      };
    };
    # A cyclic type declared twice is refused catchably, through both engines; the relation's
    # foreign entries answer "not mergeable" (`binOp`'s `null`) rather than descend.
    test-a-cyclic-type-declared-twice-refuses-catchably = {
      expr = {
        gen = caught (declaredTwice json);
        np =
          caught
            (nixpkgsLib.evalModules {
              modules = [
                { options.s = nixpkgsLib.mkOption { type = json; }; }
                { options.s = nixpkgsLib.mkOption { type = json; }; }
              ];
            }).options.s.type.name;
        binOp = (t.listOf json).functor.binOp { elemType = json; } { elemType = json; };
      };
      expected = {
        gen = true;
        np = true;
        binOp = null;
      };
    };
    # The pre-flight STOPS at a nesting type: its relation unions module SETS and descends into no
    # type, so its carried modules are neither walked nor forced. Walked, a module that throws when
    # forced refuses a redeclaration served before, and a submodule 31 containers down exhausts the
    # fuel on its module list.
    test-the-pre-flight-stops-at-a-nesting-type = {
      expr = {
        poisoned = declaredTwice (
          t.submodule [
            {
              options.y = gm.mkOption {
                type = t.int;
                default = 0;
              };
            }
            (throw "a module the pre-flight must not force")
          ]
        );
        deepSub31 = declaredTwice (nest 31 t.listOf sub);
      };
      expected = {
        poisoned = "submodule";
        deepSub31 = "listOf";
      };
    };
    # A STOCK CONTAINER IS STEPPED ONLY AS STOCK. One whose `getSubOptions`/`getSubModules` were
    # overridden after construction answers with its own override, as at base and as nixpkgs' own
    # `listOf` over it answers (`[ "overridden" ]`, `0`); stepped, it would answer its element's
    # (`[ "_module" "y" ]`, `1`), silently.
    test-an-overridden-stock-container-answers-its-own-sub-protocol = {
      expr = {
        genOptions = builtins.attrNames ((t.listOf overridden).getSubOptions [ ]);
        genModules = builtins.length (t.listOf overridden).getSubModules;
        npOptions = builtins.attrNames ((np.listOf overridden).getSubOptions [ ]);
        npModules = builtins.length (np.listOf overridden).getSubModules;
      };
      expected = {
        genOptions = [ "overridden" ];
        genModules = 0;
        npOptions = [ "overridden" ];
        npModules = 0;
      };
    };
    # LIVE CONTROL, same run: a finite chain through stock records answers as the records themselves
    # do, under the segment each adds (`*`, `<name>`, `<function body>`, none for `uniq`); a record
    # re-homing declines (a non-default placeholder) answers for itself.
    test-control-a-finite-chain-through-stock-records-answers-as-they-do = {
      expr = {
        stepped = locs ((t.listOf (np.attrsOf (np.functionTo (np.uniq npsub)))).getSubOptions [ "p" ]);
        modules = builtins.length (t.nullOr (np.lazyAttrsOf npsub)).getSubModules;
        declined = locs (
          (t.listOf (
            np.attrsWith {
              elemType = npsub;
              placeholder = "host";
            }
          )).getSubOptions
            [ "p" ]
        );
      };
      expected = {
        stepped = [
          [
            "p"
            "*"
            "<name>"
            "<function body>"
            "y"
          ]
        ];
        modules = 1;
        declined = [
          [
            "p"
            "*"
            "<host>"
            "y"
          ]
        ];
      };
    };
    # LIVE CONTROL, same run: a cycle closed through a union answers its spine (a union states no
    # module set and declares nothing), nixpkgs' evaluation and docs serve it, and a finite type
    # declared twice merges.
    test-control-a-union-closed-cycle-answers-its-spine = {
      expr = {
        getSubModules = json.getSubModules;
        getSubOptions = json.getSubOptions [ ];
        npAccept = npEval json [ { a = [ 1 ]; } ];
        npDocs = npDocs json != [ ];
        redeclareFinite = declaredTwice (t.nullOr (t.listOf t.int));
      };
      expected = {
        getSubModules = null;
        getSubOptions = { };
        npAccept = {
          a = [ 1 ];
        };
        npDocs = true;
        redeclareFinite = "nullOr";
      };
    };
  };
}
