# THE ENGINE'S OWN `_module` OPTION RECORDS, AND THE TWO TYPES THEY STATE (den-hoag-a67l3, den-hoag-pm14k).
# nixpkgs' `internalModule` declares `_module.{args,check,freeformType,specialArgs}` in every
# evaluation, so a module's `options` argument, the published `options` and every submodule hold their
# records; gen-merge serves them (`lib/modules.nix` `moduleOwn`), typed as nixpkgs types them:
# `lazyAttrsOf raw`, `bool`, `nullOr optionType` and, for `specialArgs`, which states none, the fixup
# `unspecified`. An option stating no type carries `unspecified` too (`serveOptions`).
#
# Every cell runs ONE fixture through both engines. A record is read field by field, each field
# through `?` and `tryEval`, so an absent field is a failed cell and never an abort. Where gen departs,
# the cell pins BOTH sides to literals, so an upstream move reds it as surely as a gen one. The stated
# departures:
#   d2o0g      nixpkgs' `args` carries `{ extendModules, moduleType }` from `lib/modules.nix`; gen
#              passes no such argument, so that definition is read away (`noD2o0g`). Inside a
#              submodule nixpkgs also defines `name` twice from `<unknown-file>` where gen defines it
#              once from the engine's file, so there `args` is compared on its value's names alone.
#   door       `evalModuleTree { check = false; }` is gen's (nixpkgs has no door): its `check` record
#              reads the door's definition.
#   unspecified's fold (`mergeUntyped`, the untyped option's) departs from nixpkgs' constructor
#              default in three classes: a shared attrset key whose values differ is refused by name
#              where nixpkgs' `//` keeps one silently (the 2026-09-25 carve-out), two functions are
#              refused where nixpkgs' pointwise merge aborts uncatchably (the same ruling), and
#              agreeing nulls, floats and paths are served where nixpkgs refuses (the 2026-10-06
#              serve-beyond ruling: serving an agreement costs no correctness).
#   wording    a pair of types that does not merge is refused with gen's type-merge text where
#              nixpkgs says `already declared` (`ci/tests-error.nix`, `module-option-records`).
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  nl = nixpkgsLib;
  try =
    x:
    let
      r = builtins.tryEval (builtins.deepSeq x x);
    in
    if r.success then r.value else "REFUSED";

  # ── the records, scenario × view (every key in one cell) ─────────────────────────────────────────
  show =
    v:
    if builtins.isAttrs v then
      (if v ? _type && v ? name then "type:${v.name}" else builtins.attrNames v)
    else if builtins.isFunction v then
      "<fn>"
    else
      v;
  field =
    r: n: g:
    if r ? ${n} then try (g r.${n}) else "ABSENT";
  # d2o0g: nixpkgs' `{ extendModules, moduleType }` definition, read away
  isD2o0g = d: builtins.isAttrs d.value && d.value ? extendModules;
  noD2o0g =
    k: r:
    if k != "args" || !(r ? definitionsWithLocations) then
      r
    else
      let
        kept = builtins.filter (d: !(isD2o0g d)) r.definitionsWithLocations;
      in
      r
      // {
        definitionsWithLocations = kept;
        definitions = map (d: d.value) kept;
        files = map (d: d.file) kept;
        value = removeAttrs r.value [
          "extendModules"
          "moduleType"
        ];
      };
  dump =
    k: r0:
    let
      r = noD2o0g k r0;
    in
    {
      type = field r "type" (t: t.name or "noname");
      value = field r "value" show;
      isDefined = field r "isDefined" (x: x);
      highestPrio = field r "highestPrio" (x: x);
      defs = field r "definitions" (map show);
      files = field r "files" (x: x);
      declarations = field r "declarations" (x: x);
      loc = field r "loc" (x: x);
      internal = field r "internal" (x: x);
      readOnly = field r "readOnly" (x: x);
      default = field r "default" show;
      description = field r "description" builtins.isString;
      str = try "${r}";
    };
  ownKeys = [
    "args"
    "check"
    "freeformType"
    "specialArgs"
  ];
  records =
    M: scen: view:
    let
      native = M ? evalModuleTree;
      T = M.types;
      sub = m: if native then T.submodule m else T.submoduleWith { modules = [ m ]; };
      sa = if scen == "sa" || scen == "rdSA" then { shuttle = "S"; } else { };
      ev =
        mods:
        if native then
          gm.evalModuleTree (
            { specialArgs = sa; } // (if scen == "door" then { check = false; } else { })
          ) mods
        else
          nl.evalModules {
            modules = mods;
            specialArgs = sa;
          };
      extra =
        {
          checkF = [ { config._module.check = false; } ];
          ff = [ { config._module.freeformType = T.lazyAttrsOf T.raw; } ];
          rdCheck = [
            {
              options._module.check = M.mkOption {
                type = T.bool;
                example = false;
              };
            }
          ];
          rdArgs = [ { options._module.args = M.mkOption { type = T.lazyAttrsOf T.raw; }; } ];
          rdSA = [
            { options._module.specialArgs = M.mkOption { apply = s: s // { shuttle = "applied"; }; }; }
          ];
          rdFF = [ { options._module.freeformType = M.mkOption { internal = true; }; } ];
          extra = [
            {
              options._module.extra = M.mkOption {
                type = T.int;
                default = 3;
              };
            }
          ];
        }
        .${scen} or [ ];
      # every module names its file, so a file field compares engines and not anonymous-module names
      named =
        file: m:
        if builtins.isFunction m then args: { _file = file; } // m args else { _file = file; } // m;
      reader =
        { options, config, ... }:
        {
          options.o = M.mkOption {
            type = T.raw;
            default = null;
          };
          config._module.args.zz = 5;
          config.o =
            if view == "arg" then
              builtins.listToAttrs (
                map (k: {
                  name = k;
                  value = dump k options._module.${k};
                }) ownKeys
              )
            else if view == "cfg" then
              builtins.listToAttrs (
                map (k: {
                  name = k;
                  value = show (
                    if k == "args" then
                      removeAttrs config._module.args [
                        "extendModules"
                        "moduleType"
                      ]
                    else
                      config._module.${k}
                  );
                }) ownKeys
              )
            else
              null;
        };
      mods = [ (named "R" reader) ] ++ map (named "E") extra;
      subMods = [
        {
          _file = "S";
          options.s = M.mkOption {
            type = sub (
              { options, ... }:
              {
                _file = "SI";
                options.o = M.mkOption {
                  type = T.raw;
                  default = null;
                };
                config.o = builtins.listToAttrs (
                  map (k: {
                    name = k;
                    value =
                      let
                        d = dump k options._module.${k};
                      in
                      # inside a submodule nixpkgs defines `name` twice from `<unknown-file>`; gen once
                      if k == "args" then { inherit (d) value isDefined type; } else d;
                  }) ownKeys
                );
              }
            );
            default = { };
          };
        }
      ];
    in
    if view == "pub" then
      builtins.listToAttrs (
        map (k: {
          name = k;
          value = dump k (ev mods).options._module.${k};
        }) ownKeys
      )
    else if view == "sub" then
      (ev subMods).config.s.o
    else
      (ev mods).config.o;
  recordCell = scen: view: {
    expr = records gm scen view;
    expected = records nl scen view;
  };

  # ── the approved oracle: the two types, the records' types, the freeform merge ───────────────────
  cases =
    M:
    let
      native = M ? evalModuleTree;
      T = M.types;
      ev = mods: if native then gm.evalModuleTree { } mods else nl.evalModules { modules = mods; };
      sub = m: if native then T.submodule m else T.submoduleWith { modules = [ m ]; };
      plain = [
        {
          _file = "P";
          options.o = M.mkOption {
            type = T.int;
            default = 1;
          };
          options.u = M.mkOption { };
        }
      ];
      pub = (ev plain).options;
      argView =
        k:
        (ev (
          plain
          ++ [
            (
              { options, ... }:
              {
                _file = "R";
                options.r = M.mkOption {
                  type = T.raw;
                  default = null;
                };
                config.r = options._module.${k}.type.name;
              }
            )
          ]
        )).config.r;
      ffs =
        ts:
        map (t: {
          _file = "F${toString t.i}";
          config._module.freeformType = t.t;
        }) ts;
      two =
        t1: t2:
        ffs [
          {
            i = 1;
            t = t1;
          }
          {
            i = 2;
            t = t2;
          }
        ];
      d = {
        _file = "D";
        config.x = 1;
      };
      # two type definitions whose `typeMerge` answers name which one decided
      B = nl.types.attrsOf nl.types.int;
      tg = tag: B // { typeMerge = _f: B // { description = tag; }; };
      leafArgs =
        argsDecl:
        try
          (ev [
            {
              options._module = M.mkOption {
                type = sub { options.args = M.mkOption argsDecl; };
                default = { };
              };
            }
            (
              {
                q ? "absent",
                ...
              }:
              {
                options.r = M.mkOption { default = null; };
                config.r = q;
              }
            )
          ]).config.r;
      untyped = type: if type == null then M.mkOption { } else M.mkOption { inherit type; };
      folded =
        type: defs:
        try (ev ([ { options.u = untyped type; } ] ++ map (v: { config.u = v; }) defs)).config.u;
    in
    {
      # `.type.name` of the four records and of an untyped option, published and at the argument
      tnRecords = map (k: pub._module.${k}.type.name) ownKeys ++ [
        pub._module.freeformType.type.nestedTypes.elemType.name
        pub.u.type.name
      ];
      tnArgument = map argView [
        "args"
        "freeformType"
        "specialArgs"
      ];
      tnSubUntyped =
        (
          (ev [
            {
              options.s = M.mkOption {
                type = sub { options.u = M.mkOption { }; };
                default = { };
              };
            }
          ]).options.s.type.getSubOptions
            [ "s" ]
        ).u.type.name;
      tnDesc = map (k: pub._module.${k}.type.description) ownKeys ++ [ pub.u.type.description ];
      ctlTyped = pub.o.type.name;
      # two `attrsOf` freeforms merge: the config, and the record holding the merged type
      ffMergeInt = (ev (two (T.attrsOf T.int) (T.attrsOf T.int) ++ [ (d // { config.y = 2; }) ])).config;
      # the plant-sensitive one: selecting either operand loses the other's option
      ffMergeSub =
        (ev (
          two
            (T.attrsOf (sub {
              options.a = M.mkOption {
                type = T.int;
                default = 0;
              };
            }))
            (
              T.attrsOf (sub {
                options.b = M.mkOption {
                  type = T.int;
                  default = 1;
                };
              })
            )
          ++ [
            {
              _file = "D";
              config.x.a = 5;
            }
          ]
        )).config.x;
      ffMergeRecord =
        let
          r = (ev (two (T.attrsOf T.int) (T.attrsOf T.int) ++ plain)).options._module.freeformType;
        in
        {
          name = r.value.name;
          elem = r.value.nestedTypes.elemType.name;
          inherit (r) files isDefined;
        };
      ffRefuseCaught = try (ev (two (T.attrsOf T.int) (T.attrsOf T.str) ++ [ d ])).config;
      ffRefuseFunctorCaught = try (ev (two (T.attrsOf T.int) (T.listOf T.int) ++ [ d ])).config;
      ffNotAType =
        try
          (ev [
            {
              _file = "F";
              config._module.freeformType = 5;
            }
            d
          ]).config;
      # `types.optionType`: its check, its merge called as nixpkgs' `mergeDefinitions` calls it
      optTypeCheck = {
        int = T.optionType.check T.int;
        five = T.optionType.check 5;
        set = T.optionType.check { };
        foreign = T.optionType.check nl.types.int;
      };
      optTypeMerge =
        let
          m =
            T.optionType.merge
              [ "t" ]
              [
                {
                  file = "A";
                  value = T.attrsOf T.int;
                }
                {
                  file = "B";
                  value = T.attrsOf T.int;
                }
              ];
        in
        {
          inherit (m) name;
          elem = m.nestedTypes.elemType.name;
        };
      optTypeMergeOne =
        (T.optionType.merge
          [ "t" ]
          [
            {
              file = "A";
              value = T.listOf T.str;
            }
          ]
        ).name;
      # which operand decides, at each of the four surfaces that merge types
      optTypeOrient =
        try
          (T.optionType.merge
            [ "t" ]
            [
              {
                file = "A";
                value = tg "first";
              }
              {
                file = "B";
                value = tg "second";
              }
            ]
          ).description;
      optTypeOrientOpt =
        try
          (ev [
            { options.t = M.mkOption { type = T.optionType; }; }
            {
              _file = "A";
              config.t = tg "first";
            }
            {
              _file = "B";
              config.t = tg "second";
            }
          ]).config.t.description;
      optTypeOrientMount =
        try
          (nl.evalModules {
            modules = [
              { options.t = nl.mkOption { type = T.optionType; }; }
              {
                _file = "A";
                config.t = tg "first";
              }
              {
                _file = "B";
                config.t = tg "second";
              }
            ];
          }).config.t.description;
      ffOrient =
        try
          (ev [
            {
              _file = "F1";
              config._module.freeformType = tg "first";
            }
            {
              _file = "F2";
              config._module.freeformType = tg "second";
            }
            d
          ]).options._module.freeformType.value.description;
      orderFF =
        (ev (two (T.attrsOf T.int) (T.attrsOf T.int) ++ plain)).options._module.freeformType.files;
      # a definition that is not a type, refused where nixpkgs' `check` refuses it
      optTypeNotAType =
        try
          (ev [
            { options.t = M.mkOption { type = T.optionType; }; }
            { config.t = 5; }
          ]).config.t;
      optTypeNotATypeElem =
        try
          (ev [
            { options.t = M.mkOption { type = T.attrsOf T.optionType; }; }
            { config.t.k = 5; }
          ]).config.t;
      # `types.unspecified`'s fold: the shapes it shares with nixpkgs, explicit and untyped alike
      unspecStrings = folded T.unspecified [
        "s"
        "s"
      ];
      untypedStrings = folded null [
        "s"
        "s"
      ];
      unspecLists = folded T.unspecified [
        [ 1 ]
        [ 2 ]
      ];
      unspecSetsDisjoint = folded T.unspecified [
        { a = 1; }
        { b = 2; }
      ];
      unspecIntsDiffer = folded T.unspecified [
        3
        4
      ];
      # wv300's judge: a `submodule`-typed `_module` leaf re-declaring `args`
      leafArgsUntyped = leafArgs { apply = a: a // { q = 1; }; };
      leafArgsUnspec = leafArgs {
        type = T.unspecified;
        apply = a: a // { q = 1; };
      };
      # C1: a freeform key gated on an engine record's value
      ffGateCheckVal =
        (ev [
          {
            _file = "F";
            config._module.freeformType = T.attrsOf T.raw;
          }
          (
            { options, ... }:
            {
              _file = "G";
              config.foo = M.mkIf options._module.check.value 2;
            }
          )
        ]).config.foo;
      ffGateArgsVal =
        (ev [
          {
            _file = "F";
            config._module.freeformType = T.attrsOf T.raw;
          }
          (
            { options, ... }:
            {
              _file = "G";
              config.foo = M.mkIf (options._module.args.value ? zz) 2;
            }
          )
          {
            _file = "Z";
            config._module.args.zz = 1;
          }
        ]).config.foo;
      # nixpkgs' docs walker over gen's published tree, and over a gen `submodule` it mounts
      docsPub = map (o: {
        inherit (o)
          name
          internal
          visible
          type
          ;
      }) (nl.optionAttrSetToDocList pub);
      docsMounted =
        map
          (o: {
            inherit (o)
              name
              internal
              visible
              type
              ;
          })
          (
            nl.optionAttrSetToDocList
              (nl.evalModules {
                modules = [
                  {
                    options.s = nl.mkOption {
                      type = sub {
                        options.i = M.mkOption {
                          type = T.int;
                          default = 1;
                          description = "i";
                        };
                        options.u = M.mkOption { description = "u"; };
                      };
                      default = { };
                      description = "s";
                    };
                  }
                ];
              }).options
          );
      # every record forces whole, catchably, but for the one key it refuses by name
      wholeRecords = map (
        k: (builtins.tryEval (builtins.deepSeq (removeAttrs pub._module.${k} [ "valueMeta" ]) true)).success
      ) ownKeys;
      # the stated departures, each side read
      noArgs =
        let
          r = (ev [ { options.o = M.mkOption { default = null; }; } ]).options._module.args;
        in
        {
          isDefined = try r.isDefined;
          value = try (
            builtins.filter (n: n != "extendModules" && n != "moduleType") (builtins.attrNames r.value)
          );
        };
      unspecSetsDiffer = folded T.unspecified [
        { a = 1; }
        { a = 2; }
      ];
      untypedSetsDiffer = folded null [
        { a = 1; }
        { a = 2; }
      ];
      uElemDiffer =
        try
          (ev [
            { options.u = M.mkOption { type = T.attrsOf T.unspecified; }; }
            { config.u.k.a = 1; }
            { config.u.k.a = 2; }
          ]).config.u;
      uNull = folded T.unspecified [
        null
        null
      ];
      uFloat = folded T.unspecified [
        1.5
        1.5
      ];
    };
  gen = cases gm;
  np = cases nl;
  twin = k: {
    expr = gen.${k};
    expected = np.${k};
  };
  # a stated departure: both sides pinned
  stated = k: g: n: {
    expr = {
      gen = gen.${k};
      nixpkgs = np.${k};
    };
    expected = {
      gen = g;
      nixpkgs = n;
    };
  };
in
{
  flake.tests.module-option-records = {
    # ── the four records, every scenario, at the argument, the published tree and `config` ──────────
    test-plain-arg = recordCell "plain" "arg";
    test-plain-pub = recordCell "plain" "pub";
    test-plain-cfg = recordCell "plain" "cfg";
    test-plain-sub = recordCell "plain" "sub";
    test-check-false-arg = recordCell "checkF" "arg";
    test-check-false-pub = recordCell "checkF" "pub";
    test-check-false-cfg = recordCell "checkF" "cfg";
    test-freeform-arg = recordCell "ff" "arg";
    test-freeform-pub = recordCell "ff" "pub";
    test-freeform-cfg = recordCell "ff" "cfg";
    test-specialArgs-arg = recordCell "sa" "arg";
    test-specialArgs-pub = recordCell "sa" "pub";
    test-specialArgs-cfg = recordCell "sa" "cfg";
    test-redeclared-check-arg = recordCell "rdCheck" "arg";
    test-redeclared-check-pub = recordCell "rdCheck" "pub";
    test-redeclared-check-cfg = recordCell "rdCheck" "cfg";
    test-redeclared-args-arg = recordCell "rdArgs" "arg";
    test-redeclared-args-pub = recordCell "rdArgs" "pub";
    test-redeclared-args-cfg = recordCell "rdArgs" "cfg";
    test-redeclared-specialArgs-arg = recordCell "rdSA" "arg";
    test-redeclared-specialArgs-pub = recordCell "rdSA" "pub";
    test-redeclared-specialArgs-cfg = recordCell "rdSA" "cfg";
    test-redeclared-freeformType-arg = recordCell "rdFF" "arg";
    test-redeclared-freeformType-pub = recordCell "rdFF" "pub";
    test-redeclared-freeformType-cfg = recordCell "rdFF" "cfg";
    test-declared-extra-arg = recordCell "extra" "arg";
    test-declared-extra-pub = recordCell "extra" "pub";
    test-declared-extra-cfg = recordCell "extra" "cfg";
    # the door's `check = false` is gen's own: its record reads the door's definition, and the other
    # three are nixpkgs' with no door
    test-door-check-reads-the-door = {
      expr =
        let
          r = (records gm "door" "pub").check;
        in
        {
          inherit (r) value files highestPrio;
          cfg = (records gm "door" "cfg").check;
        };
      expected = {
        value = false;
        files = [ "<gen-merge: evalModuleTree { check }>" ];
        highestPrio = 1000;
        cfg = false;
      };
    };
    test-door-other-keys-are-nixpkgs = {
      expr = removeAttrs (records gm "door" "pub") [ "check" ];
      expected = removeAttrs (records nl "plain" "pub") [ "check" ];
    };

    # ── the types the records state, and an untyped option's ────────────────────────────────────────
    test-records-and-an-untyped-option-state-nixpkgs-type-names = twin "tnRecords";
    test-records-at-the-argument-state-nixpkgs-type-names = twin "tnArgument";
    test-an-untyped-option-in-a-submodule-states-unspecified = twin "tnSubUntyped";
    test-the-type-descriptions-are-nixpkgs = twin "tnDesc";
    test-typed-option-control = twin "ctlTyped";
    test-every-record-forces-whole-but-valueMeta = {
      expr = gen.wholeRecords;
      expected = [
        true
        true
        true
        true
      ];
    };

    # ── two freeform definitions merge, and the record holds the merged type ────────────────────────
    test-two-attrsOf-int-freeforms-merge = twin "ffMergeInt";
    test-two-attrsOf-submodule-freeforms-merge-both-options = twin "ffMergeSub";
    test-the-freeform-record-holds-the-merged-type = twin "ffMergeRecord";
    test-the-freeform-record-lists-definitions-last-module-first = twin "orderFF";
    test-an-unmergeable-freeform-pair-is-refused-catchably = twin "ffRefuseCaught";
    test-an-unmergeable-freeform-functor-pair-is-refused-catchably = twin "ffRefuseFunctorCaught";
    test-a-freeform-that-is-not-a-type-is-refused = twin "ffNotAType";

    # ── `types.optionType` ─────────────────────────────────────────────────────────────────────────
    test-optionType-check = twin "optTypeCheck";
    test-optionType-merges-two-types = twin "optTypeMerge";
    test-optionType-one-definition-is-its-value = twin "optTypeMergeOne";
    test-optionType-merge-called-directly-decides-as-nixpkgs = twin "optTypeOrient";
    test-optionType-at-an-option-decides-as-nixpkgs = twin "optTypeOrientOpt";
    test-optionType-mounted-in-nixpkgs-decides-as-nixpkgs = twin "optTypeOrientMount";
    test-the-freeform-type-decides-as-nixpkgs = twin "ffOrient";
    test-optionType-refuses-a-definition-that-is-not-a-type = twin "optTypeNotAType";
    test-optionType-element-refuses-a-definition-that-is-not-a-type = twin "optTypeNotATypeElem";

    # ── `types.unspecified` ────────────────────────────────────────────────────────────────────────
    test-unspecified-concatenates-equal-strings = twin "unspecStrings";
    test-untyped-concatenates-equal-strings = twin "untypedStrings";
    test-unspecified-concatenates-lists = twin "unspecLists";
    test-unspecified-unions-disjoint-sets = twin "unspecSetsDisjoint";
    test-unspecified-refuses-differing-ints = twin "unspecIntsDiffer";
    # the three stated classes
    test-unspecified-refuses-a-shared-key-whose-values-differ = stated "unspecSetsDiffer" "REFUSED" {
      a = 1;
    };
    test-untyped-refuses-a-shared-key-whose-values-differ = stated "untypedSetsDiffer" "REFUSED" {
      a = 1;
    };
    test-unspecified-element-refuses-a-shared-key-whose-values-differ = stated "uElemDiffer" "REFUSED" {
      k.a = 1;
    };
    test-unspecified-serves-agreeing-nulls = stated "uNull" null "REFUSED";
    test-unspecified-serves-agreeing-floats = stated "uFloat" 1.5 "REFUSED";
    # nixpkgs applies two functions pointwise and aborts uncatchably on this input, so its side is
    # not read here
    test-unspecified-refuses-two-functions = {
      expr = try (
        (gm.evalModuleTree { } [
          { options.u = gm.mkOption { type = gm.types.unspecified; }; }
          { config.u = x: [ x ]; }
          { config.u = x: [ (x + 1) ]; }
        ]).config.u
          1
      );
      expected = "REFUSED";
    };

    # ── wv300's judge reads declarations: an explicit `unspecified` is refused, an untyped one served ─
    test-a-leaf-redeclaring-args-untyped-is-served = twin "leafArgsUntyped";
    test-a-leaf-redeclaring-args-unspecified-is-refused = twin "leafArgsUnspec";

    # ── a freeform key gated on an engine record's value reads the record's own binding ─────────────
    test-freeform-gated-on-the-check-record = twin "ffGateCheckVal";
    test-freeform-gated-on-the-args-record = twin "ffGateArgsVal";
    # no module defines `_module.args`: nixpkgs' own d2o0g definition makes it defined there
    test-args-with-no-definition =
      stated "noArgs"
        {
          isDefined = false;
          value = [ ];
        }
        {
          isDefined = true;
          value = [ ];
        };

    # ── nixpkgs' docs walker ───────────────────────────────────────────────────────────────────────
    test-the-docs-walker-over-the-published-tree-is-nixpkgs = twin "docsPub";
    test-the-docs-walker-over-a-mounted-submodule-is-nixpkgs = twin "docsMounted";
  };
}
