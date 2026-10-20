# THE `_module.args` RECORD LISTS NIXPKGS' DEFINITIONS, IN NIXPKGS' ORDER (den-hoag-zgpaa).
# nixpkgs states three definitions of `_module.args` in modules of its own: `internalModule`'s
# `{ extendModules; moduleType; }` (`lib/modules.nix`) in every evaluation, and in a nested one
# `submoduleWith`'s position `{ name = last loc; }` and placeholder `{ name = mkOptionDefault "‹name›"; }`,
# both `<unknown-file>`. gen-merge lists them where nixpkgs' collection puts them (`moduleOwn.definitions`).
#
# Every cell reads the record inside the evaluation (a module's own `options` argument), on three engines:
# nixpkgs' `evalModules` over nixpkgs' types (the reference), gen-merge's `evalModuleTree` over gen's types,
# and nixpkgs' `evalModules` over gen's nesting types (the export bridge). The whole record is compared:
# `files`, each definition's file, keys and values, `highestPrio`, `isDefined`, the value's keys and the
# `name` the module sees. A value is shown as `<fn>` only when it is a function, so an internal entry
# holding a module's `extendModules` in place of the engine's own reds (zgpaa gate F1/F2), and as
# `type:<name>` when it is a type, the internal entry's `moduleType` (den-hoag-d2o0g).
#
# Stated departure, both sides pinned:
#   b44rx  `_module.args = mkForce { q = 1; }`: nixpkgs serves `{ q }` and a reader of `name` finds none;
#          gen keeps serving `name`, `extendModules` and `moduleType` (den-hoag-b44rx). The definitions
#          already agree.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  np = nixpkgsLib;
  show =
    v:
    if builtins.isFunction v then
      "<fn>"
    else if builtins.isAttrs v && v._type or null == "option-type" then
      "type:${v.name}"
    else
      v;
  probe = config: o: {
    files = o.files;
    defs = map (d: {
      inherit (d) file;
      value = builtins.mapAttrs (_: show) d.value;
    }) o.definitionsWithLocations;
    prio = o.highestPrio;
    isDef = o.isDefined;
    vkeys = builtins.attrNames o.value;
    cname = config._module.args.name or "<none>";
  };
  # a partial fold's value is its content (`partialSubmodule` has no nixpkgs twin)
  unwrap = v: if builtins.isAttrs v && v._type or null == "override" then v.content else v;

  # eng: "np" nixpkgs over nixpkgs' types, "gm" gen over gen's, "mix" nixpkgs over gen's nesting types
  engine =
    eng:
    let
      L = if eng == "gm" then gm else np;
      N = if eng == "np" then np.types else gm.types;
    in
    {
      inherit L N;
      T = L.types;
      mkOption = L.mkOption;
      ev = mods: if eng == "gm" then gm.evalModuleTree { } mods else np.evalModules { modules = mods; };
      tree =
        mods:
        if eng == "np" then
          (np.evalModules { modules = mods; }).type
        else
          (gm.evalModuleTree { } mods).type;
      withArgs =
        m: a:
        if eng == "np" then
          np.types.submoduleWith {
            modules = [ m ];
            specialArgs = a;
            shorthandOnlyDefinesConfig = true;
          }
        else
          (gm.types.submodule m).withArgs a;
    };

  # ── the record per nesting shape ───────────────────────────────────────────────────────────────
  shapes =
    eng:
    let
      inherit (engine eng)
        L
        N
        mkOption
        ev
        tree
        withArgs
        ;
      innerNa =
        { options, config, ... }:
        {
          options.f = mkOption { default = probe config options._module.args; };
        };
      innerQ = {
        _file = "q.nix";
        imports = [ innerNa ];
        _module.args.q = 1;
      };
      innerForce = {
        _file = "force.nix";
        imports = [ innerNa ];
        _module.args.name = L.mkForce "forced";
      };
      innerDflt = {
        _file = "dflt.nix";
        imports = [ innerNameArg ];
        _module.args.name = L.mkDefault "dflt";
      };
      innerMf = {
        _file = "mf.nix";
        imports = [ innerNa ];
        _module.args = L.mkForce { q = 1; };
      };
      innerNameArg =
        { name, ... }:
        {
          imports = [ innerNa ];
          options.n = mkOption { default = name; };
        };
      mid.options.d = mkOption {
        type = N.submodule innerNa;
        default = { };
      };
      opt =
        type:
        mkOption {
          inherit type;
          default = { };
        };
      decl = {
        _file = "decl.nix";
        options = {
          s = opt (N.submodule innerNa);
          at = opt (N.attrsOf (N.submodule innerNa));
          lz = opt (N.lazyAttrsOf (N.submodule innerNa));
          ls = mkOption {
            type = N.listOf (N.submodule innerNa);
            default = [ ];
          };
          no = mkOption {
            type = N.nullOr (N.submodule innerNa);
            default = null;
          };
          ei = opt (N.either N.int (N.submodule innerNa));
          aa = opt (N.attrsOf (N.attrsOf (N.submodule innerNa)));
          d2 = opt (N.submodule mid);
          tr = opt (tree [ innerNa ]);
          wa = opt (withArgs innerNa { a = 1; });
          pa = opt (if eng == "np" then N.submodule innerNa else gm.partialSubmodule innerNa);
          q = opt (N.submodule innerQ);
          fo = opt (N.submodule innerForce);
          na = opt (N.submodule innerNameArg);
          md = opt (N.submodule innerDflt);
          mf = opt (N.submodule innerMf);
          wn = opt (withArgs innerNameArg { name = "caller"; });
          de = mkOption { type = N.submodule innerNa; };
          # a gen nesting type below a nixpkgs container
          mx = opt (np.types.attrsOf (N.submodule innerNa));
        };
      };
      def = {
        _file = "def.nix";
        config = {
          at.k = { };
          lz.k = { };
          ls = [ { } ];
          no = { };
          ei = { };
          aa.k.j = { };
          fr = { };
          de = { };
          mx.k = { };
        };
      };
      freeformM = {
        _file = "ff.nix";
        freeformType = N.attrsOf (N.submodule innerNa);
      };
      top =
        { options, config, ... }:
        {
          _file = "top.nix";
          options.topf = mkOption { default = probe config options._module.args; };
        };
      r = ev [
        decl
        def
        freeformM
        top
      ];
      c = r.config;
    in
    {
      top = c.topf;
      sub = c.s.f;
      at = c.at.k.f;
      lz = c.lz.k.f;
      ls = (builtins.head c.ls).f;
      no = c.no.f;
      ei = c.ei.f;
      aa = c.aa.k.j.f;
      d2 = c.d2.d.f;
      tr = c.tr.f;
      wa = c.wa.f;
      pa = unwrap c.pa.f;
      q = c.q.f;
      fo = c.fo.f;
      na = c.na.f;
      naN = c.na.n;
      de = c.de.f;
      fr = c.fr.f;
      mx = c.mx.k.f;
      # the declarations' view (nixpkgs' `base`, the placeholder alone) and the empty value
      docs = (r.options.s.type.getSubOptions [ "s" ])._module.args.files;
      docsF = (r.options.s.type.getSubOptions [ "s" ]).f.value;
      empty = (N.submodule innerNa).emptyValue.value.f;
      # the names, unchanged
      md = c.md.f;
      mdN = c.md.n;
      wn = c.wn.f;
      wnN = c.wn.n;
      mf = c.mf.f;
    };

  # ── where the three sit among the modules' own definitions ─────────────────────────────────────
  # The child's type module states `q` and imports one stating `w`; the seed states `z` and (`tr`)
  # imports one stating `y`. Each cell is the child's `files`.
  order =
    eng:
    let
      inherit (engine eng)
        N
        mkOption
        ev
        tree
        withArgs
        ;
      T = (engine eng).T;
      innerNa =
        { options, ... }:
        {
          options.f = mkOption { default = options._module.args.files; };
          options.lst = mkOption {
            type = T.listOf T.str;
            default = [ ];
          };
        };
      inner = {
        _file = "q.nix";
        _module.args.q = 1;
        lst = [ "q" ];
        imports = [
          innerNa
          {
            _file = "w.nix";
            _module.args.w = 1;
            lst = [ "w" ];
          }
        ];
      };
      # the own module keyed: the child's top level is not plain, so its definitions are classified through
      # the closure graph, read in the root's order
      innerK = inner // {
        key = "inner-k";
      };
      seed = {
        _module.args.z = 3;
        lst = [ "def" ];
      };
      seedT = seed // {
        imports = [
          {
            _file = "y.nix";
            _module.args.y = 4;
            lst = [ "y" ];
          }
        ];
      };
      mid = {
        _file = "mid.nix";
        options.d = mkOption { type = N.submodule inner; };
      };
      decl = {
        _file = "decl.nix";
        options = builtins.mapAttrs (_: type: mkOption { inherit type; }) {
          s = N.submodule inner;
          sk = N.submodule innerK;
          at = N.attrsOf (N.submodule inner);
          ls = N.listOf (N.submodule inner);
          no = N.nullOr (N.submodule inner);
          ei = N.either N.int (N.submodule inner);
          aa = N.attrsOf (N.attrsOf (N.submodule inner));
          d2 = N.submodule mid;
          tr = tree [ inner ];
          wa = withArgs inner { a = 1; };
          mx = np.types.attrsOf (N.submodule inner);
        };
      };
      def = {
        _file = "def.nix";
        config = {
          s = seed;
          sk = seed;
          at.k = seed;
          ls = [ seed ];
          no = seed;
          ei = seed;
          aa.k.j = seed;
          d2.d = seed;
          tr = seedT;
          wa = seed;
          mx.k = seed;
        };
      };
      def2 = {
        _file = "def2.nix";
        config.s._module.args.v = 5;
      };
      top = {
        _file = "top.nix";
        _module.args.t = 1;
        imports = [
          {
            _file = "topimp.nix";
            _module.args.ti = 1;
          }
        ];
      };
      topR =
        { options, ... }:
        {
          options.topf = mkOption { default = options._module.args.files; };
        };
      after = {
        _file = "after.nix";
        _module.args.after = 1;
        imports = [
          {
            _file = "ai.nix";
            _module.args.ai = 1;
          }
        ];
      };
      r = ev [
        decl
        def
        def2
        top
        topR
      ];
      c = r.config;
    in
    {
      top = c.topf;
      # a keyed top-level module, a removal, a top-level removal, a duplicate key: the closure-graph arm
      topK =
        (ev [
          {
            key = "k1";
            _file = "k1.nix";
            _module.args.k1 = 1;
            imports = [
              {
                _file = "k1i.nix";
                _module.args.k1i = 1;
              }
            ];
          }
          {
            _file = "k2.nix";
            _module.args.k2 = 1;
          }
          topR
        ]).config.topf;
      topD =
        (ev [
          {
            _file = "dis.nix";
            disabledModules = [ { key = "victim"; } ];
            _module.args.d = 1;
          }
          {
            _file = "imp.nix";
            imports = [
              {
                key = "victim";
                _file = "victim.nix";
                _module.args.v = 1;
              }
              {
                _file = "kept.nix";
                _module.args.kept = 1;
              }
            ];
            _module.args.i = 1;
          }
          topR
        ]).config.topf;
      topD2 =
        (ev [
          {
            _file = "dis.nix";
            disabledModules = [ { key = "v0"; } ];
          }
          {
            key = "v0";
            _file = "v0.nix";
            _module.args.v0 = 1;
          }
          after
          topR
        ]).config.topf;
      topKK =
        (ev [
          {
            key = "kk";
            _file = "kk1.nix";
            _module.args.kk = 1;
          }
          {
            key = "kk";
            _file = "kk2.nix";
            _module.args.kk = 1;
          }
          after
          topR
        ]).config.topf;
      sub = c.s.f;
      subK = c.sk.f;
      at = c.at.k.f;
      ls = (builtins.head c.ls).f;
      no = c.no.f;
      ei = c.ei.f;
      aa = c.aa.k.j.f;
      d2 = c.d2.d.f;
      tr = c.tr.f;
      wa = c.wa.f;
      mx = c.mx.k.f;
      docs = (r.options.s.type.getSubOptions [ "s" ])._module.args.files;
      empty = (N.submodule inner).emptyValue.value.f;
    };

  # ── the inner child's seed count against the definitions it collects ───────────────────────────
  seeds =
    eng:
    let
      inherit (engine eng) L N mkOption;
      reader =
        { options, ... }:
        {
          options.f = mkOption { default = options._module.args.files; };
        };
      tm = {
        _file = "q.nix";
        imports = [ reader ];
        _module.args.q = 1;
      };
      decl = {
        _file = "decl.nix";
        options.s = mkOption {
          type = N.submodule tm;
          default = { };
        };
        options.at = mkOption {
          type = N.attrsOf (N.submodule tm);
          default = { };
        };
      };
      run = defs: ((engine eng).ev ([ decl ] ++ defs)).config;
      dA = {
        _file = "a.nix";
        config.s._module.args.a = 1;
      };
      dMerge = {
        _file = "m.nix";
        config.s = L.mkMerge [
          { _module.args.b = 2; }
          { _module.args.c = 3; }
        ];
      };
      dIfF = {
        _file = "iff.nix";
        config.s = L.mkIf false { _module.args.d = 4; };
      };
      dIfT = {
        _file = "ift.nix";
        config.s = L.mkIf true { _module.args.e = 5; };
      };
      dAt = {
        _file = "at.nix";
        config.at.k = L.mkMerge [
          { _module.args.b = 2; }
          { }
        ];
      };
      dAtIfF = {
        _file = "atiff.nix";
        config.at = L.mkIf false { k._module.args.x = 1; };
      };
      dAt2 = {
        _file = "at2.nix";
        config.at.k._module.args.y = 1;
      };
    in
    {
      merge =
        (run [
          dA
          dMerge
        ]).s.f;
      ifFalse =
        (run [
          dA
          dIfF
        ]).s.f;
      ifTrue =
        (run [
          dA
          dIfT
        ]).s.f;
      ifFalseOnly = (run [ dIfF ]).s.f;
      atMerge =
        (run [
          dAt
          dAt2
        ]).at.k.f;
      atIfF =
        (run [
          dAtIfF
          dAt2
        ]).at.k.f;
    };

  # ── a module defining `extendModules`: the internal entry and the published field stay the engine's own ──
  extend =
    eng:
    let
      inherit (engine eng)
        L
        N
        mkOption
        ev
        ;
      reader =
        { options, ... }:
        {
          options.f = mkOption {
            default = map (d: {
              inherit (d) file;
              ext = show (d.value.extendModules or "<absent>");
            }) options._module.args.definitionsWithLocations;
          };
        };
      force5 = {
        _file = "f5.nix";
        _module.args.extendModules = L.mkForce 5;
      };
      plain5 = {
        _file = "p5.nix";
        _module.args.extendModules = 5;
      };
      ctl = {
        _file = "ctl.nix";
        _module.args.z = 1;
      };
      x.options.x = mkOption { default = 1; };
      served =
        { config, ... }:
        {
          options.s = mkOption { default = show config._module.args.extendModules; };
        };
      sub = m: {
        options.s = mkOption {
          type = N.submodule {
            imports = [
              reader
              m
            ];
          };
          default = { };
        };
      };
    in
    {
      topCtl =
        (ev [
          reader
          ctl
        ]).config.f;
      topForce =
        (ev [
          reader
          force5
        ]).config.f;
      topPlain =
        (ev [
          reader
          plain5
        ]).config.f;
      subCtl = (ev [ (sub ctl) ]).config.s.f;
      subForce = (ev [ (sub force5) ]).config.s.f;
      # the served value is the merge: `mkForce` wins
      servedForce =
        (ev [
          force5
          served
        ]).config.s;
      # the published `extendModules` is the engine's own, and re-evaluates
      published = show (ev [ force5 ]).extendModules;
      publishedExtends =
        (
          (ev [
            force5
            x
          ]).extendModules
            { modules = [ { config.x = 7; } ]; }
        ).config.x;
    };

  twinOf = fixture: eng: k: {
    expr = (fixture eng).${k};
    expected = (fixture "np").${k};
  };
  cellsOf =
    group: fixture: engs: ks:
    builtins.listToAttrs (
      builtins.concatMap (
        eng:
        map (k: {
          name = "test-${group}-${k}-${if eng == "gm" then "gen" else "bridge"}";
          value = twinOf fixture eng k;
        }) ks
      ) engs
    );
  both = [
    "gm"
    "mix"
  ];
in
{
  flake.tests.module-args-definitions =
    cellsOf "record" shapes both [
      "top"
      "sub"
      "at"
      "lz"
      "ls"
      "no"
      "ei"
      "aa"
      "d2"
      "tr"
      "wa"
      "pa"
      "q"
      "fo"
      "na"
      "naN"
      "de"
      "fr"
      "mx"
      "docs"
      "docsF"
      "empty"
      "md"
      "mdN"
      "wn"
      "wnN"
    ]
    // cellsOf "order" order both [
      "top"
      "topK"
      "topD"
      "topD2"
      "topKK"
      "sub"
      "subK"
      "at"
      "ls"
      "no"
      "ei"
      "aa"
      "d2"
      "wa"
      "mx"
      "docs"
      "empty"
      "tr"
    ]
    // cellsOf "seeds" seeds both [
      "merge"
      "ifFalse"
      "ifTrue"
      "ifFalseOnly"
      "atMerge"
      "atIfF"
    ]
    // cellsOf "extend" extend both [
      "topCtl"
      "topForce"
      "topPlain"
      "subCtl"
      "subForce"
      "servedForce"
    ]
    //
      cellsOf "extend" extend
        [ "gm" ]
        [
          "published"
          "publishedExtends"
        ]
    // builtins.listToAttrs (
      builtins.concatMap (
        eng:
        let
          tag = if eng == "gm" then "gen" else "bridge";
          g = (shapes eng).mf;
          n = (shapes "np").mf;
        in
        [
          {
            # the definitions are nixpkgs'
            name = "test-record-mf-${tag}-definitions";
            value = {
              expr = removeAttrs g [
                "vkeys"
                "cname"
              ];
              expected = removeAttrs n [
                "vkeys"
                "cname"
              ];
            };
          }
          {
            # den-hoag-b44rx: the forced set is not the whole value
            name = "test-record-mf-${tag}-value-pinned-b44rx";
            value = {
              expr = {
                gen = { inherit (g) vkeys cname; };
                nixpkgs = { inherit (n) vkeys cname; };
              };
              expected = {
                gen = {
                  vkeys = [
                    "extendModules"
                    "moduleType"
                    "name"
                    "q"
                  ];
                  cname = "mf";
                };
                nixpkgs = {
                  vkeys = [ "q" ];
                  cname = "<none>";
                };
              };
            };
          }
        ]
      ) both
    );
}
