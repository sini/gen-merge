# Per-key priority on the freeform plane (den-hoag-0g61j): a freeform key's provenance record carries the
# override priority its own value fold selected, and `priorityState` says which of three things the record
# knows. `observed`: the fold is gen's own key-local selection (`attrsOf` / `lazyAttrsOf` as their constructor
# completed them, and `anything` below a declared group), and `priority` is the number it selected.
# `noDefinition`: that fold selected nothing (every definition discharged). `unobservable`: the fold is any
# other (opaque, foreign, custom, a door copy), so gen cannot say, and `priority` is null; it is never read
# as empty. `bandedLeaves` classifies by the state. The refusals (a priority read meeting its own key's
# error) are in ../tests-error.nix `freeformPriority`.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  t = gm.types;
  np = nixpkgsLib;
  ev = gm.evalModuleTree { };
  ff = ty: mods: ev ([ { freeformType = ty; } ] ++ mods);
  A = t.attrsOf t.anything;
  st = p: {
    inherit (p) priority priorityState;
  };
  # A read that must not throw: `ok` is false where the read (deep-forced) throws.
  try =
    v:
    let
      r = builtins.tryEval (builtins.deepSeq v v);
    in
    if r.success then
      {
        ok = true;
        v = r.value;
      }
    else
      { ok = false; };
  throws = v: !(builtins.tryEval (builtins.deepSeq v v)).success;
  get = loc: s: builtins.foldl' (a: k: a.${k}) s loc;
  band =
    scope: r: loc:
    removeAttrs (get loc (gm.bandedLeaves scope r)) [ "winners" ];

  # The demand control: a sibling that throws at weak head normal form, never forced by a priority read.
  sib = {
    _file = "a.nix";
    a = gm.mkForce 1;
    b = throw "SIBLING-FORCED";
  };
  demandA = ff A [ sib ];
  demandLazy = ff (t.lazyAttrsOf t.int) [ sib ];
  # A sibling throwing BELOW weak head normal form: value laziness, not the demand control (a classifier that
  # forced every sibling's priority would not throw here).
  belowWhnf = ff A [
    {
      _file = "a.nix";
      a = gm.mkForce 1;
      b.z = throw "SIBLING-FORCED";
    }
  ];

  states = ff A [
    {
      _file = "s.nix";
      plain = 1;
      dflt = gm.mkDefault 2;
      odflt = gm.mkOptionDefault 3;
      gone = gm.mkIf false 4;
      nul = null;
      ord = gm.mkBefore [ 1 ];
    }
  ];
  # den-hoag-6dxwr's two kept-empty arms: the key survives in config, and no definition does.
  keptEmpty = ff (t.lazyAttrsOf (t.listOf t.str)) [
    {
      _file = "l.nix";
      kept = gm.mkIf false [ "x" ];
      live = [ "y" ];
    }
  ];
  keptWritten = ff (t.lazyAttrsOf ((t.listOf t.str) // { emptyValue.value = [ "WE" ]; })) [
    {
      _file = "l.nix";
      kept = gm.mkIf false [ "x" ];
    }
  ];
  # An opaque fold: a foreign type record with its own `merge`.
  opaque = {
    _type = "option-type";
    name = "opaque";
    description = "custom opaque fold";
    check = builtins.isAttrs;
    merge = _loc: defs: builtins.foldl' (a: d: a // d.value) { } defs;
  };
  opaqueEval = ff opaque [
    {
      _file = "o.nix";
      k = gm.mkForce 1;
    }
  ];
  groupDecl = {
    options.g.c = gm.mkOption {
      type = t.str;
      default = "c";
    };
  };
  group = ff A [
    groupDecl
    {
      _file = "g.nix";
      g.x = gm.mkForce "X";
      g.y = "Y";
    }
  ];
  # Below a declared group, `attrsOf str`'s element is `str`, which selects nothing key-locally.
  groupStr = ff (t.attrsOf t.str) [
    groupDecl
    {
      _file = "g.nix";
      g.x = gm.mkForce "X";
    }
  ];
  # A declared group named `__mint`: every definition of `g` holds `__mint`, so `anything` carries `g` whole
  # (`mergeLeaf`) and selects nothing for `g.k`.
  mintDeep = ff A [
    {
      options.g.__mint.c = gm.mkOption {
        type = t.int;
        default = 0;
      };
    }
    {
      _file = "m.nix";
      g.__mint.y = gm.mkForce 1;
      g.k = gm.mkForce "K";
    }
  ];

  # Two contributor evaluations, compared by band and never by raw number (ADR-0029), as den's `compose` picks.
  layer = file: mods: ff A (map (m: { _file = file; } // m) mods);
  rank = {
    force = 0;
    set = 1;
    default = 2;
  };
  pick =
    r: l:
    let
      br = (gm.bandedLeaves "registry" r).x;
      bh = (gm.bandedLeaves "relation" l).x;
    in
    if !(br ? band) && !(bh ? band) then
      "neither-bands"
    else if !(br ? band) then
      bh.value
    else if !(bh ? band) then
      br.value
    else if rank.${br.band} < rank.${bh.band} then
      br.value
    else
      bh.value;
  registry = layer "<den.users>" [ { x = gm.mkForce "R"; } ];
  relation = layer "<den.hosts>" [ { x = "H"; } ];
  # A schema module and the layer's own definition of `groups`, each layer its own evaluation. Every value
  # asserted is one survivor nixpkgs' `attrsOf anything` also serves (the twin below); a same-band pair of
  # unequal lists in ONE layer is concatenated by gen's `anything` and refused by nixpkgs', so for that arm
  # only the band is asserted.
  lay =
    file: schema: own:
    layer file [
      { groups = schema; }
      { groups = own; }
    ];
  npLay =
    schema: own:
    (np.evalModules {
      modules = [
        { freeformType = np.types.attrsOf np.types.anything; }
        { groups = schema; }
        { groups = own; }
      ];
    }).config.groups;

  # Cold and warm: an edit that moves a priority, one that adds a discharged definition, and one that flips a
  # declared option a freeform condition reads.
  base7 = [
    { freeformType = A; }
    {
      _file = "w.nix";
      x = "a";
      y = "b";
    }
  ];
  warm7 =
    base: e:
    let
      w = gm.evalModuleTree {
        warmFrom = ev base;
        editedModules = e;
      } (base ++ e);
      c = ev (base ++ e);
    in
    {
      mode = w.warmDecision.mode;
      warm = builtins.mapAttrs (_: st) w.provenance;
      cold = builtins.mapAttrs (_: st) c.provenance;
      json = builtins.toJSON w.provenance == builtins.toJSON c.provenance;
    };
  flagBase = [
    {
      freeformType = A;
      options.flag = gm.mkOption {
        type = t.bool;
        default = true;
      };
    }
    (
      { config, ... }:
      {
        _file = "c.nix";
        x = gm.mkIf config.flag (gm.mkForce "F");
      }
    )
    {
      _file = "p.nix";
      x = gm.mkDefault "D";
    }
  ];
  flagEdit = [
    {
      _file = "e.nix";
      flag = false;
    }
  ];

  # The hazard set: freeformType declared more than once, in every order; the doors.
  perms =
    xs:
    if xs == [ ] then
      [ [ ] ]
    else
      builtins.concatMap (x: map (q: [ x ] ++ q) (perms (builtins.filter (y: y != x) xs))) xs;
  orders =
    tys: map (o: map (builtins.elemAt tys) o) (perms (builtins.genList (i: i) (builtins.length tys)));
  declared =
    tys: mods:
    let
      r = ev (map (ty: { freeformType = ty; }) tys ++ mods);
    in
    st r.provenance.k // { value = r.config.k; };
  twoDefs = [
    {
      _file = "k.nix";
      k = gm.mkForce [ 1 ];
    }
    {
      _file = "j.nix";
      k = [ 2 ];
    }
  ];
  subP = t.submodule {
    options.p = gm.mkOption {
      type = t.int;
      default = 0;
    };
  };
  subQ = t.submodule {
    options.q = gm.mkOption {
      type = t.int;
      default = 0;
    };
  };
  payloadDefs = [
    {
      _file = "k.nix";
      k = gm.mkForce { p = 1; };
    }
    {
      _file = "j.nix";
      k = {
        q = 2;
      };
    }
  ];
  distinct =
    rs:
    builtins.attrNames (
      builtins.listToAttrs (
        map (r: {
          name = builtins.toJSON r;
          value = null;
        }) rs
      )
    );
in
{
  flake.tests.freeformPriority = {
    # The demand control (Artemis's constraint): one key's priority read beside a sibling that throws at weak
    # head normal form answers without forcing it, under `attrsOf` through `provenance` and under `lazyAttrsOf`
    # through `bandedLeaves` (`attrsOf`'s `bandedLeaves` reads `options`, which forces every definition, as
    # nixpkgs' `options` does). The control is that the sibling's value throws.
    test-demand-control-provenance-beside-a-throwing-sibling = {
      expr = {
        a = try (st demandA.provenance.a);
        siblingThrows = throws demandA.config.b;
      };
      expected = {
        a = {
          ok = true;
          v = {
            priority = 50;
            priorityState = "observed";
          };
        };
        siblingThrows = true;
      };
    };
    test-demand-control-banded-leaves-under-lazy-attrs-of = {
      expr = {
        a = try (band "r" demandLazy [ "a" ]);
        siblingThrows = throws demandLazy.config.b;
      };
      expected = {
        a = {
          ok = true;
          v = {
            scope = "r";
            loc = [ "a" ];
            band = "force";
            priority = 50;
            value = 1;
          };
        };
        siblingThrows = true;
      };
    };
    # Value laziness (not the demand control): a band read does not force a sibling's value below its head.
    test-a-band-read-forces-no-sibling-value-below-its-head = {
      expr = {
        a = try (band "r" belowWhnf [ "a" ]);
        siblingThrows = throws belowWhnf.config.b;
      };
      expected = {
        a = {
          ok = true;
          v = {
            scope = "r";
            loc = [ "a" ];
            band = "force";
            priority = 50;
            value = 1;
          };
        };
        siblingThrows = true;
      };
    };

    test-observed-states = {
      expr = builtins.mapAttrs (_: st) {
        inherit (states.provenance)
          plain
          dflt
          odflt
          nul
          ord
          ;
      };
      expected = {
        plain = {
          priority = 100;
          priorityState = "observed";
        };
        dflt = {
          priority = 1000;
          priorityState = "observed";
        };
        odflt = {
          priority = 1500;
          priorityState = "observed";
        };
        # a live explicit null carries a band
        nul = {
          priority = 100;
          priorityState = "observed";
        };
        # `mkOrder` stays separate
        ord = {
          priority = 100;
          priorityState = "observed";
        };
      };
    };
    test-observed-bands = {
      expr = builtins.mapAttrs (n: _: band "r" states [ n ]) {
        plain = 0;
        dflt = 0;
        odflt = 0;
        nul = 0;
      };
      expected = {
        plain = {
          scope = "r";
          loc = [ "plain" ];
          band = "set";
          priority = 100;
          value = 1;
        };
        dflt = {
          scope = "r";
          loc = [ "dflt" ];
          band = "default";
          priority = 1000;
          value = 2;
        };
        odflt = {
          scope = "r";
          loc = [ "odflt" ];
          reason = "unset: default-only";
          priority = 1500;
          defaulted = null;
        };
        nul = {
          scope = "r";
          loc = [ "nul" ];
          band = "set";
          priority = 100;
          value = null;
        };
      };
    };
    # `mkIf false` discharges before any override is read: under `attrsOf` the key leaves config, and under
    # `lazyAttrsOf` (both of 6dxwr's kept-empty arms) it stays at the element's empty value. Either way no
    # definition survives, and the key carries no band.
    test-no-definition-states = {
      expr = {
        gone = st states.provenance.gone;
        goneInConfig = states.config ? gone;
        goneBand = band "r" states [ "gone" ];
        kept = st keptEmpty.provenance.kept;
        keptValue = keptEmpty.config.kept;
        keptBand = band "r" keptEmpty [ "kept" ];
        live = st keptEmpty.provenance.live;
        written = st keptWritten.provenance.kept;
        writtenValue = keptWritten.config.kept;
      };
      expected =
        let
          none = {
            priority = null;
            priorityState = "noDefinition";
          };
        in
        {
          gone = none;
          goneInConfig = false;
          goneBand = {
            scope = "r";
            loc = [ "gone" ];
            reason = "unset: no definition";
          };
          kept = none;
          keptValue = [ ];
          keptBand = {
            scope = "r";
            loc = [ "kept" ];
            reason = "unset: no definition";
          };
          live = {
            priority = 100;
            priorityState = "observed";
          };
          written = none;
          writtenValue = [ "WE" ];
        };
    };
    test-unobservable-states = {
      expr = {
        opaque = st opaqueEval.provenance.k;
        opaqueBand = band "r" opaqueEval [ "k" ];
        groupStr = st groupStr.provenance.g.x;
        groupStrBand = band "r" groupStr [
          "g"
          "x"
        ];
      };
      expected =
        let
          unobs = {
            priority = null;
            priorityState = "unobservable";
          };
        in
        {
          opaque = unobs;
          opaqueBand = {
            scope = "r";
            loc = [ "k" ];
            reason = "unset: freeform";
          };
          groupStr = unobs;
          groupStrBand = {
            scope = "r";
            loc = [
              "g"
              "x"
            ];
            reason = "unset: freeform";
          };
        };
    };
    # den's case: keys below a declared group, the declared sibling unchanged.
    test-below-a-declared-group = {
      expr = {
        x = st group.provenance.g.x;
        y = st group.provenance.g.y;
        c = group.provenance.g.c.priority;
        cHasNoState = group.provenance.g.c ? priorityState;
        xBand = band "r" group [
          "g"
          "x"
        ];
      };
      expected = {
        x = {
          priority = 50;
          priorityState = "observed";
        };
        y = {
          priority = 100;
          priorityState = "observed";
        };
        c = 1500;
        cHasNoState = false;
        xBand = {
          scope = "r";
          loc = [
            "g"
            "x"
          ];
          band = "force";
          priority = 50;
          value = "X";
        };
      };
    };
    # gate C1: a record below `__mint` marks its module, as the value fold's `? __mint` reads it.
    test-a-record-below-mint-makes-its-group-unobservable = {
      expr = {
        k = st mintDeep.provenance.g.k;
        y = st mintDeep.provenance.g.__mint.y;
      };
      expected = {
        k = {
          priority = null;
          priorityState = "unobservable";
        };
        y = {
          priority = null;
          priorityState = "unobservable";
        };
      };
    };

    # The legacy fields are not reinterpreted, and the record gains exactly one key.
    test-old-readers-unchanged = {
      expr = {
        inherit (states.provenance.plain) defs winners defaulted;
        keys = builtins.attrNames states.provenance.plain;
        inherit (states) undeclared;
        config = builtins.toJSON states.config;
      };
      expected = {
        defs = [ { file = "s.nix"; } ];
        winners = null;
        defaulted = null;
        keys = [
          "defaulted"
          "defs"
          "priority"
          "priorityState"
          "winners"
        ];
        undeclared = [ ];
        config = ''{"dflt":2,"nul":null,"odflt":3,"ord":[1],"plain":1}'';
      };
    };

    # A registry mkForce against a plain per-host value resolves by band.
    test-registry-force-beats-a-plain-relation-by-band = {
      expr = {
        reg = band "registry" registry [ "x" ];
        rel = band "relation" relation [ "x" ];
        picked = pick registry relation;
      };
      expected = {
        reg = {
          scope = "registry";
          loc = [ "x" ];
          band = "force";
          priority = 50;
          value = "R";
        };
        rel = {
          scope = "relation";
          loc = [ "x" ];
          band = "set";
          priority = 100;
          value = "H";
        };
        picked = "R";
      };
    };
    # Schema same-band append, by actual survivors: each value is the layer's own survivors, equal to the
    # nixpkgs twin's. In the same-band-with-schema arm gen serves a concatenation nixpkgs refuses, so only the
    # band and priority are read there.
    test-schema-append-reads-actual-survivors = {
      expr = {
        schemaDefault = band "r" (lay "<den.users>" (gm.mkDefault [ "base" ]) [ "video" ]) [ "groups" ];
        schemaDefaultTwin = npLay (np.mkDefault [ "base" ]) [ "video" ];
        reset = band "h" (lay "<den.hosts>" [ "base" ] (gm.mkForce [ "wheel" ])) [ "groups" ];
        resetTwin = npLay [ "base" ] (np.mkForce [ "wheel" ]);
        sameBand =
          let
            b = band "r" (lay "<den.users>" [ "base" ] [ "video" ]) [ "groups" ];
          in
          {
            inherit (b) band priority;
          };
      };
      expected = {
        schemaDefault = {
          scope = "r";
          loc = [ "groups" ];
          band = "set";
          priority = 100;
          value = [ "video" ];
        };
        schemaDefaultTwin = [ "video" ];
        reset = {
          scope = "h";
          loc = [ "groups" ];
          band = "force";
          priority = 50;
          value = [ "wheel" ];
        };
        resetTwin = [ "wheel" ];
        sameBand = {
          band = "set";
          priority = 100;
        };
      };
    };

    # A key's error stays its own: its `defs` still answer, and a sibling's priority reads (the throws are in
    # ../tests-error.nix `freeformPriority`).
    test-a-throwing-key-keeps-its-defs-and-its-siblings = {
      expr =
        let
          r = ff A [
            {
              _file = "e.nix";
              x = gm.mkIf (throw "COND") 1;
              y = throw "VAL";
              a = gm.mkOverride 40 1;
            }
          ];
        in
        {
          xDefs = r.provenance.x.defs;
          yDefs = r.provenance.y.defs;
          a = st r.provenance.a;
        };
      expected = {
        xDefs = [ { file = "e.nix"; } ];
        yDefs = [ { file = "e.nix"; } ];
        a = {
          priority = 40;
          priorityState = "observed";
        };
      };
    };
    # Override content stays lazy: the priority reads, the value throws.
    test-a-forced-throw-reads-its-priority = {
      expr =
        let
          r = ff A [
            {
              _file = "e.nix";
              a = gm.mkForce (throw "CONTENT");
            }
          ];
        in
        {
          a = st r.provenance.a;
          valueThrows = throws r.config.a;
        };
      expected = {
        a = {
          priority = 50;
          priorityState = "observed";
        };
        valueThrows = true;
      };
    };

    # Warm reuse never reports an old winner: warm equals cold on every record and on the serialization.
    test-warm-equals-cold-after-a-priority-edit = {
      expr = warm7 base7 [
        {
          _file = "w2.nix";
          x = gm.mkForce "F";
        }
      ];
      expected = {
        mode = "warm";
        warm = {
          x = {
            priority = 50;
            priorityState = "observed";
          };
          y = {
            priority = 100;
            priorityState = "observed";
          };
        };
        cold = {
          x = {
            priority = 50;
            priorityState = "observed";
          };
          y = {
            priority = 100;
            priorityState = "observed";
          };
        };
        json = true;
      };
    };
    test-warm-equals-cold-after-a-condition-edit = {
      expr = warm7 base7 [
        {
          _file = "w3.nix";
          y = gm.mkIf false "z";
        }
      ];
      expected = {
        mode = "warm";
        warm = {
          x = {
            priority = 100;
            priorityState = "observed";
          };
          y = {
            priority = 100;
            priorityState = "observed";
          };
        };
        cold = {
          x = {
            priority = 100;
            priorityState = "observed";
          };
          y = {
            priority = 100;
            priorityState = "observed";
          };
        };
        json = true;
      };
    };
    test-warm-follows-a-declared-option-a-condition-reads = {
      expr =
        let
          prior = ev flagBase;
          w = gm.evalModuleTree {
            warmFrom = prior;
            editedModules = flagEdit;
          } (flagBase ++ flagEdit);
          c = ev (flagBase ++ flagEdit);
        in
        {
          prior = st prior.provenance.x;
          warm = st w.provenance.x;
          cold = st c.provenance.x;
          value = w.config.x;
        };
      expected = {
        prior = {
          priority = 50;
          priorityState = "observed";
        };
        warm = {
          priority = 1000;
          priorityState = "observed";
        };
        cold = {
          priority = 1000;
          priorityState = "observed";
        };
        value = "D";
      };
    };

    # Both doors over `attrsOf anything` run the export bridge, not the completed fold the classifier
    # recognises, so a door copy is unobservable (gate OQ1, arm (b)); its values equal the raw form's.
    test-door-copies-are-unobservable-with-raw-values = {
      expr = {
        raw = declared [ A ] twoDefs;
        doorMk = declared [ (gm.mkOptionType A) ] twoDefs;
        doorTypes = declared [ (t.mkOptionType A) ] twoDefs;
      };
      expected = {
        raw = {
          priority = 50;
          priorityState = "observed";
          value = [ 1 ];
        };
        doorMk = {
          priority = null;
          priorityState = "unobservable";
          value = [ 1 ];
        };
        doorTypes = {
          priority = null;
          priorityState = "unobservable";
          value = [ 1 ];
        };
      };
    };
    # Payload-dependent partners: two `attrsOf (submodule …)` declarations whose elements merge by payload.
    test-payload-dependent-pair-both-orders = {
      expr = map (tys: declared tys payloadDefs) (orders [
        (t.attrsOf subP)
        (t.attrsOf subQ)
      ]);
      expected =
        let
          r = {
            priority = 50;
            priorityState = "observed";
            value = {
              p = 1;
              q = 0;
            };
          };
        in
        [
          r
          r
        ];
    };
    # Four gen declarations (a raw form, two fresh constructions, a `//` copy), all 24 orders: one answer.
    test-four-gen-declarations-every-order = {
      expr =
        let
          rs = map (tys: declared tys twoDefs) (orders [
            A
            (t.attrsOf t.anything)
            (A // { description = "copy"; })
            (t.attrsOf t.anything)
          ]);
        in
        {
          count = builtins.length rs;
          distinct = distinct rs;
        };
      expected = {
        count = 24;
        distinct = [ ''{"priority":50,"priorityState":"observed","value":[1]}'' ];
      };
    };
  };
}
