# `priorityBand` and `bandedLeaves` (den-hoag-zakjg U1): the band each contributor's own
# evaluation resolved a leaf at, read from real `evalModuleTree` provenance. The canonical cases
# k1–k6 are the reconsideration spec's (host r, environment t, each its own evaluation against
# `x : str, default = "RD"`); every record is the one gen-view's `joinedTrace` joins back. The
# refusals (a value that still throws, a user error that propagates) are in ../tests-error.nix
# `bands`.
{ genMerge, ... }:
let
  gm = genMerge;
  t = gm.types;
  optDecl = {
    options.x = gm.mkOption {
      type = t.str;
      default = "RD";
    };
  };
  # A contributor's definitions carry its own `_file`, so a winner's file names its contributor.
  evalAs =
    scope: defs:
    gm.evalModuleTree { } (
      [
        optDecl
      ]
      ++ map (d: {
        _file = "${scope}.nix";
        config.x = d;
      }) defs
    );
  bandOf = scope: defs: (gm.bandedLeaves scope (evalAs scope defs)).x;
  cases = {
    k1 = {
      host = [ "R" ];
      env = [ "T" ];
    };
    k2 = {
      host = [ (gm.mkDefault "RD") ];
      env = [ "T" ];
    };
    k3 = {
      host = [ ];
      env = [ (gm.mkDefault "TD") ];
    };
    k4 = {
      host = [ "R" ];
      env = [ (gm.mkForce "TF") ];
    };
    k5 = {
      host = [ (gm.mkOptionDefault "RO") ];
      env = [ ];
    };
    k6 = {
      host = [ ];
      env = [ ];
    };
  };
  pair = k: {
    r = bandOf "r" cases.${k}.host;
    t = bandOf "t" cases.${k}.env;
  };
  moved = scope: band: priority: value: {
    inherit
      scope
      band
      priority
      value
      ;
    loc = [ "x" ];
    winners = [ { file = "${scope}.nix"; } ];
  };
  defaultOnly = scope: defaulted: {
    inherit scope defaulted;
    loc = [ "x" ];
    reason = "unset: default-only";
    priority = 1500;
  };

  # The C1 leaves, beside ordinary ones, in one evaluation.
  c1 = gm.evalModuleTree { } [
    {
      freeformType = t.attrsOf t.str;
      options.undefined = gm.mkOption { type = t.str; };
      options.empty = gm.mkOption { type = t.attrsOf t.str; };
      options.planted = gm.mkOption {
        type = t.str;
        default = throw "PLANTED";
      };
      options.g.x = gm.mkOption {
        type = t.str;
        default = "d";
      };
    }
    { free = "f"; }
  ];
  c1Bands = gm.bandedLeaves "c" c1;
  files = rec': map (w: w.file) rec'.winners;
  conflicting = gm.evalModuleTree { } [
    { options.x = gm.mkOption { type = t.str; }; }
    { x = "a"; }
    { x = "b"; }
  ];
in
{
  flake.tests.bands = {
    # The owner's thresholds, on both sides of every boundary.
    test-thresholds =
      let
        ps = [
          (-1)
          50
          99
          100
          999
          1000
          1499
          1500
          9999
        ];
      in
      {
        expr = map gm.priorityBand ps;
        expected = [
          "force"
          "force"
          "force"
          "set"
          "set"
          "default"
          "default"
          "unset"
          "unset"
        ];
      };
    # The band of each definition form, read through real provenance rather than a number.
    test-each-form-bands-through-real-provenance = {
      expr = map (d: (bandOf "r" d).band or (bandOf "r" d).reason) [
        [ (gm.mkForce "a") ]
        [ (gm.mkOverride 99 "a") ]
        [ "a" ]
        [ (gm.mkOverride 999 "a") ]
        [ (gm.mkDefault "a") ]
        [ (gm.mkOverride 1499 "a") ]
        [ ]
        [ (gm.mkOptionDefault "a") ]
      ];
      expected = [
        "force"
        "force"
        "set"
        "set"
        "default"
        "default"
        "unset: default-only"
        "unset: default-only"
      ];
    };

    test-k1 = {
      expr = pair "k1";
      expected = {
        r = moved "r" "set" 100 "R";
        t = moved "t" "set" 100 "T";
      };
    };
    test-k2 = {
      expr = pair "k2";
      expected = {
        r = moved "r" "default" 1000 "RD";
        t = moved "t" "set" 100 "T";
      };
    };
    test-k3 = {
      expr = pair "k3";
      expected = {
        r = defaultOnly "r" true;
        t = moved "t" "default" 1000 "TD";
      };
    };
    test-k4 = {
      expr = pair "k4";
      expected = {
        r = moved "r" "set" 100 "R";
        t = moved "t" "force" 50 "TF";
      };
    };
    # mkOptionDefault ties the declared default at 1500: two winners, so not `defaulted`.
    test-k5 = {
      expr = pair "k5";
      expected = {
        r = defaultOnly "r" false;
        t = defaultOnly "t" true;
      };
    };
    test-k6 = {
      expr = pair "k6";
      expected = {
        r = defaultOnly "r" true;
        t = defaultOnly "t" true;
      };
    };

    # One unset record per reason, through real provenance (gate C1). The planted default is never
    # forced: the whole tree is deep-forced here, and reading `config.planted` fires it (the control
    # is `test-the-planted-default-fires-when-the-value-is-read` in ../tests-error.nix).
    test-every-unset-reason = {
      expr = builtins.deepSeq c1Bands c1Bands;
      expected = {
        undefined = {
          scope = "c";
          loc = [ "undefined" ];
          reason = "unset: no definition";
        };
        empty = {
          scope = "c";
          loc = [ "empty" ];
          reason = "unset: no definition";
        };
        planted = {
          scope = "c";
          loc = [ "planted" ];
          reason = "unset: default-only";
          priority = 1500;
          defaulted = true;
        };
        g.x = {
          scope = "c";
          loc = [
            "g"
            "x"
          ];
          reason = "unset: default-only";
          priority = 1500;
          defaulted = true;
        };
        free = {
          scope = "c";
          loc = [ "free" ];
          reason = "unset: freeform";
        };
      };
    };
    # The engine half: an undefined leaf's provenance is the empty record (its value still refuses:
    # ../tests-error.nix), and it is the record an empty-able type with no definitions publishes.
    test-an-undefined-leaf-has-the-empty-provenance-record = {
      expr = {
        inherit (c1.provenance) undefined empty;
      };
      expected =
        let
          none = {
            defs = [ ];
            winners = [ ];
            priority = null;
            defaulted = false;
          };
        in
        {
          undefined = none;
          empty = none;
        };
    };

    # Lazy per loc: a leaf whose definition throws on discharge is never touched by reading another.
    test-reading-one-leaf-forces-no-other = {
      expr =
        (gm.bandedLeaves "r" (
          gm.evalModuleTree { } [
            {
              options.x = gm.mkOption { type = t.str; };
              options.y = gm.mkOption { type = t.str; };
            }
            {
              x = "v";
              y = throw "UNREAD";
            }
          ]
        )).x.band;
      expected = "set";
    };

    # The band read never forces the merged value: `x` defined twice at one priority has a band and a
    # priority, while its value refuses (../tests-error.nix
    # `test-a-conflicting-leaf-value-refuses-where-its-band-reads`).
    test-a-conflicting-leaf-bands-without-forcing-its-value =
      let
        b = (gm.bandedLeaves "r" conflicting).x;
      in
      {
        expr = {
          inherit (b) band priority;
        };
        expected = {
          band = "set";
          priority = 100;
        };
      };

    # `scope` is the caller's and every other field is this result's own (the U2/U3 gate's P1): with
    # each contributor's modules carrying its own `_file`, an honest pairing's winners name only its
    # own files, and a pairing of `r` with `t`'s evaluation shows `t`'s files under scope `r`.
    test-winners-belong-to-the-evaluation-the-record-was-read-from = {
      expr = {
        honest = map (s: files (bandOf s [ s ])) [
          "r"
          "t"
        ];
        swapped = files ((gm.bandedLeaves "r" (evalAs "t" [ "T" ])).x);
      };
      expected = {
        honest = [
          [ "r.nix" ]
          [ "t.nix" ]
        ];
        swapped = [ "t.nix" ];
      };
    };
  };
}
