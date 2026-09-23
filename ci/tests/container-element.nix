{ genMerge, ... }:
let
  gm = genMerge;
  inherit (gm) evalModuleTree mkOption mkIf;
  t = gm.types;

  # A lax tree, `known` its one option.
  mt =
    (evalModuleTree {
      check = false;
      modules = [
        {
          options.known = mkOption {
            type = t.str;
            default = "k";
          };
        }
      ];
    }).type;
  # A lax tree whose leaf `sub` is itself a lax tree.
  t2 =
    (evalModuleTree {
      check = false;
      modules = [
        {
          options.k = mkOption {
            type = t.str;
            default = "d";
          };
        }
      ];
    }).type;
  t1 =
    (evalModuleTree {
      check = false;
      modules = [
        {
          options.known = mkOption {
            type = t.str;
            default = "k";
          };
          options.flag = mkOption {
            type = t.bool;
            default = false;
          };
          options.sub = mkOption { type = t2; };
        }
      ];
    }).type;
  run =
    ty: def:
    evalModuleTree {
      check = false;
      modules = [
        { options.x = mkOption { type = ty; }; }
        {
          _file = "/real/F.nix";
          config.x = def;
        }
      ];
    };
  runM =
    ty: m:
    evalModuleTree {
      check = false;
      modules = [
        { options.x = mkOption { type = ty; }; }
        m
      ];
    };
  forces = e: (builtins.tryEval (builtins.deepSeq e null)).success;
  bad = {
    known = "v";
    bogus = 1;
  };
in
{
  flake.tests.container-element = {
    # A tree merged as a container element carries no undeclared report, so a key its own level
    # does not declare is refused by name rather than dropped. LIVE CONTROLS in the same cell: the
    # container's own WHNF forces no element, clean elements are values, and the same tree typed
    # bare still reports rather than refuses.
    test-an-element-tree-refuses-what-it-cannot-report = {
      expr = {
        containerWhnf =
          (builtins.tryEval (builtins.seq (run (t.attrsOf mt) { a = bad; }).config.x null)).success;
        cleanValues = [
          (run (t.attrsOf mt) { a.known = "v"; }).config.x
          (run (t.listOf mt) [ { known = "v"; } ]).config.x
          (run (t.nullOr mt) { known = "v"; }).config.x
        ];
        bareReport = (run mt bad).undeclared;
        refusedNotDropped = !(forces (run (t.attrsOf mt) { a = bad; }).config.x);
      };
      expected = {
        containerWhnf = true;
        cleanValues = [
          { a.known = "v"; }
          [ { known = "v"; } ]
          { known = "v"; }
        ];
        bareReport = [
          {
            file = "/real/F.nix";
            path = [
              "x"
              "bogus"
            ];
          }
        ];
        refusedNotDropped = true;
      };
    };

    # THE REFUSAL IS PER LEVEL, AS nixpkgs REFUSES. An element's WHNF decides its OWN level only:
    # a tree nested inside the element is not forced to decide it. A throwing, or self-referential,
    # nested-tree leaf the read never reaches stays unforced, exactly as in nixpkgs
    # (`attrsOf ((evalModules …).type)` gives "v" and "s" on the same inputs). A deciding
    # predicate that walked the nested trees' findings throws `lazy-sub` on the first and aborts
    # with an uncatchable infinite recursion on the second.
    test-an-element-tree-decides-its-own-level-only = {
      expr = {
        subThrowElem =
          (runM (t.attrsOf t1) {
            config.x.a = {
              known = "v";
              sub = throw "lazy-sub";
            };
          }).config.x.a.known;
        selfRefElem =
          (runM (t.attrsOf t1) (
            { config, ... }:
            {
              config.x.a = {
                known = "v";
                flag = true;
                sub = mkIf config.x.a.flag { k = "s"; };
              };
            }
          )).config.x.a.sub.k;
        # The finding one level down is still not dropped: it is refused when ITS level is read,
        # and a read of the element's own level is a value.
        subBadKnown =
          (run (t.attrsOf t1) {
            a = {
              known = "v";
              sub = {
                k = "s";
                bogus = 1;
              };
            };
          }).config.x.a.known;
        subBadRefused =
          !(forces
            (run (t.attrsOf t1) {
              a = {
                known = "v";
                sub = {
                  k = "s";
                  bogus = 1;
                };
              };
            }).config.x.a.sub
          );
      };
      expected = {
        subThrowElem = "v";
        selfRefElem = "s";
        subBadKnown = "v";
        subBadRefused = true;
      };
    };

    # THE EMPTY VALUE TAKES THE SAME SITE RULE (9f4bn K4). A tree whose OWN module set defines an
    # undeclared `zz`, used for an option nobody defines: where the report is carried the empty
    # value is the lax fold over no definitions, run where nixpkgs runs it (prefix `[ ]`, so the
    # tree's `prefix` reads empty), and `zz` is REPORTED at the option's path; nixpkgs gives
    # `b = 7` on the same input. Where no report is carried (a `lazyAttrsOf` element whose every
    # def is discharged) the same finding is refused, not dropped: see tests-error.
    test-a-tree-empty-value-reports-where-a-report-is-carried =
      let
        zzTree =
          (evalModuleTree {
            check = false;
            modules = [
              {
                options.b = mkOption {
                  type = t.int;
                  default = 7;
                };
                options.c = mkOption {
                  type = t.str;
                  default = "c";
                };
              }
              ({ prefix, ... }: { config.c = builtins.concatStringsSep "." prefix; })
              { config.zz = 1; }
            ];
          }).type;
        e = evalModuleTree {
          check = false;
          modules = [ { options.o = mkOption { type = zzTree; }; } ];
        };
      in
      {
        expr = {
          inherit (e.config.o) b c;
          report = map (u: u.path) e.undeclared;
        };
        expected = {
          b = 7;
          c = "";
          report = [
            [
              "o"
              "zz"
            ]
          ];
        };
      };

    # A TREE TYPE'S `verify` IS APPLIED AT EVERY SITE. The reporting site returns the `.reported`
    # value rather than the checked one, so it applies `verify` itself; a branch that returned the
    # value as is would accept at the bare and bare-empty sites what the element site refuses.
    test-a-tree-type-verify-refuses-at-every-site =
      let
        vt = mt // {
          verify = _: "verify-fired";
        };
      in
      {
        expr = {
          bare = forces (run vt { known = "v"; }).config.x;
          bareEmpty = forces (runM vt { }).config.x;
          elem = forces (run (t.attrsOf vt) { a.known = "v"; }).config.x;
        };
        expected = {
          bare = false;
          bareEmpty = false;
          elem = false;
        };
      };

    # ONE FOLD VALUE. A caller replacing the seam's `mergeDefs` replaces the fold at EVERY site,
    # the reporting one included: the report is an attribute of the fold, so it goes with it.
    test-a-replaced-seam-fold-governs-every-site = {
      expr =
        let
          w = mt // {
            mergeDefs = _loc: _defs: { wrapped = true; };
          };
        in
        {
          bare = (run w { known = "v"; }).config.x;
          elem = (run (t.attrsOf w) { a.known = "v"; }).config.x;
          report = (run w bad).undeclared;
        };
      expected = {
        bare = {
          wrapped = true;
        };
        elem = {
          a = {
            wrapped = true;
          };
        };
        report = [ ];
      };
    };
  };
}
