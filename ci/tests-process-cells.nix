# THE PER-PROCESS CELLS — fixtures whose verdict is a PROCESS EXIT, one fixture per process.
#
# WHY THESE CANNOT BE SUITE CELLS. The subject cell observes `infinite recursion encountered`,
# which aborts the evaluator: `tryEval` does not catch it, so there is no message a suite cell
# could read and no boolean it could return. The assertion IS the exit status and the channel it
# died on, read by the runner in `tests-process.nix`, which evaluates each arm in its OWN process.
#
# Wiring: each dependency through its own `lib/` entry with explicit arguments, the way
# `../lib/default.nix`'s formals name them. Sources arrive as ARGUMENTS rather than through
# `fetchTree` because the runner evaluates inside the build sandbox, where fetching is impossible.
{
  arm,
  libSrc,
  genPreludeSrc,
  genIdentitySrc,
  genGraphSrc,
  genTypesSrc,
  genMemoSrc,
  genScopeSrc,
  # A trace label generated fresh per run by the runner, which counts its lines on stderr.
  label ? "",
  nixpkgsSrc ? null,
  # den-hoag-3jyxf: gen-schema/gen-aspects/gen-algebra as CI-only VALUES (never a `lib/` dep — same
  # precedent as `nixpkgsSrc` above), so the two ADMITTED-AS-nta-CHILDREN constructions can be driven
  # through this file's own spy without those consumers growing their own spy wiring.
  genSchemaSrc ? null,
  genAspectsSrc ? null,
  genAlgebraSrc ? null,
}:
let
  prelude = import "${genPreludeSrc}/lib";
  identity = import "${genIdentitySrc}/lib";
  graph = import "${genGraphSrc}/lib" { inherit prelude; };
  m = import libSrc {
    inherit prelude;
    types = import "${genTypesSrc}/lib" { inherit identity prelude; };
    memo = import "${genMemoSrc}/lib" { inherit graph prelude; };
    scope = import "${genScopeSrc}/lib" { inherit graph identity prelude; };
  };
  opt = m.mkOption {
    type = m.types.str;
    default = "d";
  };
  on = m.mkOption {
    type = m.types.str;
    default = "on";
  };
  eval = modules: m.evalModuleTree { inherit modules; };

  # THE SPY (den-hoag-n6dh7 U2-g): the same library over an evaluator whose `eval` traces `label`,
  # so the label's count on stderr is the number of independent gen-scope evaluations.
  scope = import "${genScopeSrc}/lib" { inherit graph identity prelude; };
  spied = import libSrc {
    inherit prelude;
    types = import "${genTypesSrc}/lib" { inherit identity prelude; };
    memo = import "${genMemoSrc}/lib" { inherit graph prelude; };
    scope = scope // {
      # den-hoag-3jyxf: a declaration-only evaluation (no `definitions`/`positions` attribute) is
      # ALSO traced `<label>-plain`, so a census can tell a standalone side-evaluation from one that
      # threads as a proper child carrying definitions (the same distinction `u2-probe.nix`, the
      # landing gate's own fixture, already draws). Additive: the bare `label` trace every existing
      # cell's `traced()` counts still fires exactly once per call, unconditionally.
      eval =
        a:
        builtins.trace label (
          if a.attributes ? definitions || a.attributes ? positions then
            scope.eval a
          else
            builtins.trace "${label}-plain" (scope.eval a)
        );
    };
  };
  st = spied.types;
  sub = st.submodule { options.x = spied.mkOption { type = st.int; }; };
  spiedAt =
    type: defs:
    (spied.evalModuleTree {
      modules = [ { options.o = spied.mkOption { inherit type; }; } ] ++ map (d: { config.o = d; }) defs;
    }).config.o;
  # U2-l: a module that traces `label` each time it is APPLIED, in a member's shared module set.
  tracedSub = st.submodule (
    _:
    builtins.trace label {
      options.x = spied.mkOption { type = st.int; };
    }
  );
  spiedCore = import "${libSrc}/modules.nix" {
    inherit prelude;
    priority = import "${libSrc}/priority.nix" { inherit prelude; };
    memo = import "${genMemoSrc}/lib" { inherit graph prelude; };
    inherit scope;
    strategies = ct;
  };
  # The core seam's own vocabulary, tied to it as `ci/flake.nix` ties `genMergeVocab`.
  ct = import "${libSrc}/types.nix" {
    inherit prelude;
    core = spiedCore;
  };
  lazyUnionAt =
    defs:
    spiedCore.evalModuleTreeExposed {
      modules = [
        { options.o = spied.mkOption { type = ct.lazyAttrsOf (ct.either tracedSub st.str); }; }
      ]
      ++ map (d: { config.o = d; }) defs;
    };
  childResult =
    r: key: (r._evaluation.get (scope.mintNtaId "module-tree" "nested" "[\"o\"]" key) "result").config;

  # den-hoag-3jyxf: the two same-mechanism constructions the 09-15 relocation ruling excluded and
  # the 09-25 sitting admitted AS nta CHILDREN (an outer-tree `config` read flowing into an inner
  # submodule's `imports`). Built over `spied` so every scope.eval any of the three libraries makes
  # counts, and its `evalModuleTree` wrapped a second time so an explicit ROOT call also traces
  # `<label>-door` (U2-h's door count) — the bridge price is `evals - doors`.
  algebra = import "${genAlgebraSrc}/lib";
  spiedDoored = spied // {
    evalModuleTree = a: builtins.trace "${label}-door" (spied.evalModuleTree a);
  };
  gs = import "${genSchemaSrc}/lib" {
    inherit
      prelude
      algebra
      identity
      graph
      ;
    merge = spiedDoored;
  };
  ga = import "${genAspectsSrc}/lib" {
    inherit prelude identity;
    merge = spiedDoored;
    schema = gs;
  };

  cells = {
    # U2-g: ONE evaluation, however many nested trees the value holds (each reads 1).
    one-eval-flat =
      (spied.evalModuleTree {
        modules = [
          {
            options.a = spied.mkOption { type = st.int; };
            config.a = 1;
          }
        ];
      }).config.a;
    one-eval-sub-one = spiedAt sub [ { x = 2; } ];
    one-eval-attrs-two = spiedAt (st.attrsOf sub) [
      {
        a.x = 1;
        b.x = 2;
      }
    ];
    one-eval-list-two = spiedAt (st.listOf sub) [
      [
        { x = 1; }
        { x = 2; }
      ]
    ];
    one-eval-sub-empty = spiedAt (st.submodule {
      options.x = spied.mkOption {
        type = st.int;
        default = 0;
      };
    }) [ ];
    one-eval-deep =
      spiedAt (st.attrsOf (st.submodule { options.i = spied.mkOption { type = st.attrsOf sub; }; }))
        [
          { a.i.b.x = 5; }
        ];
    # U2-i: a stock nixpkgs `attrsOf` over a gen tree is re-homed where it is bound, so its elements
    # are children of the one evaluation too.
    one-eval-np-attrs = spiedAt ((import "${nixpkgsSrc}/lib").types.attrsOf sub) [
      {
        a.x = 1;
        b.x = 2;
      }
    ];
    # The spy's live control: two root evaluations read 2.
    one-eval-control-two-roots = (spiedAt sub [ { x = 1; } ]).x + (spiedAt sub [ { x = 2; } ]).x;
    # U2-l (gate O1): a candidate's `result` refuses before its member's modules are applied, so the
    # traced module is applied 0 times. The evaluation holds no SELECTED child of that member.
    candidate-modules =
      (builtins.tryEval (childResult (lazyUnionAt [ { foo = "s"; } ]) "[\"foo\"]")).success;
    # Its live control, a separate evaluation: the same member in a selected child applies it.
    candidate-modules-control = (childResult (lazyUnionAt [ { bar.x = 1; } ]) "[\"bar\"]").x;
    # THE OUTER FIXPOINT (den-hoag-xzchx, C3). A PLAIN attrset — no formals, no `imports`, no
    # `__functor` — whose option KEY SET under `a` reads the evaluation's own `options` through
    # the lexical binding `r`. That is ADR-0033's in-flight clause read literally, reached through
    # a channel the guard's by-name refusal cannot see: the module is never applied, so no
    # poisoned argument is ever demanded. What the guard still guarantees is that NO VALUE is
    # produced — forcing the declaration spine closes the cycle and the evaluator dies. An
    # admission that skips the guard for a module with no formals answers `{ a.b = "d"; y = "on"; }`
    # here instead: "takes no arguments" is not "closed term", since a thunk's free variables are
    # invisible to any predicate over the module's shape.
    outer-options-read =
      let
        r = eval [
          {
            options.y = on;
            options.a = if r.options ? y then { b = opt; } else { };
          }
        ];
      in
      r.config;

    # The SAME clause in the in-module form: the guard is live in this library and refuses it BY
    # NAME. The positive twin of the death above, on the same runner and the same wiring.
    in-module-options-read =
      (eval [
        (
          { options, ... }:
          {
            options.y = on;
            options.a = if options ? y then { b = opt; } else { };
          }
        )
      ]).config;

    # The same outer fixpoint read at a stratum-2 position ADR-0033 admits — an option DEFAULT —
    # ANSWERS: the wiring evaluates, and the death above is the cycle, not the fixture.
    outer-default-read =
      let
        r = eval [
          {
            options.y = on;
            options.x = m.mkOption {
              type = m.types.str;
              default = r.config.y;
            };
          }
        ];
      in
      r.config.x;

    # den-hoag-3jyxf cell 1: a config-decided extraModules list (gen-schema mkInstanceRegistry) —
    # ADMITTED AS an nta CHILD. `evals - doors` is the ruled bridge price (U2-h, one bridge at
    # `schema`); `plain` is 0 when the construction threads as a proper child rather than firing a
    # standalone declaration-only evaluation.
    nta-extra-modules =
      let
        ntaSchema = gs.evalSchema {
          modules = [ { config.schema.host.options.addr = spiedDoored.mkOption { type = st.str; }; } ];
        };
        run =
          knob:
          (spiedDoored.evalModuleTree {
            modules = [
              (
                { config, ... }:
                {
                  options.knob = spiedDoored.mkOption {
                    type = st.bool;
                    default = false;
                  };
                  options.hosts = gs.mkInstanceRegistry ntaSchema.host {
                    extraModules =
                      if config.knob then
                        [
                          {
                            options.tag = spiedDoored.mkOption {
                              type = st.str;
                              default = "on";
                            };
                          }
                        ]
                      else
                        [
                          {
                            options.tag = spiedDoored.mkOption {
                              type = st.str;
                              default = "off";
                            };
                          }
                        ];
                  };
                  config.knob = knob;
                  config.hosts.igloo.addr = "10.0.1.1";
                }
              )
            ];
          }).config.hosts.igloo.tag;
      in
      [
        (run true)
        (run false)
      ];

    # den-hoag-3jyxf cell 2: gen-aspects mkAspectModule (the inner type computed from
    # `config.schema.aspect.__defsModule`) — ADMITTED AS an nta CHILD, same shape as cell 1.
    nta-aspect-module =
      let
        ntaSchema = ga.mkAspectSchema {
          keySemantics = {
            classOne.category = "class";
          };
        };
        c = spiedDoored.evalModuleTree {
          modules = [
            { options.schema = ntaSchema.schemaOption; }
            (ntaSchema.mkAspectModule { })
            {
              config.schema.aspect.options.priority = spiedDoored.mkOption {
                type = st.int;
                default = 50;
              };
            }
            {
              config.aspects.networking.priority = 10;
              config.aspects.desktop = { };
            }
          ];
        };
      in
      [
        c.config.aspects.networking.priority
        c.config.aspects.desktop.priority
      ];
  };
in
cells.${arm}
