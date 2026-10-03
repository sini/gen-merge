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
#
# den-hoag-3jyxf's two ADMITTED-AS-nta-CHILDREN cells (`nta-extra-modules`, `nta-aspect-module`)
# relocated to gen-aspects' own `ci/` (den-hoag-n6dh7 SCC build, ADR-0037): they drove gen-schema
# and gen-aspects as CI-only VALUES here, which closed a cycle in the test graph once Unit 2
# published gen-aspects to main. gen-aspects' graph already carries gen-merge and gen-schema, so
# they keep their coverage there with no CI-only pin at all.
{
  arm,
  libSrc,
  genPreludeSrc,
  genIdentitySrc,
  genGraphSrc,
  genTypesSrc,
  genAlgebraSrc,
  genMemoSrc,
  genScopeSrc,
  # A trace label generated fresh per run by the runner, which counts its lines on stderr.
  label ? "",
  nixpkgsSrc ? null,
}:
let
  prelude = import "${genPreludeSrc}/lib";
  identity = import "${genIdentitySrc}/lib";
  algebra = import "${genAlgebraSrc}/lib";
  graph = import "${genGraphSrc}/lib" { inherit prelude; };
  m = import libSrc {
    inherit prelude;
    types = import "${genTypesSrc}/lib" { inherit algebra identity prelude; };
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
  # `<name>:<q>` read off the child `x` of an `attrsOf (submodule …)` whose second module is `extra`.
  nameAt =
    extra:
    (eval [
      {
        options.s = m.mkOption {
          type = m.types.attrsOf (
            m.types.submodule [
              (
                { name, q, ... }:
                {
                  options.a = m.mkOption {
                    type = m.types.str;
                    default = "${name}:${q}";
                  };
                }
              )
              extra
            ]
          );
        };
      }
      { s.x = { }; }
    ]).config.s.x.a;

  # THE SPY (den-hoag-n6dh7 U2-g): the same library over an evaluator whose `eval` traces `label`,
  # so the label's count on stderr is the number of independent gen-scope evaluations.
  scope = import "${genScopeSrc}/lib" { inherit graph identity prelude; };
  spied = import libSrc {
    inherit prelude;
    types = import "${genTypesSrc}/lib" { inherit algebra identity prelude; };
    memo = import "${genMemoSrc}/lib" { inherit graph prelude; };
    scope = scope // {
      # den-hoag-3jyxf: a declaration-only evaluation (no `definitions`/`positions` attribute) is
      # ALSO traced `<label>-plain`, so a census can tell a standalone side-evaluation from one that
      # threads as a proper child carrying definitions (the same distinction `u2-probe.nix`, the
      # landing gate's own fixture, already draws). Additive: the bare `label` trace every existing
      # cell's `traced()` counts still fires exactly once per call, unconditionally.
      eval =
        o: attributes: s:
        builtins.trace label (
          if attributes ? definitions || attributes ? positions then
            scope.eval o attributes s
          else
            builtins.trace "${label}-plain" (scope.eval o attributes s)
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
    types = import "${genTypesSrc}/lib" { inherit algebra identity prelude; };
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
    r: key:
    (r._evaluation.get (scope.mintNtaId {
      host = "module-tree";
      name = "nested";
      group = "[\"o\"]";
      key = key;
    }) "result").config;

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

    # THE CYCLE CLOSED THROUGH A FOREIGN RECORD'S `description` (den-hoag-type-description-parity-5k1l1):
    # the docs phrase's one argued exception. A gen container composes a foreign member's STATED
    # phrase, and when the foreign phrase is itself built from the gen type's `description` (a gen
    # cycle through a nixpkgs composer), or diverges in nixpkgs' own thunk (nixpkgs' self-referential
    # `valueType` under a gen container), the read dies in the infinite-recursion channel, as nixpkgs'
    # twin does on every arm. No construction decides it without changing an answer gen gives
    # correctly today; the README's "Known byte-mode boundaries" states the argument.
    phrase-cycle-gen-through-foreign =
      let
        np = (import "${nixpkgsSrc}/lib").types;
        vm = m.types.nullOr (np.listOf vm);
      in
      vm.description;
    phrase-cycle-foreign-under-gen =
      let
        np = (import "${nixpkgsSrc}/lib").types;
        nv = np.nullOr (
          np.oneOf [
            np.str
            (np.attrsOf nv)
            (np.listOf nv)
          ]
        );
      in
      (m.types.listOf nv).description;
    # The same exception closed through a CALLER's stated phrase: a derivation whose `fields' states
    # its base's `description' reads the phrase its own member renders, as a foreign composer does.
    phrase-cycle-stated-from-base =
      let
        d = m.types.deriveType (m.types.either m.types.int (m.types.listOf d)) {
          id = "d";
          fields = b: { inherit (b) description; };
        };
      in
      d.description;
    # Its live control: the derivation stating nothing renders its base's phrase within the budget.
    phrase-cycle-stated-from-base-control =
      let
        d = m.types.deriveType (m.types.either m.types.int (m.types.listOf d)) { id = "d"; };
      in
      builtins.substring 0 40 d.description;
    # Their live control, same wiring: the same shapes over a foreign member that holds no cycle answer.
    phrase-cycle-control =
      let
        np = (import "${nixpkgsSrc}/lib").types;
      in
      (m.types.nullOr (np.listOf m.types.int)).description
      + " | "
      + (m.types.listOf (np.nullOr np.str)).description;

    # A FOREIGN KNOT CLOSED THROUGH A GEN DOOR (den-hoag-23dqs): `r = door (F … r …)`, `F` a stock
    # foreign container and `door` `mkOptionType` or `deriveType`. The import decides at construction
    # whether the record is re-homed, a decision its key set states, by walking the elements, and the
    # walk reaches the value being constructed: the infinite-recursion channel, where nixpkgs' twin
    # constructs. No construction decides it without changing an answer gen gives today; the README's
    # "Known byte-mode boundaries" states the argument.
    foreign-knot-mkoptiontype =
      let
        np = (import "${nixpkgsSrc}/lib").types;
        r = m.mkOptionType (np.either np.int (np.listOf r));
      in
      r.check [
        1
        [ 2 ]
      ];
    foreign-knot-derivetype =
      let
        np = (import "${nixpkgsSrc}/lib").types;
        d = m.deriveType (np.either np.int (np.listOf d)) { id = "d"; };
      in
      d.check [
        1
        [ 2 ]
      ];
    # Their live control and the stated way out, same wiring: the knot closed on the foreign side and
    # carried through the door once constructs and serves nixpkgs' value.
    foreign-knot-crossed-once =
      let
        np = (import "${nixpkgsSrc}/lib").types;
        t = m.mkOptionType (
          let
            r = np.either np.int (np.listOf r);
          in
          r
        );
      in
      (eval [
        { options.s = m.mkOption { type = t; }; }
        {
          config.s = [
            1
            [ 2 ]
          ];
        }
      ]).config.s;

    # A SUBMODULE'S `name` RESOLVED AGAINST A KEY SET THAT READS IT (den-hoag-fpxsd): the position's
    # `name` is a definition beside the modules' own, so whether a module states `name` is decided
    # by the key set of their `_module.args`. A module whose key set depends on `name` closes that
    # cycle and dies in the infinite-recursion channel, as nixpkgs' `submoduleWith` does on the same
    # construction. When `name` was a `specialArgs` key outranking every definition, this was served.
    name-keyset-reads-name = nameAt (
      { name, ... }:
      {
        _module.args = if name == "x" then { q = "1"; } else { };
      }
    );
    # Its live control, same wiring: a `_module.args` VALUE read through `name` over a key set that
    # does not read it answers.
    name-keyset-control = nameAt (
      { name, ... }:
      {
        _module.args.q = name;
      }
    );
  };
in
cells.${arm}
