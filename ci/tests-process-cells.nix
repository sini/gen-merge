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
    scope = import "${genScopeSrc}/lib" {
      inherit
        algebra
        graph
        identity
        prelude
        ;
    };
  };
  opt = m.mkOption {
    type = m.types.str;
    default = "d";
  };
  on = m.mkOption {
    type = m.types.str;
    default = "on";
  };
  eval = modules: m.evalModuleTree { } modules;
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
  scope = import "${genScopeSrc}/lib" {
    inherit
      algebra
      graph
      identity
      prelude
      ;
  };
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
    (spied.evalModuleTree { } (
      [ { options.o = spied.mkOption { inherit type; }; } ] ++ map (d: { config.o = d; }) defs
    )).config.o;
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
    types = genTypesLib;
    # The published leaves, the knot `lib/default.nix` ties as `completedLeaves`.
    leaves = spied.types;
  };
  genTypesLib = import "${genTypesSrc}/lib" { inherit algebra identity prelude; };
  # The core seam's own vocabulary, tied to it as `ci/flake.nix` ties `genMergeVocab`.
  ct = import "${libSrc}/types.nix" {
    inherit prelude;
    types = genTypesLib;
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
  # den-hoag-qbrq9: `attrsOf (attrsOf sub)` with n modules each defining `o.a.k<i>`, so the inner
  # `attrsOf sub` at `o.a` is keyed over-approximately over n definitions with n distinct keys. The
  # whole value is forced; the cell answers its key count, n.
  keyWalkWide =
    n:
    let
      sub = m.types.submodule { options.x = m.mkOption { type = m.types.int; }; };
      c =
        (eval (
          [ { options.o = m.mkOption { type = m.types.attrsOf (m.types.attrsOf sub); }; } ]
          ++ builtins.genList (i: { config.o.a."k${toString i}".x = i; }) n
        )).config.o;
    in
    builtins.deepSeq c (builtins.length (builtins.attrNames c.a));
  # den-hoag-hnd82: n options, each declared twice so that its type is a MET record (one per option), and
  # each defined; the served values are forced. `mode` picks the met record's producer: `val`, meetOf's
  # record over a foreign `addCheck`; `box`, a `listOf` over it; `s2`, meetOf's foreign-`verify` record;
  # `s3`, metWith's held record. The runner reads the process's thunks at n = 100 and 200.
  # A chain of `d` gen `listOf` over a submodule, its module set read off the outer type: the spine walks the chain,
  # and each gen container on it answers its own `getSubModules` once the rest of the chain is shown to bottom out
  # (den-hoag-y4w78), so the walk is quadratic in the depth (`tests-process.nix` holds the bound).
  spineCost =
    d:
    let
      sub = m.types.submodule { options.a = m.mkOption { type = m.types.int; }; };
      nest = k: if k == 0 then sub else m.types.listOf (nest (k - 1));
    in
    builtins.length (nest d).getSubModules;
  graphCost =
    removal: n:
    let
      decl.options.x = m.mkOption {
        type = m.types.listOf m.types.str;
        default = [ ];
      };
      mods = [
        decl
      ]
      ++ builtins.genList (i: { x = [ "m${toString i}" ]; }) n
      ++ [ (if removal then { disabledModules = [ { key = ":anon-2"; } ]; } else { }) ];
    in
    builtins.length (builtins.filter (g: g.disabled) (m.evalModuleTree { } mods).graph);
  # One option defined through a stock nixpkgs rename, whose alias leaf runs the staged declaration
  # passes, or defined directly, which runs none.
  stagedCost =
    renamed:
    let
      nl = import "${nixpkgsSrc}/lib";
    in
    (eval (
      [ { options.new = m.mkOption { type = m.types.int; }; } ]
      ++ (
        if renamed then
          [
            (nl.mkRenamedOptionModule [ "old" ] [ "new" ])
            { old = 3; }
          ]
        else
          [ { new = 3; } ]
      )
    )).config.new;
  metCost =
    mode: n:
    let
      nl = import "${nixpkgsSrc}/lib";
      np = nl.types;
      t = m.types;
      even = v: builtins.bitAnd v 1 == 0;
      attrsInt = np.attrsOf np.int;
      evenFold = m.mkOptionType (
        let
          self = nl.mkOptionType {
            name = "evenFold";
            check = {
              __functor = _: builtins.isInt;
              isV2MergeCoherent = true;
            };
            merge =
              loc: defs:
              let
                v = nl.mergeEqualOption loc defs;
              in
              if even v then v else throw "odd";
            functor = np.defaultFunctor "evenFold" // {
              type = _: self;
              payload = { };
              binOp = _a: _b: { };
            };
            typeMerge = f: if f.name == "int" || f.name == "evenFold" then np.int else null;
          };
        in
        self
      );
      decl = {
        val = [
          (np.addCheck t.int even)
          t.int
        ];
        box = [
          (t.listOf (np.addCheck t.int even))
          (t.listOf t.int)
        ];
        s2 = [
          (
            attrsInt
            // {
              verify = v: if builtins.all (x: x < 10) (builtins.attrValues v) then null else "rejected";
            }
          )
          attrsInt
        ];
        s3 = [
          evenFold
          t.int
        ];
      };
      v =
        {
          val = 2;
          box = [ 2 ];
          s2.a = 2;
          s3 = 2;
        }
        .${mode};
      names = builtins.genList (i: "o${toString i}") n;
      e = eval (
        map (ty: {
          options = builtins.listToAttrs (
            map (k: {
              name = k;
              value = m.mkOption { type = ty; };
            }) names
          );
        }) decl.${mode}
        ++ [
          {
            config = builtins.listToAttrs (
              map (k: {
                name = k;
                value = v;
              }) names
            );
          }
        ]
      );
      vals = map (k: e.config.${k}) names;
    in
    builtins.deepSeq vals (builtins.length vals);
  childResult =
    r: key:
    (r._evaluation.get (scope.mintNtaId {
      host = "module-tree";
      name = "nested";
      group = "[\"o\"]";
      key = key;
    }) "result").config;

  # a module reading `f` of its arguments, deep-forced inside the evaluation, on the module system `M`
  # (gen-merge or nixpkgs' lib), read back as the option `r`
  mtEval =
    M: modules:
    if M ? evalModuleTree then M.evalModuleTree { } modules else M.evalModules { inherit modules; };
  mtRegress =
    M: f:
    (mtEval M [
      { options.a = M.mkOption { default = 1; }; }
      (
        { config, moduleType, ... }@a:
        {
          options.r = M.mkOption { default = (builtins.tryEval (builtins.deepSeq (f a) true)).success; };
        }
      )
    ]).config.r;
  mtDepth =
    M:
    let
      emptyOf = t: if M ? evalModuleTree then t.whenEmpty.value else t.emptyValue.value;
    in
    (mtEval M [
      (
        { moduleType, ... }:
        {
          options.d = M.mkOption {
            default =
              let
                r = builtins.tryEval (emptyOf moduleType).d;
              in
              if r.success then r.value + 1 else 0;
          };
        }
      )
    ]).config.d;

  cells = {
    # U2-g: ONE evaluation, however many nested trees the value holds (each reads 1).
    one-eval-flat =
      (spied.evalModuleTree { } [
        {
          options.a = spied.mkOption { type = st.int; };
          config.a = 1;
        }
      ]).config.a;
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
    # den-hoag-olrmz G3: ONE `verify` copy of a nesting container, declared twice, threads as one
    # evaluation. Merging the two declarations compares them without their phrase, which for a nesting
    # type reads its own module set's declarations, so a declaration-only side evaluation costs nothing.
    one-eval-verify-shared =
      let
        T = spied.mkOptionType (st.nullOr sub // { verify = _: null; });
      in
      (spied.evalModuleTree { } [
        { options.o = spied.mkOption { type = T; }; }
        { options.o = spied.mkOption { type = T; }; }
        { config.o.x = 1; }
        { config.o = { }; }
      ]).config.o.x;
    # The spy's live control: two root evaluations read 2.
    one-eval-control-two-roots = (spiedAt sub [ { x = 1; } ]).x + (spiedAt sub [ { x = 2; } ]).x;
    # den-hoag-8qenh (c′): an evaluation's own type's empty value is that evaluation's on-demand
    # `type` child, so reading it is still ONE evaluation; the bridge's root would be a second.
    one-eval-own-type =
      (spied.evalModuleTree { } [
        {
          options.a = spied.mkOption {
            type = st.int;
            default = 1;
          };
        }
      ]).type.whenEmpty.value.a;
    # den-hoag-8qenh C17, den-hoag-d2o0g: a module that deep-forces its own `moduleType` regresses
    # without end, since that type's empty value holds the module again, one level deeper, as
    # nixpkgs' each `base` does. It dies on the call-depth channel on both engines, and is never
    # cut short with a value (ADR-0033: divergence is inherited, never added).
    mt-regress-formal = mtRegress m (a: a.moduleType);
    mt-regress-formal-nixpkgs = mtRegress (import "${nixpkgsSrc}/lib") (a: a.moduleType);
    mt-regress-args = mtRegress m (a: a.config._module.args.moduleType);
    mt-regress-args-nixpkgs = mtRegress (import "${nixpkgsSrc}/lib") (
      a: a.config._module.args.moduleType
    );
    # an option whose default is one more than itself in its own moduleType's empty value: no depth
    # at which the regress is cut, so no value
    mt-regress-depth = mtDepth m;
    mt-regress-depth-nixpkgs = mtDepth (import "${nixpkgsSrc}/lib");
    # U2-l (gate O1): a candidate's `result` refuses before its member's modules are applied, so the
    # traced module is applied 0 times. The evaluation holds no SELECTED child of that member.
    candidate-modules =
      (builtins.tryEval (childResult (lazyUnionAt [ { foo = "s"; } ]) "[\"foo\"]")).success;
    # Its live control, a separate evaluation: the same member in a selected child applies it.
    candidate-modules-control = (childResult (lazyUnionAt [ { bar.x = 1; } ]) "[\"bar\"]").x;
    # den-hoag-qbrq9: one over-approximately keyed position collecting n definitions, each with its
    # own key. The runner reads its function calls at n = 100, 400, 1600.
    key-walk-wide-100 = keyWalkWide 100;
    key-walk-wide-400 = keyWalkWide 400;
    key-walk-wide-1600 = keyWalkWide 1600;
    # den-hoag-hnd82: a met record's cost, read by the runner as thunks per option.
    met-cost-val-100 = metCost "val" 100;
    met-cost-val-200 = metCost "val" 200;
    met-cost-box-100 = metCost "box" 100;
    met-cost-box-200 = metCost "box" 200;
    met-cost-s2-100 = metCost "s2" 100;
    met-cost-s2-200 = metCost "s2" 200;
    met-cost-s3-100 = metCost "s3" 100;
    met-cost-s3-200 = metCost "s3" 200;
    # den-hoag-8tmd5: the staged declaration passes' cost, read by the runner as the thunks the rename
    # adds over the direct definition.
    staged-cost-plain = stagedCost false;
    staged-cost-rename = stagedCost true;
    # den-hoag-y4w78: the spine's cost on a chain of `listOf` over a submodule, read by the runner as thunks between
    # depth 1 and 30.
    spine-cost-1 = spineCost 1;
    spine-cost-30 = spineCost 30;
    # den-hoag-7o7i9: a module graph read over n anonymous modules, every node's `disabled` forced,
    # read by the runner as thunks per module: with no removal the key set is bound once per read, so
    # a node costs what it did before removal existed; with one, the marking is one walk.
    graph-cost-100 = graphCost false 100;
    graph-cost-400 = graphCost false 400;
    graph-cost-removal-100 = graphCost true 100;
    graph-cost-removal-400 = graphCost true 400;
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

    # nixpkgs' RENAMED-OPTION FAMILY under the guard's staged passes (den-hoag-9oc7y). A rename cycle
    # forced uncontained refuses on the guard's named channel: containment alone cannot tell a by-name
    # refusal from a cycle the passes certified. Its two neighbours are the stated prices, uncatchable
    # on purpose: a declaration reading a field its target does not carry dies as nixpkgs dies once
    # the view is real, and a module that catches a stamped-view refusal takes a leaf's shape at the
    # pass and a group's on the value side, where it reaches Nix's recursion abort (ADR-0008 §3).
    rename-cycle-read =
      let
        np = import "${nixpkgsSrc}/lib";
      in
      (eval [
        { options.a = np.mkOption { type = np.types.int; }; }
        (np.mkAliasOptionModule [ "b" ] [ "c" ])
        (np.mkAliasOptionModule [ "c" ] [ "b" ])
        { a = 1; }
      ]).config.a;
    leaf-reads-absent-field =
      let
        np = import "${nixpkgsSrc}/lib";
      in
      (eval [
        { options.a = np.mkOption { type = np.types.int; }; }
        (
          { options, ... }:
          {
            options.b =
              np.mkOption {
                type = np.types.int;
                default = 1;
              }
              // np.optionalAttrs (options.a.example == 0) { };
          }
        )
        { a = 1; }
      ]).config.b;
    catch-group =
      let
        np = import "${nixpkgsSrc}/lib";
      in
      (eval [
        { options.a = np.mkOption { type = np.types.int; }; }
        (
          { options, ... }:
          {
            options.b =
              if (builtins.tryEval options.a.isDefined).success then
                {
                  x = np.mkOption {
                    type = np.types.int;
                    default = 3;
                  };
                }
              else
                np.mkOption {
                  type = np.types.int;
                  default = 4;
                }
                // np.optionalAttrs (options.a.type != null) { };
          }
        )
        { a = 1; }
      ]).config.b;

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
        d = m.types.deriveType { fields = b: { inherit (b) description; }; } "d" (
          m.types.either m.types.int (m.types.listOf d)
        );
      in
      d.description;
    # Its live control: the derivation stating nothing renders its base's phrase within the budget.
    phrase-cycle-stated-from-base-control =
      let
        d = m.types.deriveType { } "d" (m.types.either m.types.int (m.types.listOf d));
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
        d = m.deriveType { } "d" (np.either np.int (np.listOf d));
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

    # A TYPE THAT IS ITS OWN DERIVATION (den-hoag-iaram): `d = deriveType d { … }` states no
    # constructor between `d` and itself, so it denotes no type, and `deriveType` reading its base
    # at construction reads `d` while `d` is being built. Nix black-holes the thunk before any gen
    # code observes a value: the infinite-recursion channel, as nixpkgs' `d = d // { … }` does. The
    # README's "Known byte-mode boundaries" states the argument.
    cyclic-derive-self =
      let
        d = m.types.deriveType { } "d" d;
      in
      builtins.seq d true;
    # AN UNGUARDED (NON-CONTRACTIVE) CYCLE (den-hoag-iaram): `r = either int r` passes no
    # constructor that consumes the value, so `check` of a value outside `int` asks `r` the same
    # question again, without end: the call-depth channel, as nixpkgs' twin does.
    cyclic-unguarded =
      let
        r = m.types.either m.types.int r;
      in
      r.check "s";
    # Their live control, same wiring: a cycle closed through a container, inside a derivation, checks
    # a value in its domain and refuses one outside it.
    cyclic-guarded-control =
      let
        d = m.types.deriveType { } "d" (m.types.either m.types.int (m.types.listOf d));
      in
      [
        (d.check [
          1
          [ 2 ]
        ])
        (d.check "s")
      ];
  };
in
cells.${arm}
