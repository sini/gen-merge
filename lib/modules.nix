# Core byte-mode merge engine — `evalModuleTree` + the shared `mergeDefs` fold.
#
# Design spec §1 (the 7-item primitive) + §2 (API). Reproduces `lib.evalModules` merge OUTPUT for
# den's surface with none of `lib.types`: collect+flatten imports, tie the self-referential `config`
# fixpoint (spec §1 item 4 — on the INJECTED evaluator, see `driveKnot`), collect per-option defs, priority-resolve
# (spec §1 priority subset, via ./priority.nix), dispatch structural types to their `.merge`
# strategy, route unknown keys through the freeformType, and check leaves via the injected gen-types
# `verify`. Class layering: gen-prelude → gen-types → gen-merge (this) → {gen-schema, gen-aspects}.
#
# ★★★ THE FOREIGN PROTOCOL IS REACHED THROUGH ONE UNIT AND NEVER SPELLED HERE. This engine runs types
# it did not build — a consumer may inject a foreign leaf vocabulary wholesale, and a gen type mounted
# in a foreign module system can face a foreign partner declared for the same option — so every
# question it asks a type it asks GEN-FIRST, then, for a type that answers in the other vocabulary,
# through `lib/interface.nix`'s import environment. The arm ORDER is the substance: the engine
# dispatches on gen's own record, and the foreign protocol is the foreign arm rather than the basis.
# A type carrying no foreign field is a first-class operand here, which is the whole point.
#
# `memo` (gen-memo.lib, REQUIRED — ADR-0008 item 2): the incremental plane's reuse DECISION.
# `warmDecide` below builds the bipartite contribution-relation FACT (module entries ↔
# declared-leaf locations) and hands it to `memo.warmDecision`, which answers `isClean`. This
# engine no longer decides reuse from its own footprint SET — it computes the relation and asks.
#
# `scope` (gen-scope.lib, REQUIRED — ADR-0006, ADR-0008 §1): the ONE universal graph evaluator.
# This engine declares no fixpoint driver of its own; the module tree is one node on that evaluator
# and `driveKnot` below is the whole of the seam. It is bound at the LIBRARY's construction
# (`lib/default.nix`), which is what puts it in lexical scope for `lib/types.nix`'s nested
# structural folds — see that file's header for why a per-call formal cannot reach them.
{
  prelude,
  priority,
  memo,
  scope,
  # The type vocabulary built OVER this engine (`lib/types.nix`'s result), for the one question
  # that needs gen's own constructors here: re-homing a recognised foreign container as the gen
  # container it is (den-hoag-n6dh7 item 5). A KNOT, tied lazily by every caller (`lib/default.nix`,
  # `ci/flake.nix`): nothing reads it while the vocabulary is still being built.
  strategies,
  # gen-types' library (the roster's `types`), for the one thing this engine takes from it: the
  # check-witness protocol gen-types owns, which the boundary builds every export through and reads
  # every fold's witness by (den-hoag-ydro3). `lib/default.nix` has refused a `types` without it,
  # and one whose protocol disagrees with this engine's inline test, before this is imported.
  types,
  # The published, protocol-complete leaves (`lib/default.nix` `completedLeaves`), for the type the
  # engine's own `_module.check` record states: nixpkgs' docs walker reads `getSubOptions` off it,
  # which the raw gen-types leaf lacks. A KNOT, tied as `strategies` is.
  leaves,
}:
let
  inherit (prelude)
    isAttrs
    isList
    concatMap
    concatLists
    foldl'
    filter
    map
    mapAttrs
    attrNames
    listToAttrs
    concatStringsSep
    optional
    length
    head
    tail
    setAttrByPath
    getAttrByPath
    all
    any
    ;
  # The two readers are the BUILTINS, stated rather than taken from gen-prelude. Module application,
  # in `callM` and `callD`, reads nixpkgs' functor-aware predicate (`lib.isFunction` and
  # `lib.functionArgs`, gen-prelude's readers) INLINE behind the builtin test, so a functor module is
  # applied by its `__functionArgs` (den-hoag-genmerge-functor-module-application-u6lf8). The
  # builtins stay bound here for that inline fast path and `isModuleValue`; every definition-value
  # site reads `prelude.isFunction` by name (den-hoag-1ypox). Inline rather than the prelude
  # readers by name because `prelude.isFunction` is a lambda: binding it allocates an env on every
  # module application,
  # lambda and attrset modules included (+921,600 B on the hub's deepSubmodule n=1600, ratio 0.501
  # against the 0.500 bound), where the inline test costs those arms nothing.
  inherit (builtins) isFunction functionArgs;
  inherit (priority)
    dischargeProperties
    dischargePropertiesAt
    filterOverrides
    filterOverridesRich
    sortProperties
    isOrderMarker
    pushDownProperties
    mkOptionDefault
    defaultPriority
    ;

  # nixpkgs' `lib.strings.escapeNixIdentifier`: a name that is not a Nix identifier, or is a keyword,
  # prints as a string literal (`$` escaped as `escapeNixString` does). The one home of the keyword
  # list, read by `showOption` and by the undeclared-option refusal's value print.
  escapeIdentifier =
    let
      keywords = [
        "assert"
        "else"
        "if"
        "in"
        "inherit"
        "let"
        "or"
        "rec"
        "then"
        "with"
      ];
    in
    s:
    if builtins.match "[a-zA-Z_][a-zA-Z0-9_'-]*" s != null && !(builtins.elem s keywords) then
      s
    else
      builtins.replaceStrings [ "$" ] [ "\\$" ] (builtins.toJSON s);

  # nixpkgs' `lib.options.showOption`: each segment through `escapeIdentifier`, so `a."b.c"` and
  # `a.b.c` stay two paths; the placeholders `*` and `<...>` print bare.
  showOption =
    let
      showPart =
        part: if part == "*" || builtins.match "<(.*)>" part != null then part else escapeIdentifier part;
    in
    loc: concatStringsSep "." (map showPart loc);

  # The conflict refusal, ONE text for both leaf folds (`mergeLeaf` below and the boundary's
  # `leafFold`), so the engine and what it publishes outward cannot drift apart. ADR-0025 item 1:
  # a refusal names what a reader acts on, and for a conflict that is every contributing
  # definition's FILE, listed with its value where a scalar prints — the information nixpkgs'
  # `mergeEqualOption` lists. It is built only on the refusal path, where the fold's agreement test
  # has already forced every value to WHNF, and it renders through gen-prelude's shared `renderValue`.
  #
  # A LIST is named by its type here and never handed to the shared renderer, whose string-list arm
  # forces every element. The agreement test does not force them — list `==` decides unequal lengths
  # before it reads an element — so an element that aborts at WHNF (`({ }).nope`, a missing config
  # attribute) would first be forced INSIDE the refusal, turning this catchable, named refusal into
  # an uncatchable abort (ADR-0025 item 1). Forcing no element keeps the refusal total on every list.
  #
  # `showDefLine` is the "- In `file'" line, shared with the undeclared-option refusal (`_orphanCheck`,
  # `lib/undeclared-text.nix`), which names ONE definition as nixpkgs' `showDefs [ firstDef ]` does and
  # renders its value as nixpkgs' `showDefs` does, not through `showValue`.
  showValue = v: if builtins.isList v then "<a list>" else prelude.renderValue v;
  showDefLine = d: rest: "\n- In `${toString (d.file or "<unknown-file>")}'${rest}";
  showDefs = defs: concatStringsSep "" (map (d: showDefLine d ": ${showValue d.value}") defs);
  showConflict =
    loc: defs: "gen-merge: the option `${showOption loc}' has conflicting definitions:" + showDefs defs;

  # The definition the undeclared-option refusal names: nixpkgs takes `head merged.unmatchedDefns`
  # (modules.nix), which is NAME-SORTED per level across a level's own undeclared keys and its
  # declared groups. `unmatched` lists own keys first, then groups, so the head is the first of the
  # smallest path (componentwise), the earlier entry winning a tie — which keeps nixpkgs' choice
  # among several definitions of one name.
  firstUnmatched =
    unmatched:
    foldl' (best: d: if d.path < best.path then d else best) (head unmatched) (tail unmatched);

  # The protocol boundary (lib/interface.nix). Imported HERE, and re-exported on the core seam, so the
  # dependency graph stays a chain — prelude → interface → this engine → the type vocabulary — rather
  # than a knot: the boundary needs only the prelude, this file's loc and conflict renderers, and the
  # constructor's default fold (`mergeDescriptorDefault`, below), and both of its consumers reach it
  # through the same binding, so their views of the foreign protocol cannot drift apart.
  #
  # ★ Two arguments close a loop back over this engine, both for the nested-tree crossing
  # (den-hoag-n6dh7 items 5, 7) and both read lazily: gen's own containers, which re-homing rebuilds
  # a recognised foreign container as, and the nested tree's door, through which the export bridge
  # evaluates a nesting type's tree.
  interface = import ./interface.nix {
    inherit
      prelude
      showOption
      showConflict
      mergeDescriptorDefault
      nestedTreeAt
      types
      mergeDefsThreaded
      ;
    constructors = strategies;
  };

  reverse =
    xs:
    let
      n = length xs;
    in
    prelude.genList (i: prelude.elemAt xs (n - 1 - i)) n;

  # Vendored module-convention helper (audit §4 — a ~2-line pure attrset constructor, NOT the
  # `lib.types` machinery): tag a module with its definition site for error provenance.
  setDefaultModuleLocation = file: m: {
    _file = file;
    imports = [ m ];
  };

  # A nesting type's DEFINITIONS, as the modules its nested evaluation reads: the reference's
  # `submoduleWith` `allModules`, flag for flag. With `shorthandOnlyDefinesConfig` an attrset def is
  # CONFIG (`types.submodule`); otherwise, and for every function or path def, the def is a MODULE
  # (`(evalModules …).type`, `submoduleWith`'s default).
  defsAsModules =
    shorthandOnlyDefinesConfig: defs:
    map (
      d:
      if shorthandOnlyDefinesConfig && isAttrs d.value then
        {
          _file = toString (d.file or "<def>");
          config = d.value;
        }
      else
        setDefaultModuleLocation (toString (d.file or "<def>")) d.value
    ) defs;

  # A STRING naming an absolute path is a module the way a path literal is: the reference's
  # `loadModule` `import`s whatever is not a function or an attrset, so `"${inputs.x}/m.nix"` and
  # `"${modulesPath}/…"` load. Tested after the attrset arm, so a clean module never pays for it.
  isPathString = m: builtins.isString m && builtins.substring 0 1 m == "/";

  # The module-value domain, shared by every type whose definitions ARE modules (`submodule`,
  # `deferredModule`, and the tree's own `type` below) so they cannot drift into answering it
  # differently. The engine's `callM` applies a path, a string naming an absolute path, a function,
  # a `__functor` attrset or a plain attrset, and nothing else; the string test is the loader's own
  # `isPathString`, so this domain is nixpkgs `pathWith { absolute = true; }` beside attrsets and
  # functions, context irrelevant. It lives here rather than in `./types.nix` because the tree reads
  # it too, and this file is below that one.
  isModuleValue = v: isAttrs v || isFunction v || builtins.isPath v || isPathString v;

  # A STRUCTURAL FOLD IS TOTAL OVER ITS INPUT: a definition outside the type's stated domain is
  # refused catchably, naming the option, the type and the files, BEFORE the fold runs — otherwise
  # it reaches `imap0`/`//`/`?` and the interpreter aborts with a raw type error naming neither, or
  # (`deferredModule`) is accepted here and fails wherever it is imported. The engine's post-fold
  # check reads `verify`, never `admits`, so each structural constructor applies this to its own
  # fold, passing the SAME binding it states as `admits`; its domain check therefore cannot disagree
  # with the `check` it exports. It tests the surviving definitions (after discharge, priority and
  # order), where nixpkgs' `checkedAndMerged` tests `defsFinal`, and forces each only to WHNF, which
  # the engine's discharge has already done. The refusal list is built only on refusal. The
  # quantifier is spelled inline rather than read from `admitsAll`: this door sits on every
  # structural fold, the submodule fold among them, and the call through the binding is a measured
  # allocation on the hub perf-bench's ratcheted `deepSubmodule` row (den-hoag-mda6f). The
  # submodule's threaded fold spells the quantifier the same way and reaches this binding only to
  # refuse (`fold` is then never read), so its text is this throw's (den-hoag-c7jkw.1).
  refusingOutside =
    tyName: inDomain: fold: loc: defs:
    if all (d: inDomain d.value) defs then
      fold loc defs
    else
      throw "gen-merge: option `${showOption loc}' has definitions `${tyName}' cannot consume (${
        concatStringsSep ", " (map (d: toString (d.file or "<def>")) (filter (d: !(inDomain d.value)) defs))
      })";

  # The door's quantifier as the key walk's over-approximated arm (`keyWalk`) reads it: it keys a
  # position only where the door above would let its fold run. The door spells the same quantifier
  # inline, so the two are two spellings of one predicate, and `nesting-threaded-native-keyed-on-read`'s
  # agreement cell pins that they give one verdict over every structural container's domain.
  admitsAll = inDomain: defs: all (d: inDomain d.value) defs;

  # The refusal of a value that is none of those shapes, one binding for every reader that loads a
  # module: the config and declaration strata's `callM`/`callD`, and the lint's `collect`.
  notAModule =
    m:
    throw "gen-merge: a module must be a path, a function or an attribute set, and this one is ${builtins.typeOf m} (an `imports' element, or a nesting type's definition read as a module)";

  # Deep attrset merge (rhs wins at leaves) — for the `_module` pseudo-tree and the final
  # declared-over-freeform config merge (~:433).
  recursiveUpdate =
    lhs: rhs:
    lhs
    // mapAttrs (
      n: v:
      if (lhs ? ${n}) && isAttrs (lhs.${n} or null) && isAttrs v then recursiveUpdate lhs.${n} v else v
    ) rhs;

  # An option-decl LEAF is a `mkOption` descriptor (tagged `_type = "option"` by `lib/types.nix` `mkOption`).
  # Anything else inside the `options` tree is an option-GROUP: a plain attrset of sub-declarations.
  isOptLeaf = v: isAttrs v && (v._type or null) == "option";

  # ── THE OPTION RECORD, IN nixpkgs' SHAPE (den-hoag-foreign-mount-parity-knhyg, den-hoag-ixcxl) ──────
  # A declaration carries `loc` and `declarations` (the declaring modules' files, read off the
  # evaluation's own `sitesAt`, in nixpkgs' order: its module list is reversed once) and nixpkgs'
  # string form, `__toString = _: showOption loc` (nixpkgs `lib/modules.nix`
  # `mergeOptionDecls`/`evalOptionValue`), so `"${opt}"` reads the path there as here.
  #
  # THE STRATUM-1 DOOR (`declaredOptions`) folds no value, so its record is the declaration and the
  # evaluated keys nixpkgs adds beside it are REFUSED BY NAME, never absent, because an absent key is
  # an uncatchable abort in the reader (ADR-0025 item 1). One shared record, so a refusal costs no
  # thunk per option. nixpkgs has no such door.
  unansweredOptionKeys = listToAttrs (
    map
      (k: {
        name = k;
        value = throw "gen-merge: a gen option record does not answer `${k}': it is the declaration, not the evaluated option; read the value off the evaluation's `config' and its definitions off `provenance'";
      })
      [
        "value"
        "isDefined"
        "definitions"
        "definitionsWithLocations"
        "files"
        "highestPrio"
        "declarationPositions"
        "options"
        "valueMeta"
      ]
  );
  # THE EVALUATED RECORD, served wherever an evaluation publishes one: its `options`, a module's own
  # `options` argument, and `getSubOptions`. nixpkgs' keys are projections of ONE list, the
  # definitions its type merge read (`defsFinal`), and here they are projections of the list gen's
  # type merge read (`typeDefs`, carried on `optionDefs.defs`), so no key is a second derivation free
  # to disagree with the fold. `value` is the option's own merged value (`optionDefs.values`, the
  # declared-only tree), as nixpkgs' is, never the module config: that one's freeform layer would
  # make a freeform key gated on `options.x.value` a cycle. The `<default>` sentinel takes the file
  # nixpkgs gives it, `head declarations`; `highestPrio`'s `null` (nothing survived discharge) reads
  # as nixpkgs' `filterOverrides'` seed, 9999; `options` is `[ ]`, nixpkgs' value after
  # `fixupOptionType`. `valueMeta` is refused by name: it is nixpkgs' v2-merge metadata, whose records
  # carry nixpkgs' type objects and evaluations, and gen's types have no such merge.
  serveOptions =
    sitesAt: rel: loc: prov: defs: cfg: tree:
    mapAttrs (
      k: v:
      let
        lk = loc ++ [ k ];
      in
      if isOptLeaf v then
        let
          # the reference's declaration order: its module list reversed once, as its definitions are
          sites = reverse (sitesAt lk);
          dwl = map (d: if d.file == "<default>" then d // { file = (head sites).file; } else d) defs.${k};
          p = prov.${k};
        in
        v
        // {
          # nixpkgs' `fixupOptionType`: a declaration stating no type is `unspecified` (den-hoag-pm14k)
          type = v.type or strategies.unspecified;
          loc = lk;
          declarations = map (s: s.file) sites;
          __toString = _: showOption lk;
          definitionsWithLocations = dwl;
          definitions = map (d: d.value) dwl;
          files = map (d: d.file) dwl;
          isDefined = dwl != [ ];
          highestPrio = if p.priority == null then 9999 else p.priority;
          value = cfg.${k};
          declarationPositions = map (
            s:
            let
              pos = builtins.unsafeGetAttrPos k (getAttrByPath rel s.options);
            in
            if pos != null then
              pos
            else
              {
                inherit (s) file;
                line = null;
                column = null;
              }
          ) sites;
          options = [ ];
          valueMeta = throw "gen-merge: the option `${showOption lk}' does not answer `valueMeta': it is the reference engine's v2-merge metadata, whose records carry that engine's own type objects and evaluations";
        }
      else
        serveOptions sitesAt (rel ++ [ k ]) lk prov.${k} defs.${k} cfg.${k} v
    ) tree;
  stampOptions =
    sitesAt: loc: tree:
    mapAttrs (
      k: v:
      let
        lk = loc ++ [ k ];
      in
      if isOptLeaf v then
        v
        // unansweredOptionKeys
        // {
          loc = lk;
          declarations = map (s: s.file) (reverse (sitesAt lk));
          __toString = _: showOption lk;
        }
      else
        stampOptions sitesAt lk v
    ) tree;

  # ── isOptLeaf's missing THIRD arm: a declaration-plane misuse ─────────────
  # The disjunction above is binary, so a value that is neither a leaf nor a group is recursed into
  # as though its own internals were sub-declarations — and the abort fires frames below the mistake
  # as a raw, pathless, `tryEval`-UNCATCHABLE Nix type error (`expected a set but found a string:
  # "merge"`). ADR-0025 item 1 rules that every operation returns a value or a NAMED refusal.
  #
  # The misplaceable tag set is CLOSED at five, enumerable from this library's own source
  # (`grep -rhoP '_type\s*=\s*"\K[a-zA-Z-]+' lib/`): `merge`, `if`, `order`, `override` are
  # DEFINITION-plane combinators (`lib/priority.nix`), and the type tag belongs to a TYPE object
  # (`lib/interface.nix`, asked through `interface.isOptionType` because that literal is private to
  # that unit); `option` is the legitimate leaf. They carry TWO diagnoses, not one message repeated —
  # a combinator on the wrong plane and a type where a declaration belongs have different remedies,
  # and one shared string would misdiagnose a member while satisfying the enumeration.
  declPlaneMisuseTag =
    v:
    if !(isAttrs v) then
      null
    else if interface.isOptionType v then
      "bare-type"
    else
      let
        tag = v._type or null;
      in
      if tag == "merge" || tag == "if" || tag == "order" || tag == "override" then "combinator" else null;

  declPlaneMisuseMessage =
    loc: v: tag:
    let
      # A misuse AT the root of a module's own `options` has no option path to name — the offending
      # value IS the tree. Every other depth names the path, like the collision throw below.
      at = if loc == [ ] then "the `options' attrset itself" else "option `${showOption loc}'";
    in
    if tag == "bare-type" then
      "gen-merge: ${at} is declared as a bare type (`${interface.nameOf v}'), not a declaration; "
      + "wrap it: `mkOption { type = <that type>; }'"
    else
      "gen-merge: ${at} is declared as the `${v._type}' combinator "
      + "(mkMerge/mkIf/mkOrder/mkBefore/mkAfter/mkForce/mkOverride build DEFINITIONS, not "
      + "DECLARATIONS); move it under `config'/`imports', or write one plain attrset here";

  # Walks a module's declaration subtree, refusing BY NAME the instant it meets a misplaced tag at
  # ANY depth. Stops at a genuine leaf — an option descriptor's own internals (`type`, `default`, …)
  # are not a declaration tree — and otherwise recurses exactly where `isOptLeaf`'s group arm would,
  # so the per-key `mapAttrs` thunks keep today's laziness. A leaf child is returned without its
  # location, which only a refusal below it reads, and the tag is re-derived on the refusing branch
  # rather than bound on every group node.
  validateDeclSubtree =
    loc: v:
    if isOptLeaf v then
      v
    else if declPlaneMisuseTag v != null then
      throw (declPlaneMisuseMessage loc v (declPlaneMisuseTag v))
    else if isAttrs v then
      mapAttrs (k: c: if isOptLeaf c then c else validateDeclSubtree (loc ++ [ k ]) c) v
    else
      v;

  # ── fixed-input core marker (design spec §2.5) ────────────────────────────
  # A def value that CARRIES an already-merged subtree: `mkCoreValue digest values` tags
  # `values` (the by-contract full-merge output for a whole loc) so a consumer (gen-class tier-2)
  # can hand the engine a pre-computed result and skip the discharge/fold/verify spine for that loc.
  # This is a DIFFERENT insertion point from the README's per-option combine-kernel seam (that swaps
  # byte-vs-confluent HOW defs join; this short-circuits WHETHER they are joined at all). Recognised
  # ONLY when `evalModuleTree` runs with `coreShortCircuit = true` — default-off leaves the marker an
  # ordinary attrset value, so the engine is byte-for-byte unchanged (spec §2.5 opt-in constraint).
  # Two positional operands (den-hoag-7gp66 P2, R7): the digest names the subtree, `values` is the
  # subject it tags. Positional arity is structural, so there is no field to check.
  mkCoreValue = digest: values: {
    __coreValue = true;
    inherit digest values;
  };
  isCoreValue = v: isAttrs v && (v.__coreValue or false) == true;

  # Merge two TYPES through the `functor`/`typeMerge` protocol the library already ships
  # (lib/types.nix), guarded on both halves. nixpkgs assumes every type it meets carries the full
  # protocol; gen-merge meets types that do not — a gen-types PARAMETRIC leaf (`enum`, `struct`,
  # `union`) reaches the unified namespace as a bare constructor and is never protocol-completed, so
  # it carries no `functor`. A missing half answers "not mergeable" rather than aborting on a missing
  # attribute. This is the ONE binding both strata that ask the question consult — the ELEMENT
  # stratum (a container's own relation, `lib/types.nix` `elementRel`, which asks this about the two
  # ELEMENTS) and the DECLARATION stratum (`redeclareDecl` below) — so the two cannot drift into
  # answering it differently.
  #
  # A NON-MOUNTABLE operand answers "not mergeable" BEFORE the protocol halves are read, and this
  # ordering is load-bearing rather than defensive. The tree-as-a-type (`evalModuleTree`'s `.type`,
  # below) now carries `typeMerge`/`functor` as NAMED REFUSALS — reading either says "this is not an
  # option type" — but "do these two types merge?" is a question with a true answer here, and it is
  # `null`: they do not. Returning the value keeps the declaration stratum's own refusal, which names
  # BOTH types and every declaring file, in place of a refusal that would name only the tree.
  # ★★★ THE DISPATCH BASIS IS THE GEN-NATIVE RELATION, AND THE FOREIGN PROTOCOL IS THE SECOND ARM.
  #
  # This read `a.typeMerge b.functor` and nothing else — so the engine spoke the foreign protocol on
  # types that NEVER CROSS. That was not incidental coupling: `redeclareDecl` below calls this on the
  # pure-gen declaration path and throws on a `null` answer, and the containers reached it through
  # the element functor's `binOp`, so every container merge recursed back through the same
  # protocol-shaped relation. Strip the protocol fields from gen types under that arrangement and
  # every option declared twice throws.
  #
  # ★★ `typeMergeRel` IS ROW-FREE, WHICH IS THE WHOLE DIFFERENCE. nixpkgs asks
  # `a.typeMerge b.functor`: the second operand is a FUNCTOR PAYLOAD — a row whose shape both sides
  # must agree on, which is why the boundary needs a guard for a payload naming anything beyond the
  # role it understands (`lib/interface.nix` `importedCarried`). The relation takes THE OTHER TYPE.
  # No payload spelling crosses, so it is gen's own relation rather than the foreign protocol renamed.
  #
  # It is PARTIAL and its refusal is NAMED: `{ merged = <type>; }` or `{ refused = <reason>; }`, so
  # a caller that must throw can say what did not merge instead of reporting a bare null. This
  # binding still answers `null` for "not mergeable" because that is the contract its two callers
  # already read; the named reason is available to a caller that wants it.
  #
  # ★ THE FOREIGN ARM STAYS, AND IT IS NOT LEGACY. gen-merge meets FOREIGN functors by construction —
  # a gen type mounted in a foreign module system can face a same-named foreign type declared for
  # the same option. That partner has no `typeMergeRel` and never will. Removing the arm would make
  # the boundary one-directional, which is exactly the ceremony predicate this work is measured
  # against. The arm is the boundary's IMPORT ENVIRONMENT, reached here and spelled there: this is
  # the engine's own read of a foreign type, and it is why the inbound half is load-bearing rather
  # than decorative.
  #
  # ★ THE GEN ARM TAKES THE FOREIGN ARM'S PRE-FLIGHT, ONCE PER ENTRY (den-hoag-iaram). A gen relation
  # descends one carried role per call (`elementRel`, the union's pairwise members), so over a cyclic
  # type (`r = either int (listOf r)` declared twice) it never bottoms out, and nixpkgs' twin
  # overflows the stack on the same pair. Both operands are asked `importedDecidable` first, the
  # foreign arm's own walk and fuel; a pair that passes is a finite tree within the fuel, so the
  # relation's descent ends, and one that does not is `null`, named by `mergeTypesReason` below. The
  # descent itself (`relationMergeWithin`, reached through `mergeTypesWithin`, the element stratum's
  # `mergeElemTypes`) asks no pre-flight again: each operand it meets is a sub-tree of one already
  # walked, so asking again would re-walk every sub-tree once per level, quadratic in depth. Every
  # other ENTRY to a gen relation asks it too: `declaredPair`'s veto below, and `exportType`'s
  # `typeMerge` and `binOp` (`lib/interface.nix`), which a foreign engine calls.
  relationMergeWithin =
    a: b:
    if a ? typeMergeRel then
      let
        answer = a.typeMergeRel b;
      in
      if answer ? merged then answer.merged else null
    else
      let
        r = interface.importedMerge a b;
      in
      if r == null then null else rolesMet r a b;
  # THE FOREIGN ARM MEETS AT EVERY ROLE: the foreign join `r` is the carrier, and at each role the three
  # records carry (an element; a union's two members) its own carried type is met with the operands'
  # (`innerMet`), then `r` is rebuilt over the met roles by its own constructor. The top is met by the
  # caller (`mergeTypesBy`).
  rolesMet =
    r: a: b:
    let
      at =
        role:
        map (interface.carriedAt role) [
          r
          a
          b
        ];
      el = at "element";
      al = at "alternatives";
      rebuilt =
        role: carried:
        let
          x = interface.rebuiltOverAt role carried r;
        in
        if x == null then r else x;
      pick = l: i: builtins.elemAt l i;
      # a carried role's own join met with the operands' at that role, and at every role below it
      innerMet =
        r': a': b':
        interface.metWith (rolesMet r' a' b') [
          a'
          b'
        ];
    in
    if builtins.all (x: x != null) el then
      (
        let
          m = innerMet (pick el 0) (pick el 1) (pick el 2);
        in
        if sameTypeValue m (pick el 0) then r else rebuilt "element" m
      )
    else if builtins.all (x: x != null) al then
      (
        let
          m = builtins.genList (i: innerMet (pick (pick al 0) i) (pick (pick al 1) i) (pick (pick al 2) i)) 2;
        in
        if
          sameTypeValue (pick m 0) (pick (pick al 0) 0) && sameTypeValue (pick m 1) (pick (pick al 0) 1)
        then
          r
        else
          rebuilt "alternatives" m
      )
    else
      r;
  relationMerge =
    a: b:
    if a ? typeMergeRel && !(interface.importedDecidable a && interface.importedDecidable b) then
      null
    else
      relationMergeWithin a b;

  # ★★ A REDECLARED OPTION ACCEPTS A DEFINITION ONLY IF EVERY DECLARED CHECK DOES: EVERY TYPE MERGE IS
  # MET (den-hoag-l1j4q, owner-ruled 2026-10-06, the meet reading of a redeclaration). nixpkgs'
  # `addCheck` is `elemType // { check = …; }`: it keeps its base's name and relation, so a relation
  # answers its base's own `self`, a type that no longer holds the added check, and nixpkgs serves the
  # value the wrapper refuses. Each step here answers `interface.metWith m [ a b ]`: the relation's join
  # `m` (the carrier: its fold, name and functor, decided by nixpkgs' later-operand rule) restricted by
  # each operand's check it does not carry. By induction over the fold, the declared type accepts only
  # what every declaration accepts, a lower bound, not the greatest one (a join stricter than the
  # conjunction stays stricter). `declaredPair`'s veto arm routes a relation's `meets` answer through
  # the same function, and the foreign arm meets role by role (`rolesMet`).
  #  - A gen x gen step owes nothing (gen relations are exact over checks they state), so it is
  #    answered before `metWith` is called and allocates nothing.
  #  - A pair that is ONE value keeps it (`x ⊔ x = x ⊓ x = x`): the same wrapped binding declared
  #    twice merges and keeps its check.
  #  - The constructor's own law over its PARAMETERS is kept: a fresh join of one constructor that
  #    widens an operand's parameters (`enum`'s value union) owes that operand only where its own
  #    parameters admit the value, so a wrapper over it stays owed (`metWith`).
  #  - ★ AT A MODULE SET THE STEP CARRIES A DROPPED WITNESSED REWRITE'S CHECK (den-hoag-59gnz C4): the
  #    module-set fold does not enforce a met record's check, so the step answers the join restricted
  #    by the dropped check (`interface.carriedAtDepth`), a witnessed rewrite of the join, which the
  #    fold enforces as it enforces one declared alone. That is the carriage the declaration list's
  #    fixup gives a FOREIGN wrapper, which states no witness, so no step can see it dropped
  #    (`fixupModuleSets`, den-hoag-8ip0d); taken here, the freeform plane, which the fixup does not
  #    run on, is carried too. `dropsWrappedCheck` is asked first, so an unwrapped module set never
  #    builds the substructure read.
  #
  # The step lives HERE rather than at `declaredPair`, because a check is dropped wherever a type
  # merge runs and this is the binding every stratum reaches: `listOf (addCheck int p)` beside
  # `listOf int` drops it one level down, inside `elementRel`, which `declaredPair` never sees.
  # "One value" is Nix `==` over `closuresFirst`'s subject, as `sealedRel` compares, because an
  # exported record is cyclic. The comparison runs only on the path where a witnessed rewrite would
  # be dropped; a record with no witness short-circuits.
  sameTypeValue = x: y: interface.closuresFirst [ x ] x == interface.closuresFirst [ y ] y;
  # `interface.replacesVerify`, restated inline for cost: this is asked of both operands of every step
  verifySlice = builtins.intersectAttrs { verify = null; };
  dropsWrappedCheck =
    m: o:
    (
      interface.rewritesCheck o
      ||
        o ? verify
        && !(builtins.isFunction (o.__typeSelf or null) && verifySlice o == verifySlice (o.__typeSelf null))
    )
    && !(sameTypeValue m o);
  mergeTypesBy =
    relation: a: b:
    let
      m = relation a b;
    in
    if m == null then
      null
    else if !(dropsWrappedCheck m a || dropsWrappedCheck m b) then
      # a gen relation's answer over two gen operands stating their own checks carries both: nothing is
      # owed, and nothing is allocated (`metWith`'s first test, inline)
      if m ? typeMergeRel && a ? typeMergeRel && b ? typeMergeRel then
        m
      else
        interface.metWith m [
          a
          b
        ]
    else if sameTypeValue a b then
      a
    else if (interface.importedSubstructure m).modules != null then
      interface.carriedAtDepth true [
        a
        b
      ] m
    else
      interface.metWith m [
        a
        b
      ];
  mergeTypes = mergeTypesBy relationMerge;
  mergeTypesWithin = mergeTypesBy relationMergeWithin;

  # The same relation, answering with its REASON rather than with `null` — for a caller that reports
  # rather than dispatches. `redeclareDecl` throws on a failed merge and has to name the pair; where
  # the relation supplied a reason, that reason is better than a name comparison reconstructed at
  # the throw site.
  # ★ THE FOREIGN ARM NAMES THE ONE REFUSAL THE BOUNDARY MAKES ON ITS OWN. `importedMerge` answers
  # `null` for a pair whose structure does not bottom out within its type-walk fuel — the foreign
  # `typeMerge` would abort uncatchably on it — and that `null` is indistinguishable at the throw
  # site from an ordinary "these two names do not merge". Reading the predicate back here is what
  # turns it into a reason an author can act on; the fuel is interpolated from the one binding that
  # states it, so the number lives at a single site.
  #
  # ★ BOTH THROW SITES INHERIT THIS through `declaredPair` below: `redeclareDecl` (the declaration
  # plane) and the freeform selection both report `declaredRefusalText`, which prefers this reason
  # to a bare name pair. It is asked `(later, earlier)`, the deciding operand first. A gen type is unaffected — `mergeTypes` short-circuits on `typeMergeRel` before the
  # boundary is reached, so the first arm still answers for every pair that has a relation.
  # The drop arm comes first: where the relation answers but `mergeTypes` refused a dropped check, the
  # relation itself has no refusal to report, so this names the merged type and whose check it lost.
  # Whose is said by POSITION in the pair the reason names, not as "later"/"earlier": inside a
  # container the pair arrives in whichever order the deciding relation asked it, and `declaredPair`'s
  # veto asks the earlier operand's relation first.
  mergeTypesReasonBy =
    within: a: b:
    let
      m = (if within then relationMergeWithin else relationMerge) a b;
      dA = m != null && dropsWrappedCheck m a;
      dB = m != null && dropsWrappedCheck m b;
    in
    if (dA || dB) && !(sameTypeValue a b) then
      "`${interface.nameOf a}' and `${interface.nameOf b}', which merge to `${interface.nameOf m}', a type that drops the `check' a wrapper added to ${
        if dA && dB then
          "both"
        else if dA then
          "the first"
        else
          "the second"
      }"
    else if
      a ? typeMergeRel && (within || interface.importedDecidable a && interface.importedDecidable b)
    then
      (a.typeMergeRel b).refused or null
    else if !(interface.importedDecidable a) || !(interface.importedDecidable b) then
      "`${interface.nameOf a}' and `${interface.nameOf b}', whose structure does not bottom out within the boundary's type-walk fuel (${toString interface.importedTypeWalkFuel})"
    else
      interface.importedMergeReason a b;
  mergeTypesReason = mergeTypesReasonBy false;
  mergeTypesReasonWithin = mergeTypesReasonBy true;

  # ── the declared-type LIST: how N declarations of one option (or N freeform winners) merge ──
  #
  # nixpkgs' `mergeOptionDecls` folds `res.type.typeMerge opt.options.type.functor` over a
  # declaration list `evalModules` has REVERSED, so the accumulated type is seeded from the LAST
  # declaration and decides against each earlier one: [a,b,c] = (c ⊳ b) ⊳ a. `⊳` is not
  # associative, so the bracketing is part of the answer, not a presentation choice: a left fold
  # (a ⊳ b) ⊳ c, or pairwise-correct operands under a left fold, c ⊳ (b ⊳ a), each disagree with
  # nixpkgs from three declarations up. Both planes read the list through `mergeDeclaredTypes`.
  #
  # `declaredPair earlier later` is ONE fold step, and it answers
  # `{ merged = <type>; }` or `{ refused = <reason-or-null>; earlier; later; }`:
  #   · VETO FIRST — an earlier gen-native relation (`typeMergeRel`) that refuses the later operand
  #     is the answer, in that relation's own words. No later relation overrules it. EXCEPT a refusal
  #     stated `vetoes = false`: the relation's answer AS THE DECIDER, mirroring what its nixpkgs twin's
  #     relation answers in the order where the twin decides (the leaf relation's payload refusal,
  #     `lib/types.nix` `nullaryRel`). nixpkgs never asks the earlier operand, so neither does this
  #     step: the later operand decides, and the refusal only names the pair where that relation
  #     gives no join (a foreign relation's assert included, taken through `tryEval` on this path
  #     alone, as `interface.joinInRebuiltPartner` takes one). A partner relation's own `throw` is
  #     caught the same way, so it is reported in gen's words and the partner's are lost; an `abort`
  #     is not caught and surfaces unchanged.
  #   · otherwise the LATER operand decides, `mergeTypes later earlier`, which is nixpkgs'
  #     `later.typeMerge earlier.functor` on a foreign pair.
  # Because the step is asked of the ACCUMULATED later type, a gen relation is asked about the type
  # the later declarations jointly became, never about a declaration a later relation has already
  # merged away. Where this departs from nixpkgs it departs by REFUSING — where a step's gen relation
  # refuses, or where a foreign join drops a name an operand states (`interface.joinRenames`) — or,
  # for a foreign pair that is one shared value, by keeping it: README "Known byte-mode boundaries
  # (deliberate)".
  declaredPair =
    earlier: later:
    let
      # the pre-flight, asked once for both the veto and the merge (`relationMerge` above)
      decidable = interface.importedDecidable earlier && interface.importedDecidable later;
      veto = if earlier ? typeMergeRel && decidable then earlier.typeMergeRel later else { };
      # read only where the veto did not end the step, so a refusal seen here is one that defers
      m =
        if !decidable then
          null
        else if veto ? refused then
          (
            let
              tried = builtins.tryEval (mergeTypesWithin later earlier);
            in
            if tried.success then tried.value else null
          )
        else
          mergeTypesWithin later earlier;
    in
    if veto.meets or false then
      {
        merged = interface.metWith veto.merged [
          earlier
          later
        ];
      }
    else if veto ? refused && (veto.vetoes or true) then
      {
        inherit (veto) refused;
        inherit earlier later;
      }
    else if m == null then
      {
        refused = veto.refused or (mergeTypesReason later earlier);
        inherit earlier later;
      }
    else
      { merged = m; };
  # nixpkgs `fixupOptionType`: the merged type rebuilt over the AUTHORED concatenation of every
  # declaration's own module set, replacing whatever module list the join's `binOp` built, and
  # restricted by every check a declaration states that the rebuild cannot carry, at every depth
  # (`interface.carriedAtDepth`, den-hoag-8ip0d): nixpkgs' rebuild erases them, gen's enforces them. A type
  # that states no module set (a leaf, `either`, `oneOf`) is returned as is. Lives on the
  # declaration plane, not in `mergeDeclaredTypes`, because that is also the freeform-type merge,
  # which nixpkgs's `optionType.merge` leaves unrebuilt.
  fixupModuleSets =
    declared: merged:
    let
      sub = interface.importedSubstructure merged;
      own =
        t:
        let
          m = (interface.importedSubstructure t).modules;
        in
        if m == null then [ ] else m;
    in
    if sub.modules == null then
      merged
    else
      interface.carriedAtDepth true declared (sub.rebuild (concatMap own declared));
  # The list, in AUTHORED order; stops at the first refusing step. A one-element list is itself.
  mergeDeclaredTypes =
    ts:
    foldl' (acc: earlier: if acc ? refused then acc else declaredPair earlier acc.merged) {
      merged = prelude.last ts;
    } (reverse (prelude.init ts));
  # A relation-supplied reason is that relation's own text and names the DECIDING (later) type
  # first; only the null-reason fallback is spelled here, and it names the pair in authored order,
  # through the library's one total name reader (`interface.nameOf`). Where the two state functor
  # names that differ, those are what a foreign `typeMerge' keyed on, so the fallback names them too
  # (`interface.functorNamesOf`): a derivation keeps its base's type name, and the bare pair would
  # read "`int' and `int'".
  declaredRefusalText =
    d:
    if d.refused != null then
      d.refused
    else
      let
        pair = "`${interface.nameOf d.earlier}' and `${interface.nameOf d.later}'";
        functorNames = interface.functorNamesOf d.earlier d.later;
      in
      if functorNames == null then
        pair
      else
        "${pair}, whose functors are named `${functorNames.first}' and `${functorNames.second}'";

  # The declaring SITES at one option loc, in authored module order — the entries whose own
  # `options` tree carries `loc` as a LEAF, each keeping the `idx` it had in the module fold. The
  # index is what lets a shadow record name the module that actually contributed the field being
  # shadowed rather than the n-th declarer of the option. Each site also carries its own leaf as
  # `decl`, lazily.
  # The entries are grouped ONCE into a lazy trie keyed by path step (`zipAttrsWith`, nixpkgs
  # `mergeModules'`'s `declsByName`), so a loc is answered by a lookup of `depth` steps, never by a
  # scan of the module list per loc. `depth` (the caller's prefix length) is applied inside, so each
  # caller binds the application once. A node forces each entry's subtree at its own depth to WHNF and
  # reads its `_type`, and nothing deeper. Every per-key list keeps entry order. It is read on the happy path: every redeclaration step where both operands are typed
  # reads it (`redeclareDecl`), and the declaration fold reads each redeclared leaf's site indices
  # from it (`mergeOptionDeclTrees`).
  declaringSitesAt =
    depth: entries:
    let
      node = xs: {
        sites = map (x: x.e // { decl = x.o; }) (filter (x: isOptLeaf x.o) xs);
        under = builtins.zipAttrsWith (_: node) (
          map (
            x:
            if isAttrs x.o && !(isOptLeaf x.o) then
              mapAttrs (_: o: {
                inherit (x) e;
                inherit o;
              }) x.o
            else
              { }
          ) xs
        );
      };
      at =
        n: path:
        if path == [ ] then
          n.sites
        else if n.under ? ${head path} then
          at n.under.${head path} (tail path)
        else
          [ ];
      root = node (
        map (e: {
          inherit e;
          o = e.options;
        }) entries
      );
    in
    lk: at root (drop depth lk);

  # redeclareDecl — the ENGINE's answer when one option loc is declared by two modules.
  #
  # A DECLARATION MERGE CONSULTS THE TYPE ALGEBRA THE LIBRARY ALREADY SHIPS. When both declarations
  # carry a `type`, the merged declaration's type is `mergeDeclaredTypes`' answer about EVERY typed
  # declaration of the loc, bracketed as nixpkgs brackets it (see `declaredPair`); a refusal is a
  # NAMED REFUSAL carrying the option path and the declaring files. This is
  # the one place on the declaration path that did not consult the protocol, and the measured cost
  # was a record disagreeing with itself: one declaration's descriptor surviving beside the OTHER's
  # type, no error and no warning. Routing here is why that is no longer expressible — the only way
  # a merged declaration acquires a type is through a merge that must return one. The predicate is
  # not invented here: it ships as the advisory lint kind `type-merge` (lib/lint.nix), whose own
  # finding text is a standing admission that the library knew the answer and declined to give it.
  #
  # THE NON-TYPE FIELDS STAY RIGHT-BIASED, and the ground is ADR-0029: positional authority is the
  # substrate's, and this fold is an ORDERED fold over the authored module order — a later
  # declaration is a later contribution, not a stronger one. gen-schema's ref-binding modules are the
  # deliberate consumer: a module layering `apply` onto an earlier typed leaf carries no `type` of
  # its own, so it never reaches the algebra above.
  #
  # AN ORDERED BIAS IS A RULE ONLY WHILE THE LOSER STAYS REACHABLE. Bracha & Cook 1990 keep the
  # overridden parent behind `super`; Leijen 2005's scoped labels retain a shadowed field "both in
  # the value and in the type", against free extension where "the previous value is overwritten,
  # after which it is no longer accessible". So a merge that actually shadows a field records what
  # it shadowed, oldest first, under `overridden` — the declaration stratum's provenance, beside the
  # definition stratum's on the result.
  #
  # BOUNDARY, stated because the rule does not reach it: a field whose value is REFLECTED INTO AN
  # IDENTITY is not made safe here. Those sit under ADR-0016's option-set-closure precondition, and
  # enforcing it belongs to the minting spec, not to this engine. What this guarantees is narrower:
  # the merged record's TYPE is the algebra's answer about every typed declaration, never one of
  # them picked in silence.
  #
  # THE TYPE IS DECIDED ONCE, AT THE LAST TYPED DECLARATION. The record fold is left and binary
  # (ADR-0029) and `⊳` is not associative, so the fold cannot compute (c ⊳ b) ⊳ a step by step.
  # The loc's typed sites and the index of the last of them are read from `sitesAt` once per loc, and
  # each step is told its position `j` in the loc's declaration list; the step with no typed site
  # after it (`modIndex >= lastTypedIdx`) decides, and only there does a refusal throw. An earlier step's `type` is
  # the prefix's answer — lazy, so `overridden[].declaration.type` keeps its meaning of "the
  # accumulated earlier declaration" — and a prefix that does not merge on its own reads as a named
  # throw if forced, since a later declaration may still merge the whole list (with `B = attrsOf
  # int`, `fo` a `B` whose functor is renamed and `Fk` a `B` whose relation admits any partner,
  # `[fo, B, Fk]` merges to `attrsOf` on both engines). A later UNTYPED site does not defer the
  # decision.
  # The shadow chain `redeclareDecl` threads, as the published oldest-first list: one
  # `genericClosure` walk back along `prev` (each node's `key` is its depth), reversed once. The
  # functional queue: a `++` per step would copy every earlier entry, quadratic in bytes when forced.
  shadowChainList =
    c:
    map (n: n.entry) (
      reverse (
        builtins.genericClosure {
          startSet = [ c ];
          operator = n: if n.prev == null then [ ] else [ n.prev ];
        }
      )
    );
  redeclareDecl =
    sitesAt: lk:
    let
      sites = sitesAt lk;
      # the loc's typed sites and the index of the last of them, bound ONCE per loc: the step function
      # below is applied to the loc's whole declaration list, so a scan of `sites` inside it would run
      # once per declaring module
      typed = filter (s: s.decl ? type) sites;
      lastTypedIdx = if typed == [ ] then -1 else (prelude.last typed).idx;
      # the declared-type list through module index `i`: every typed site at or before it, and the
      # list's answer. Bound once per loc and applied per step, so a step that is not the last typed
      # one allocates the one `type` thunk that reads it, and nothing else.
      through =
        i:
        let
          prior = filter (s: s.idx <= i) typed;
          declaredTypes = map (s: s.decl.type) prior;
        in
        {
          inherit prior declaredTypes;
          upTo = mergeDeclaredTypes declaredTypes;
        };
      typeOf =
        r:
        if r.upTo ? merged then
          fixupModuleSets r.declaredTypes r.upTo.merged
        else
          throw "gen-merge: option `${showOption lk}': the declarations through the one in ${(prelude.last r.prior).file} do not merge on their own (${declaredRefusalText r.upTo}); a later declaration decides them";
      step =
        j: av: bv:
        let
          modIndex = (prelude.elemAt sites j).idx;
          merged = av // bv;
          # PRESENCE, never value equality: deciding "did B restate this field" by comparison would
          # force declaration values nothing has asked for. `_type` is the metadata every option record
          # carries — identical by construction, so never a shadow.
          shadowed = filter (k: k != "_type" && bv ? ${k}) (attrNames av);
          # `av` is an ACCUMULATION of every earlier module that declared `lk`, and `file` names the one
          # that most recently contributed to it — the last declaring site before this merge. It is NOT
          # "the file that declared every field in the record": a module that only ADDS a field shadows
          # nothing and records no entry, yet its contribution is what a later module goes on to shadow,
          # and that entry must name IT rather than whoever declared the option first. Indexing the site
          # list by how many entries have accumulated says otherwise and is wrong for exactly that shape
          # — shadow events and declaring modules are different counts. `<unknown-file>` where there is
          # no earlier site (a decl tree assembled outside the module fold), never a guess. It is also
          # the label an anonymous declaring module carries (nixpkgs' `unknownModule`), so the entry does
          # not tell "no earlier site" from "an anonymous module declared it"; nothing compares it.
          #
          # `overridden` appears ONLY where a declaration really was shadowed: a layering module that
          # merely ADDS fields leaves the record exactly what the plain union produced. An intermediate
          # step's `overridden` is a chain node (`shadowChainList`), cons-ed in constant space; nothing
          # observes it, since each entry's `declaration` drops the field and only the next step reads
          # it. The last step (`j + 1 == length sites`, the alignment `elemAt sites j` already rests on)
          # publishes the list, oldest first.
          chain =
            let
              c = {
                key = (av.overridden.key or 0) + 1;
                entry = {
                  file = if j == 0 then "<unknown-file>" else (prelude.elemAt sites (j - 1)).file;
                  declaration = builtins.removeAttrs av [ "overridden" ];
                };
                prev = av.overridden or null;
              };
            in
            if j + 1 == length sites then shadowChainList c else c;
          kept =
            if shadowed == [ ] then
              if av ? overridden && j + 1 == length sites then
                merged // { overridden = shadowChainList av.overridden; }
              else
                merged
            else
              merged // { overridden = chain; };
        in
        # A step whose two operands both carry a `type` shadows `type`, so it records a shadow by
        # construction: its record is the union, the chain and the type, built in one `//`.
        if !((av ? type) && (bv ? type)) then
          kept
        # the LAST typed declaration decides the whole list; an earlier step's prefix is provisional
        else if modIndex >= lastTypedIdx then
          let
            r = through modIndex;
          in
          if r.upTo ? refused then
            throw "gen-merge: option `${showOption lk}' is declared with types that do not merge (${declaredRefusalText r.upTo}); declared in ${
              concatStringsSep ", " (map (s: s.file) sites)
            }"
          else
            merged
            // {
              overridden = chain;
              type = typeOf r;
            }
        else
          merged
          // {
            overridden = chain;
            type = typeOf (through modIndex);
          };
    in
    # the leaf's k declarations, folded from the left as the binary fold does, each step forced to
    # WHNF as it is made (a lazy accumulator would be forced from the outside, to depth k); `j` is the
    # position of the step's later operand in the loc's list
    ys:
    (foldl' (
      acc: j:
      let
        v = step j acc.v (prelude.elemAt ys j);
      in
      builtins.seq v { inherit v; }
    ) { v = head ys; } (prelude.genList (j: j + 1) (length ys - 1))).v;

  # mergeOptionDecls — combine two option-decl TREES (nixpkgs mergeModules' descent, byte-mode).
  # This is what lets `options.a.b.c = mkOption {…}` build a NESTED tree rather than the old
  # single-level view:
  #   leaf ∪ leaf  = `onRedeclare` — see below;
  #   group ∪ group = RECURSE (a second module's `options.a.b.d` merges beside `options.a.b.c`);
  #   leaf ⁄ group at the same path = a hard collision (nixpkgs likewise refuses to make an option
  #                  the parent of sub-options) — must throw, never silently `//`-merge.
  # `onRedeclare lk av bv` is a REQUIRED formal, not a defaulted hook: the tree walk knows the shape
  # of a redeclaration and nothing about what it means, and the two callers genuinely disagree. The
  # engine passes `redeclareDecl`; the portable-subset lint passes the plain field-union, because a
  # lint that ABORTED on the redeclaration it exists to report could never report it. Making the
  # caller state it keeps that divergence one legible argument rather than a fork of the descent.
  # DELIBERATE divergence: nixpkgs' `optionTreeToOption` has one sugar case —
  # raw options merged INTO a `submodule`-typed leaf — that byte-mode does not reproduce (out of the
  # den surface; submodule nesting rides the separate `submodule`/`attrsOf` `.merge` path). Byte-mode
  # conservatively throws here rather than risk emitting wrong bytes.
  mergeOptionDecls =
    onRedeclare: loc: a: b:
    a
    // mapAttrs (
      k: bv:
      let
        lk = loc ++ [ k ];
      in
      if a ? ${k} then
        let
          av = a.${k};
          aLeaf = isOptLeaf av;
          bLeaf = isOptLeaf bv;
        in
        if aLeaf && bLeaf then
          onRedeclare lk av bv
        else if (!aLeaf) && (!bLeaf) then
          mergeOptionDecls onRedeclare lk av bv
        else
          throw "gen-merge: option `${showOption lk}' is declared both as an option and as an option-group (leaf/group collision)"
      else
        bv
    ) b;

  # mergeOptionDeclTrees — the engine's declaration fold: `mergeOptionDecls`' answer over a whole
  # LIST of trees (the declaring entries' validated `options`, in entry order), grouped once per level
  # with `zipAttrsWith`, so no step copies a growing accumulator (a `//` fold copies it once per
  # module). A key declared once is that declaration; a group recurses; a leaf/group mix throws the
  # binary fold's collision text; a leaf declared k times is `onRedeclare lk ys`, one call over the
  # loc's k declarations: `redeclareDecl` folds its step from the left there, as the binary fold
  # does, and the guard's `spineRedeclare` answers the last declaration, which is what that fold
  # keeping the later operand answers. The binary `mergeOptionDecls` stays the lint's fold, and
  # applies `onRedeclare lk av bv`.
  mergeOptionDeclTrees =
    onRedeclare: loc: trees:
    let
      xs = filter (v: v != { }) trees;
    in
    if xs == [ ] then
      { }
    else if length xs == 1 then
      head xs
    else
      builtins.zipAttrsWith (
        k: ys:
        if length ys == 1 then
          head ys
        else
          let
            lk = loc ++ [ k ];
            leaf = isOptLeaf (head ys);
          in
          if !(all (y: isOptLeaf y == leaf) ys) then
            throw "gen-merge: option `${showOption lk}' is declared both as an option and as an option-group (leaf/group collision)"
          else if leaf then
            onRedeclare lk ys
          else
            mergeOptionDeclTrees onRedeclare lk ys
      ) xs;

  # ── list/path helpers for the warm re-eval path (design spec §§1-3) ─────────
  # `drop n` / `take n` (gen-prelude ships neither) — index-based, no `++` accumulation.
  drop =
    n: xs:
    let
      l = length xs;
    in
    prelude.genList (i: prelude.elemAt xs (n + i)) (if l > n then l - n else 0);
  take =
    n: xs:
    let
      l = length xs;
      m = if n < l then n else l;
    in
    prelude.genList (i: prelude.elemAt xs i) (if m > 0 then m else 0);

  # ── freeform def coalescing (per originating module instance) ──────────────────────────────────
  # nixpkgs' freeformType option receives a FEW WIDE defs — one per module, each carrying that
  # module's WHOLE unmatched-config subtree — so the `attrsOf`/`lazyAttrsOf` key-union and per-key
  # folds run linear in sibling-key count. The realizer instead bubbles undeclared keys up ONE def
  # PER KEY (`mergeTree`'s `ownUnmatched`), so handing them straight to `freeform.merge` would give it
  # n single-key defs → its `foldl' (//)` key-union and per-key `concatMap` both go O(n²). Coalescing
  # rebuilds the per-module shape (byte-identical output): group the unmatched defs by originating
  # MODULE INSTANCE (a threaded index — NOT `_file`: distinct anonymous modules share the
  # `<unknown-file>` fallback file yet must stay SEPARATE defs for priority resolution), then emit one
  # wide def per module in ASCENDING index order. Ascending index = reverse-module order (topDefs is
  # `pushedRev`), which is the order nixpkgs collects defs in (last module first) — load-bearing for
  # list-typed freeform values, order-independent for scalars/attrsets.
  #
  # Within a module the unmatched paths are DISJOINT, so its subtree is assembled in one pass: depth-1
  # keys (the wide-freeform hot path) build via `listToAttrs` — O(width) — and the deeper keys
  # (undeclared UNDER a declared group) fold via `recursiveUpdate`. That fold is O(deep-entries ×
  # subtree-width) (each `recursiveUpdate` copies its LHS), fine only because deeper freeform is BOTH
  # rare AND narrow on the den surface — a WIDE nested freeform group would want the same listToAttrs
  # treatment, but no consumer needs it. A depth-1 head and a deeper head can never collide within one
  # module (a key undeclared HERE is captured whole and never descended; a deeper key rode a DECLARED
  # group), so the two partitions union cleanly.
  buildModuleUnmatched =
    entries:
    let
      flat = filter (u: length u.path == 1) entries;
      deep = filter (u: length u.path > 1) entries;
      flatAttrs = listToAttrs (
        map (u: {
          name = head u.path;
          inherit (u) value;
        }) flat
      );
      deepAttrs = foldl' (acc: u: recursiveUpdate acc (setAttrByPath u.path u.value)) { } deep;
    in
    recursiveUpdate flatAttrs deepAttrs;

  # Group the entries by module ONCE (`builtins.groupBy`, which keeps each group in list order), then
  # read each module's group in ASCENDING index order (= reverse-module order) and build its subtree
  # once: linear in |unmatched| and in the module count, which is not bounded. A `foldl'` group-by
  # would not be: with no O(1) cons/insert, accumulating per-module lists (`++`) or subtrees (`//`)
  # copies the growing value each step (measured: 27× CPU / 52× alloc at a 4× width step, hidden from
  # a thunk count because the copies are lazy). A builtin grouping copies nothing.
  # `withIndex` keeps each module's `modIndex` on its record, for the nested walk's declaration
  # addresses (`nestedDeclAts`); the freeform fold's own call takes the bare record.
  coalesceUnmatched =
    withIndex: moduleCount: unmatched:
    let
      byModule = builtins.groupBy (u: toString u.modIndex) unmatched;
    in
    concatMap (
      i:
      let
        entries = byModule.${toString i} or [ ];
      in
      optional (entries != [ ]) (
        if withIndex then
          {
            file = (head entries).file;
            value = buildModuleUnmatched entries;
            modIndex = i;
          }
        else
          {
            file = (head entries).file;
            value = buildModuleUnmatched entries;
          }
      )
    ) (prelude.genList (i: i) moduleCount);

  # ── module classification: the reference's `unifyModuleSyntax`, key list for key list ─────────
  # STRUCTURED iff the module carries `config` or `options` — nothing else makes it structured. A
  # structured module admits exactly `structuredKeys` (the reference's `attrsToRemove`, verbatim, plus
  # this engine's `__pureModule`, `__reservedKeys` and `__keyEq`); any other top-level key is REFUSED BY NAME, naming every surplus
  # key and the file, whatever `check` says. `_module` is such a key, as in the reference: beside
  # `config`/`options` it is refused, because `_module` is a CONFIG path (`config._module`) and two
  # sites in one module would be two definitions with no order between them. `meta` is folded into
  # config as `meta`.
  # Otherwise the module is SHORTHAND: `shorthandMetaKeys` (the reference's `shorthandAttrsToRemove`,
  # verbatim, plus `_module` and `__pureModule`) are metadata, `require` joins `imports`
  # (`importsOf`), and every other key is config. The shorthand arm copies the module only when a
  # metadata key is present.
  #
  # The deliberate departures, each listed under README "Known byte-mode boundaries":
  #   * `_class` is stripped and never checked — this engine has no `class` parameter, which is the
  #     reference's `class = null`.
  #   * `disabledModules` is REFUSED BY PRESENCE, before the surplus test, in both forms — an empty
  #     list included, which the reference accepts. This engine does not implement module removal
  #     (deferred work, re-armed by a consumer that needs it): the modules named would stay enabled.
  #     Refusing by presence never forces the list. The key stays in both lists so they are verbatim.
  #     A declaration read refuses it too, so `.options`, `declaredOptions` and
  #     `substructure.declares` refuse the empty list as well as a config read does.
  #   * THE REFUSALS FIRE ON EACH DOOR'S FIRST READ OF A MODULE, as the reference's
  #     `unifyModuleSyntax` does. Both throws live in `moduleSyntaxChecked`, in this order, and it is
  #     read at exactly two sites: `declarationStratum`'s entries and `lint`'s `rootPushed`. The first
  #     is the engine's first read of every flattened entry: `evalModuleTree` forces it through
  #     `declarationGuard` before any config, and `declaredOptions` and `substructure.declares` read it
  #     directly. So a declaration-only read refuses exactly as a config read does, and a warm trace
  #     over a refused module set refuses with it. `configOf` only classifies. A reserved name in a
  #     scoped module (`reservedHits`) refuses after `disabledModules` and before the surplus test,
  #     so a structured module gets the owner's text rather than the generic surplus remedy.
  #
  # COST. The clean path pays one call per entry: `moduleSyntaxChecked` returns the ENTRY it was handed,
  # the predicate is `?` tests written inline (not a call to `isStructured`), `e._file` and the key
  # names are read only inside the throws, and a structured entry pays one `removeAttrs` compared
  # against `{ }`.
  structuredKeys = [
    "_class"
    "_file"
    "key"
    "disabledModules"
    "imports"
    "options"
    "config"
    "meta"
    "freeformType"
    "__pureModule"
    "__reservedKeys"
    "__keyEq"
  ];
  shorthandMetaKeys = [
    "_class"
    "_file"
    "key"
    "disabledModules"
    "require"
    "imports"
    "freeformType"
    "_module"
    "__pureModule"
    "__reservedKeys"
    "__keyEq"
  ];
  # The keys this engine reads off the RECORD of a `__functor` module, before applying it (see
  # `reservedHits`), published as data (moduleSyntax.functorRecord) so a library riding a key there
  # can refuse an engine that would never read it.
  functorRecordKeys = [
    "__reservedKeys"
    "__keyEq"
  ];
  # The reader's own structuring test, published as data (moduleSyntax.structuring, lib/default.nix)
  # so a consumer's structured/shorthand guard reads the rule this engine enforces instead of
  # restating it (den-hoag-4kh.53.55; den-hoag-1n12c).
  structuringKeys = [
    "config"
    "options"
  ];
  isStructured = m: m ? config || m ? options;
  configOf =
    e:
    let
      m = e.content;
    in
    if m ? config || m ? options then
      (if m ? meta then (m.config or { }) // { inherit (m) meta; } else m.config or { })
    else if
      m ? _file
      || m ? key
      || m ? _class
      || m ? disabledModules
      || m ? require
      || m ? imports
      || m ? freeformType
      || m ? _module
      || m ? __pureModule
      || m ? __reservedKeys
      || m ? __keyEq
    then
      # A shorthand module's `_module` is config like any other key: stripped with the
      # metadata keys and restored. A structured module's top-level `_module` is refused by
      # `moduleSyntaxChecked`, so the structured arm above never reads it.
      let
        s = builtins.removeAttrs m shorthandMetaKeys;
      in
      if m ? _module then s // { inherit (m) _module; } else s
    else
      m;
  optionsOf = m: m.options or { };
  # nixpkgs' `internalModule` declares four `_module` options. This engine reads `args` and
  # `freeformType` itself and takes `specialArgs` at its door, so a module defining `specialArgs` is
  # refused by name. `check` is the option it is in nixpkgs, declared per evaluation, so a module
  # defining it is merged with the door's `mkDefault` and honoured at this level only. Every other
  # `_module` sub-key stays a config path, met by the realizer like any other: a declared one
  # merges, an undeclared one is unmatched.
  moduleOwnKeys = [
    "args"
    "freeformType"
    "check"
    "specialArgs"
  ];
  # The engine's own declaration of each of those keys, as nixpkgs' `internalModule` declares it,
  # carrying exactly what that engine's `mergeOptionDecls` reads of a declaration: which of
  # `default`, `example`, `description` and `apply` it states. Whether a declared type merges with
  # its own is the boundary's question (`interface.moduleOwnTypeAdmits`).
  moduleOwnDecls = {
    args.description = true;
    check = {
      default = true;
      description = true;
    };
    freeformType = {
      default = true;
      description = true;
    };
    specialArgs.description = true;
  };
  # ── THE ENGINE'S OWN `_module` RECORDS, SERVED (den-hoag-a67l3) ─────────────────────────────────
  # nixpkgs' `internalModule` declares the four keys in every evaluation, so its `options`, a
  # module's `options` argument and `getSubOptions` hold their records. They stay out of
  # `allOptions` (the warm identity walk, the docs and lint read that tree) and are added where an
  # evaluated record is served, over the values the module-visible `config._module` holds
  # (`moduleConfig`), so `options._module.<k>.value` and `config._module.<k>` are one value. The file
  # is the one that states them here, the name nixpkgs gives its own.
  moduleOwn = rec {
    file = "lib/modules.nix";
    options = prefix: {
      args = {
        type = strategies.lazyAttrsOf strategies.raw;
        description = "The arguments each module is applied to beside `config', `options', `prefix' and the caller's `specialArgs': the modules' own `_module.args', merged, with a positioned evaluation's `name'.";
      }
      // (if prefix == [ ] then { } else { internal = true; });
      check = {
        type = leaves.bool;
        internal = true;
        default = true;
        description = "Whether to check whether all option definitions have matching declarations.";
      };
      freeformType = {
        type = strategies.nullOr strategies.optionType;
        internal = true;
        default = null;
        description = "If set, the type every definition without an associated option is merged with; its result is combined with the declared options' values to produce `config'.";
      };
      # nixpkgs' states no type: its record's `unspecified` is the fixup every untyped declaration gets
      specialArgs = {
        readOnly = true;
        internal = true;
        description = "The caller's `specialArgs', which every module is applied to; a module cannot define it.";
      };
    };
    # The four records over `own`, the evaluation's `optionDefs.moduleOwn`, added to a served tree. A
    # module re-declaring a key states fields beside the engine's own, as nixpkgs merges the two
    # (`moduleOwnRedeclared` has judged the pair), and its files follow the engine's in `declarations`,
    # as nixpkgs' reversed module list puts its own module first. A `submodule`-typed `_module` leaf
    # is one option, and nixpkgs serves that record alone.
    serve =
      prefix: own: served:
      let
        user = served._module or { };
        record =
          k: d:
          let
            lk = prefix ++ [
              "_module"
              k
            ];
            u = user.${k} or { };
            o = own.${k};
          in
          {
            _type = "option";
          }
          // d
          // u
          // {
            # the engine's stated type (a re-declaration's has been judged to merge with it), else the
            # re-declaration's, else nixpkgs' `fixupOptionType` default; a served `u` states the
            # fixup for an untyped re-declaration, which must not displace the engine's own
            type = d.type or u.type or strategies.unspecified;
            loc = lk;
            __toString = _: showOption lk;
            declarations = [ file ] ++ (u.declarations or [ ]);
            declarationPositions = [
              (builtins.unsafeGetAttrPos k (options prefix))
            ]
            ++ (u.declarationPositions or [ ]);
            definitionsWithLocations = o.defs;
            definitions = map (x: x.value) o.defs;
            files = map (x: x.file) o.defs;
            isDefined = o.defs != [ ];
            highestPrio = o.prio;
            inherit (o) value;
            options = [ ];
            valueMeta = throw "gen-merge: the option `${showOption lk}' does not answer `valueMeta': it is the reference engine's v2-merge metadata, whose records carry that engine's own type objects and evaluations";
          };
      in
      if isOptLeaf user then
        served
      else
        served
        // {
          _module = user // mapAttrs (k: _: record k (options prefix).${k}) moduleOwnDecls;
        };
    # The same four declarations on the stratum-1 door's tree (`declaredOptions`), whose records are
    # declarations whose evaluated keys refuse by name (`unansweredOptionKeys`), so the two
    # publications agree on the declared key set.
    stamp =
      prefix: stamped:
      let
        user = stamped._module or { };
      in
      if isOptLeaf user then
        stamped
      else
        stamped
        // {
          _module =
            user
            // mapAttrs (
              k: _:
              let
                lk = prefix ++ [
                  "_module"
                  k
                ];
                u = user.${k} or { };
              in
              {
                _type = "option";
              }
              // (options prefix).${k}
              // u
              // unansweredOptionKeys
              // {
                loc = lk;
                __toString = _: showOption lk;
                declarations = [ file ] ++ (u.declarations or [ ]);
              }
            ) moduleOwnDecls;
        };
    # A key's surviving definitions as nixpkgs' option reads them: discharged, override-filtered,
    # each `{ file; value; }`, with the priority that survived (`null` for none, nixpkgs' 9999).
    winners =
      defs:
      let
        w = filterOverrides (
          concatMap (d: map (x: x // { inherit (d) file; }) (dischargeProperties d.value)) defs
        );
      in
      {
        defs = map (x: { inherit (x) file value; }) w;
        prio = if w == [ ] then 9999 else (head w).priority;
      };
  };
  # The declarations of an engine-owned `_module.<k>` an evaluation's modules state, in authored order,
  # each `{ file; decl; }`. A `_module` group declares them as `options._module.<k>` leaves
  # (`sitesAt`). A `submodule`-typed `_module` leaf declares them inside its submodule, which nixpkgs
  # merges with its own `_module` options, so they are read off the leaf type's sub-options, one
  # merged record named by the files that declared the leaf (`interface.moduleLeafSubOptions`). A
  # record nixpkgs has already judged against its own declarations carries `judged`.
  # A gen `submodule` leaf's sub-options are read off its DECLARATIONS (the stratum-1 door over its
  # own modules and arguments), never its served records: a served record states `unspecified` for a
  # declaration that states no type (`serveOptions`, nixpkgs' `fixupOptionType`), which an explicit
  # `type = unspecified` cannot be told from, and the judge asks what was declared. A nixpkgs leaf is
  # judged by nixpkgs (`interface.moduleLeafSubOptions`).
  moduleLeafSubOptions =
    t: loc:
    if t ? carries && t ? nests then
      {
        judged = false;
        options = declaredOptions {
          prefix = loc;
          inherit (t.nests) specialArgs;
        } (t.nests.modules ++ [ namePlaceholder ]);
      }
    else
      interface.moduleLeafSubOptions moduleOwnDecls t loc;
  moduleOwnSites =
    sitesAt: prefix: allOptions: leafSub: k:
    let
      m = allOptions._module;
      leafFiles = map (s: s.file) (sitesAt (prefix ++ [ "_module" ]));
      sub = if leafSub != null then leafSub else moduleLeafSubOptions m.type (prefix ++ [ "_module" ]);
    in
    if !(isOptLeaf m) then
      if m ? ${k} && !(isOptLeaf m.${k}) then
        [
          {
            file = concatStringsSep ", " (
              prelude.unique (
                map (s: s.file) (
                  concatMap (
                    n:
                    sitesAt (
                      prefix
                      ++ [
                        "_module"
                        k
                        n
                      ]
                    )
                  ) (attrNames m.${k})
                )
              )
            );
            decl = m.${k};
          }
        ]
      else
        sitesAt (
          prefix
          ++ [
            "_module"
            k
          ]
        )
    else if (m.type.name or null) != "submodule" || (sub.options.${k} or null) == null then
      [ ]
    else
      [
        {
          file = concatStringsSep ", " leafFiles;
          decl = sub.options.${k};
          inherit (sub) judged;
        }
      ];
  # A module re-declaring an engine-owned `_module.<k>`, judged as nixpkgs' `mergeOptionDecls` judges
  # it where the engine's own declaration takes part: refused by name when a declared type does not
  # merge with the engine's own, or when a declaration states a field the engine's own states
  # (`moduleOwnDecls`). Between two modules' declarations the non-type fields right-bias, as every
  # redeclaration in this engine does (ADR-0029's ordered fold, owner-ruled on den-hoag-00g), so two
  # `apply`s keep the later one; nixpkgs refuses that pair.
  #
  # Of what an accepted re-declaration may carry, nixpkgs reads `apply` and `readOnly` into a value,
  # and at `specialArgs` (which declares no type of its own) a `type`. This engine runs `apply` where
  # it reads the key itself (`moduleArgs`, `freeform`, `moduleOwnSpecialArgs`), a `type` at
  # `specialArgs` there too, and `readOnly` here: nixpkgs' own module defines `args`, and both its
  # own `freeformType` default and a re-declaration's `default` count as definitions, so a second one
  # refuses; at `specialArgs` the engine's is the only definition a module can make. At `check` the
  # engine runs neither, so a re-declaration carrying one is refused by name, never dropped. An owned
  # key declared as a group of options would be the parent of options its own type cannot carry, and
  # is refused as nixpkgs refuses it.
  moduleOwnRedeclared =
    {
      sites,
      loc,
      pushed,
      freeformDeclared,
    }:
    k:
    let
      own = moduleOwnDecls.${k};
      files = concatStringsSep ", " (map (s: s.file) sites);
      group = filter (s: !isOptLeaf s.decl) sites;
      # A record nixpkgs has judged against its own declarations already (`judged`) states theirs too.
      unjudged = filter (s: !(s.judged or false)) sites;
      unread =
        filter (f: any (s: s.decl ? ${f} && (f != "readOnly" || s.decl.readOnly)) sites)
          {
            args = [ ];
            freeformType = [ ];
            check = [
              "apply"
              "readOnly"
            ];
            specialArgs = [ ];
          }
          .${k};
      defined =
        if !(any (s: s.decl.readOnly or false) sites) then
          [ ]
        else if k == "args" then
          map (p: p._file) (
            filter (p: p.attrs ? _module && (pushDownProperties p.attrs._module) ? args) pushed
          )
          ++ map (s: s.file) (filter (s: s.decl ? default) sites)
        else if k == "freeformType" then
          map (c: c._file) freeformDeclared
        else
          [ ];
    in
    if group != [ ] then
      throw "gen-merge: the option `${showOption loc}' is the engine's own, and its type does not support nested options, so it cannot be the parent of `${
        concatStringsSep "', `" (map (n: showOption (loc ++ [ n ])) (attrNames (head group).decl))
      }'; declared in ${files}"
    else if
      !all (s: interface.moduleOwnTypeAdmits k s.decl.type) (filter (s: s.decl ? type) unjudged)
      || any (f: any (s: s.decl ? ${f}) unjudged) (attrNames own)
    then
      throw "gen-merge: the option `${showOption loc}' in ${
        concatStringsSep ", " (map (s: "`${s.file}'") sites)
      } is already declared by the engine's own `_module' options"
    else if unread != [ ] then
      throw (
        "gen-merge: `${showOption loc}' is read only from `evalModuleTree { check = …; }'"
        + ", so a module's ${
          concatStringsSep ", " (map (f: "`${f}'") unread)
        } on it would not run; declared in ${files}"
      )
    else if defined != [ ] then
      throw "gen-merge: the option `${showOption loc}' is read-only, but it is defined more than once (the engine defines it too); defined in ${concatStringsSep ", " (prelude.unique defined)}"
    else
      null;
  # Each engine-owned `_module.<k>` an evaluation's modules declare, judged; `realized` reads it only
  # on the branches where a module declares `options._module`.
  moduleOwnJudged =
    sitesAt: prefix: allOptions: leafSub: pushed: freeformDeclared: k:
    moduleOwnRedeclared {
      sites = moduleOwnSites sitesAt prefix allOptions leafSub k;
      loc = prefix ++ [
        "_module"
        k
      ];
      inherit pushed freeformDeclared;
    } k;
  # An accepted re-declaration's `apply`, the last one stated (the ordered fold), or the identity.
  moduleOwnApply =
    sites:
    let
      a = filter (s: s.decl ? apply) sites;
    in
    if a == [ ] then x: x else (prelude.last a).decl.apply;
  # The `_module.args` of an evaluation whose modules declare `options._module`: the modules' own
  # sets merged (`mergeModuleArg`), with the position's `name` (`positionNameOf`) where the
  # evaluation is positioned, as nixpkgs' `submoduleWith` defines it there, and then mapped by an
  # accepted `apply` (`moduleOwnApply`). So the `name` its modules receive is the applied set's.
  moduleOwnArgs =
    positioned: prefix: sites: pushed:
    let
      stated = builtins.zipAttrsWith mergeModuleArg (moduleArgSetsOf pushed);
    in
    moduleOwnApply sites (
      if positioned then stated // { name = positionNameOf prefix stated pushed; } else stated
    );
  # The `_module.specialArgs` a module reads where its evaluation's modules declare `options._module`:
  # the caller's set, as nixpkgs' `internalModule` defines it, merged through a re-declared `type`
  # (the last one stated, the ordered fold) and mapped by an accepted `apply`. Only the read changes:
  # the arguments every module is applied to stay the caller's set, as in nixpkgs.
  moduleOwnSpecialArgs =
    loc: sites: specialArgs:
    let
      typed = filter (s: s.decl ? type) sites;
    in
    moduleOwnApply sites (
      if typed == [ ] then
        specialArgs
      else
        mergeOption loc { inherit ((prelude.last typed).decl) type; } [
          {
            file = "<gen-merge>";
            value = specialArgs;
          }
        ]
    );
  moduleDefOf =
    file: attrs:
    if !(attrs ? _module) then attrs else moduleRest file attrs (pushDownProperties attrs._module);
  moduleRest =
    let
      # the two keys this engine reads itself; `check` stays a config path (`moduleOwnKeys`)
      readKeys = [
        "args"
        "freeformType"
      ];
    in
    file: attrs: m:
    if !isAttrs m then
      throw "gen-merge: `_module' must be an attribute set, and this one is ${builtins.typeOf m}; defined in ${file}"
    else if m ? specialArgs then
      throw "gen-merge: `_module.specialArgs' is set by the caller, never by a module: pass it as `evalModuleTree { specialArgs = …; }'; defined in ${file}"
    else if builtins.removeAttrs m readKeys == { } then
      builtins.removeAttrs attrs [ "_module" ]
    else
      attrs // { _module = builtins.removeAttrs m readKeys; };
  moduleSyntaxChecked =
    e:
    let
      m = e.content;
    in
    if m ? disabledModules then
      throw "gen-merge: module `${e._file}' sets `disabledModules'. gen-merge does not implement module removal (it is deferred work): the modules it names would stay enabled here, where the reference module system removes them. Remove the key; it is refused by presence, an empty list included."
    else if e.reserved or null != null && isAttrs m && reservedHits e != [ ] then
      throw "${e.reserved.names.${head (reservedHits e)}} (module `${e._file}')"
    else if (m ? config || m ? options) && builtins.removeAttrs m structuredKeys != { } then
      throw "gen-merge: module `${e._file}' has an unsupported attribute `${head (attrNames (builtins.removeAttrs m structuredKeys))}'. A module carrying a top-level `config' or `options' reads only the module keys; move ${concatStringsSep ", " (attrNames (builtins.removeAttrs m structuredKeys))} into its explicit `config', or drop `config'/`options' and write every configuration key at the top level."
    else if (m ? __keyEq || (e.m0.__keyEq or null) != null) && !(m ? key) then
      throw "gen-merge: module `${e._file}' publishes a key comparison (`__keyEq') but no `key'. The comparison decides between two occurrences of one key, so a module without a key has nothing for it to decide: give the module its `key', or remove `__keyEq'."
    else if isAttrs m then
      e
    else
      throw "gen-merge: module `${e._file}' is a function whose result is ${builtins.typeOf m}, not an attribute set. A module function is applied once, to the module arguments, and must return the module itself; a function that returns another function (`a: b: { … }`) is not a module.";
  # THE RESERVATION SCOPE (`__reservedKeys`, den-hoag-8x97u). A module carrying
  # `__reservedKeys = { names = { <name> = <refusal text>; … }; exempt = [ <attribute path> … ]; }`
  # reserves those names in every module it IMPORTS, through every route the collector follows
  # (nested `imports`, `require`, function and functor modules read after application, paths). The
  # marked module's own top level is not checked: a library marking a module checks that level
  # itself, so each write meets one door. The scope is an inherited attribute (`reserved`) along the
  # import edge, as `_file` is, so it belongs to a module's FIRST occurrence in import order: a module
  # already reached outside any scope is not re-checked when a scoped module imports it again. A
  # nested `__reservedKeys` replaces the inherited one for its own closure. A module carrying every
  # `exempt` path is not checked (gen-schema exempts the kind shape its `inherits` alias reads). The
  # content is plain data supplied by the library that owns the names; gen-merge names no kind and no
  # formal. A reserved name is never a module key, so one key read serves both forms; only a property
  # root (`mkIf c { … }` as a whole module) needs the push-down. A malformed marker is refused by
  # name on the first module it scopes, never read as an empty reservation.
  #
  # TWO CARRIERS, one scope (den-hoag-r05lc). The marker is read off the module's content, and else
  # off the RECORD of a `__functor` module, its unapplied value: `{ __functor = …; __reservedKeys = …; }`
  # scopes the closure of what the functor returns. The record is the carrier for a module another
  # evaluator may also read: nixpkgs applies a functor and reads only its result, so the marker never
  # reaches the module it collects, where a content-level `__reservedKeys` is an unsupported attribute
  # (structured) or a configuration key (shorthand).
  hasAttrPath =
    p: v: p == [ ] || (isAttrs v && v ? ${head p} && hasAttrPath (builtins.tail p) v.${head p});
  reservedHits =
    e:
    let
      m = e.content;
      r = e.reserved;
      names = r.names or null;
      exempt = r.exempt or [ ];
    in
    if
      isAttrs names
      && all builtins.isString (builtins.attrValues names)
      && builtins.isList exempt
      && all (p: builtins.isList p && all builtins.isString p) exempt
    then
      (
        if exempt != [ ] && all (p: hasAttrPath p m) exempt then
          [ ]
        else
          filter (k: names ? ${k}) (attrNames (if m ? _type then pushDownProperties (configOf e) else m))
      )
    else
      throw "gen-merge: module `${e._file}' is imported under a malformed `__reservedKeys': ${
        if !(isAttrs r) then
          "it is a ${builtins.typeOf r}"
        else if !(isAttrs names) then
          (if r ? names then "its `names' is a ${builtins.typeOf names}" else "it has no `names'")
        else if !(all builtins.isString (builtins.attrValues names)) then
          "its `names.${
            head (filter (k: !(builtins.isString names.${k})) (attrNames names))
          }' is not a refusal text"
        else
          "its `exempt' is not a list of attribute paths"
      }. The key is { names = { <name> = <refusal text>; … }; exempt = [ <attribute path> … ]; }: `names' maps each reserved name to the text its refusal throws, and the optional `exempt' lists attribute paths (lists of strings) that exempt a module carrying them all.";
  importsOf =
    m:
    let
      i = m.imports or [ ];
    in
    if m ? require && !(isStructured m) then
      m.require ++ (if isList i then i else [ i ])
    else if isList i then
      i
    else
      [ i ];
  topFreeformOf = m: m.freeformType or null;

  # ── WHAT AN EVALUATION DERIVES FROM ITS MODULE CLOSURE, AS FUNCTIONS OF `flat` ────────────────
  # The evaluation body binds each of these over its own `flat`; a reader OUTSIDE the body (the
  # published `options`' stamp, the tree-as-a-type's freeform datum) applies the same function to
  # the `flat` the body publishes. One definition, two applications, so the two cannot disagree, and
  # no evaluation result carries a field only those readers need: a field on the body is paid by
  # every child evaluation (the hub perf-bench's deepSubmodule alloc row prices it).
  #
  # Config attrsets (shorthand-aware), config-root properties pushed to keys. Every config read
  # forces this for every entry, so it is where the module-syntax refusals fire.
  #
  # Each is spelled as the per-entry function the body maps, never as a wrapper over the list: a
  # call per evaluation is an environment per evaluation, which the same row prices.
  pushedEntry = e: {
    inherit (e) _file;
    attrs = pushDownProperties (configOf e);
  };
  # Each module's options root, beside the file that declared it and its position in the fold.
  declEntry = i: e: {
    idx = i;
    file = e._file;
    options = optionsOf e.content;
  };
  # The freeform declarations by KEY, value unforced: a top-level `freeformType` and each module's
  # `_module.freeformType`, one entry per contribution.
  topFreeformEntry = e: {
    inherit (e) _file;
    type = topFreeformOf e.content;
  };
  hasTopFreeform = e: e.content ? freeformType;
  moduleFreeformEntries =
    p:
    optional (p.attrs ? _module && (pushDownProperties p.attrs._module) ? freeformType) {
      inherit (p) _file;
      type = (pushDownProperties p.attrs._module).freeformType;
    };
  # The resolved freeform type (the body's `freeform` states the rule it follows).
  resolvedFreeform =
    freeformDeclared:
    let
      candidates = filter (c: c.type != null) freeformDeclared;
      # `dischargeProperties` is shared with the value-path def folds (`mergeDefsWith`,
      # `mergeDefsRichWith`) and emits `{ priority; value; }`, so the originating file is
      # paired back on HERE rather than grown as a field there.
      winners = filterOverrides (
        concatMap (c: map (d: d // { inherit (c) _file; }) (dischargeProperties c.type)) candidates
      );
    in
    if winners == [ ] then
      null
    else
      mergeTypeDefs "the freeform type" (
        map (w: {
          file = w._file;
          inherit (w) value;
        }) winners
      );
  # nixpkgs' `types.optionType.merge`, read over an AUTHORED list (first module first): one
  # definition is its own type, several merge through the declaration type-merge
  # (`mergeDeclaredTypes`, the last authored deciding), and a pair that does not merge is refused by
  # name, its files in authored order. The freeform winners arrive authored. `types.optionType`'s
  # fold is handed its definitions last module first, as every type's merge is, and reverses them
  # before calling this (lib/types.nix), so both readers fold one list one way.
  mergeTypeDefs =
    what: defs:
    if length defs == 1 then
      (head defs).value
    else
      let
        decided = mergeDeclaredTypes (map (d: d.value) defs);
      in
      if decided ? merged then
        decided.merged
      else
        throw "gen-merge: ${what} is defined with types that do not merge (${declaredRefusalText decided}); defined in ${
          concatStringsSep ", " (map (d: d.file) defs)
        }";

  # ── source-class classifier (design spec §0.3 / §3) ────────────────────────
  # Tag a module with the CLASS of its PRE-application source. The class is decided on `m0` (before
  # `callM`), because `callM` applies function and `__functor` modules with the WHOLE
  # `specialArgs // extra` set — nixpkgs application semantics, which byte-mode keeps — so any function
  # module can reach `config` regardless of its visible formals, and the post-application content is
  # always a plain attrset that no longer reveals whether config was reachable.
  #
  # Consequently `builtins.functionArgs` CANNOT prove a function module clean: `args@{ genSchema, ... }:
  # args.config` reports only `genSchema` yet the `@`-binding captures the full argument set, and a bare
  # lambda (`args: args.config`) reports `{ }` — either reads `config` despite its visible formals. So a
  # function module is DIRTY BY DEFAULT; `pureModule` is the author's explicit clean assertion (§5).
  #
  # WHY CLEANLINESS IS DECLARED, NOT DERIVED (ADR-0013: a dependence fact is derived unless derivation
  # is proven impossible, and the proof names what would have to change). "This module reads no
  # fixpoint value" is a dependence fact, and under the whole-set application above it is sealed
  # inside a closure: which attributes of its argument a function body reads is not observable before
  # it runs, and after `callM` the content no longer shows whether `config` was reachable. So the
  # classifier takes the conservative verdict, and the only clean verdict a function can get is the
  # one its author DECLARES with `pureModule` — trusted, never checked.
  # WHAT WOULD HAVE TO CHANGE for the fact to become derivable: apply a function module with ONLY its
  # named formals (`intersectAttrs (functionArgs m) args`) instead of the whole set. A hidden read —
  # `args@{ … }: args.config`, or a bare lambda — then fails loudly (`attribute 'config' missing`)
  # instead of silently seeing `config`, so the formals become the complete read set: a module whose
  # formals name no fixpoint-derived argument is clean BY DERIVATION, and `pureModule` is checked
  # rather than trusted. The price is nixpkgs application parity for `args@`-capturing and bare-lambda
  # modules in whatever scope adopts it, which is why the whole-set application stands.
  #   • attrset (no `__functor`, no `__pureModule`)  → "attrset"   — no body, cannot read anything.
  #   • path                                          → import it, classify the RESULT.
  #   • `__pureModule`-marked wrapper                 → "marked-pure" — tags THIS entry only; the
  #                                                     module's own `imports` classify independently.
  #   • everything else (functions, bare lambdas,     → "dirty".
  #     `__functor` attrsets without the marker)
  classifyModule =
    m0:
    if builtins.isPath m0 then
      classifyModule (import m0)
    else if isAttrs m0 then
      if m0 ? __pureModule then
        "marked-pure"
      else if m0 ? __functor then
        "dirty"
      else
        "attrset"
    else
      "dirty";

  # pureModule (design spec §3 / §5) — the author's clean-module assertion. Wraps a function module in
  # the marker attrset `classifyModule` reads BEFORE `callM` applies it (`callM` applies `__functor`
  # attrsets, so a bare function's cleanliness would be invisible post-application). Contract (§5): the
  # wrapped function reads ONLY its declared formals and EVERY formal resolves from `specialArgs` — the
  # engine TRUSTS the marker. HAZARD (non-local): a formal is unsafe if another module can shadow its
  # NAME into `_module.args`, making it fixpoint-derived rather than specialArgs-sourced — a lying marker
  # then reuses stale values silently (README §pureModule spells out the blast radius). The marker is a
  # DECLARED dependence fact because the engine cannot derive it; the argued impossibility, and the
  # named-formals application that would make it derivable, are stated at `classifyModule`. The tag
  # classifies this wrapper's own content entry marked-pure; entries reached through the module's
  # `imports` classify independently.
  pureModule = f: {
    __pureModule = true;
    __functor = self: f;
  };

  # ── THE MODULE GRAPH (den-hoag-470xp, arm F) ────────────────────────────────────────────────────
  # Module imports are graph edges and a module is a node; a diamond is two edges into one node, so a
  # module imported twice contributes once by construction. Node identity is nixpkgs' key rule, split
  # into two namespaces: an explicit `key` and a path module's identity (its own `key`, else its path)
  # share the group `key` (a key that spells a path IS that path's module), and an anonymous module is the group `anon`, keyed
  # `<importer's id>:anon-<n>` (1-based; the importer is the tree itself at the top level). The anon
  # rule is compositional, since an anonymous module under a shared node is itself shared, and
  # injective, since a minted id is length-prefixed. An explicit key spelled like an anonymous one
  # stays apart from it, where nixpkgs merges the two: a named byte-mode boundary (README).
  #
  # A module is identified by its applied result's `key`; a path module without one by its path, as
  # nixpkgs' `unifyModuleSyntax` (`key = toString m.key or key`, the path for a path module). A lambda
  # carries no identity (ADR-0034): the key is data read off the applied result.
  #
  # THE CLOSURE KEYS BY A LOCAL SPELLING OF THAT IDENTITY, and mints only when the graph is read. The
  # merge path needs identity to decide which occurrence is a node and never reads a node, so it pays
  # no minted id: `moduleKeyOf` spells the group as the first character (`k` for the key group, `a`
  # for an anonymous module) and an anonymous module as `a<importer's spelling>:<n>`, the top-level
  # importer spelled `""` and `<n>` 0-based. It is injective by the same argument: the first character separates the
  # groups, and an anonymous spelling reads back as its importer's spelling and `<n>` (digits after
  # the last `:`). So it is a bijection with the minted ids within one tree, and `moduleNodeId` is the
  # map, applied by the family alone (`moduleFamily`).
  #
  # THE SPELLING IS CONTEXT-FREE, deliberately. A string path `"${input}/modules/x.nix"` carries the
  # context of the store path it names, and a key is an identity (it becomes an attribute name and an
  # id segment, both of which refuse a context-carrying string uncatchably). Discarding it is sound
  # here because the context only records that the key's text names a store path the key already
  # holds as text: the spelling is the path, the same as the equivalent path value's `toString`.
  moduleKeyOf =
    importer: i: m0: m:
    if builtins.isPath m0 || isPathString m0 then
      "k" + builtins.unsafeDiscardStringContext (toString (m.key or m0))
    else if isAttrs m && m ? key then
      "k" + builtins.unsafeDiscardStringContext (toString m.key)
    else
      "a" + importer.key + ":" + toString i;
  moduleIdOf =
    treeId: group: key:
    scope.mintNtaId {
      host = treeId;
      name = "modules";
      inherit group key;
    };
  # An element's `nta` coordinates in its tree, and its minted id. An anonymous module's key names
  # its importer's minted id, which is the element that reached it (`importer`), or the tree.
  moduleCoords =
    treeId: e:
    if builtins.substring 0 1 e.key == "k" then
      {
        group = "key";
        key = builtins.substring 1 (builtins.stringLength e.key) e.key;
      }
    else
      {
        group = "anon";
        key = "${
          if e.importer.key == "" then treeId else moduleNodeId treeId e.importer
        }:anon-${toString (e.i + 1)}";
      };
  moduleNodeId =
    treeId: e:
    let
      c = moduleCoords treeId e;
    in
    moduleIdOf treeId c.group c.key;

  # THE IDENTITY-KEYED CLOSURE, the graph's own: one level of it is the modules one importer names,
  # each applied through the caller's `callM`, as the element the closure keys (`moduleKeyOf`).
  # `importer` and `i` locate the element for its minted id; `next` is its imports' elements. It is
  # built only where the graph is read (the family) or where the warm path needs a node's origin; the
  # merge path collects by `moduleClosure` below, which keeps the same order and the same nodes.
  moduleLevel =
    callM: importer: mods:
    prelude.imap0 (
      i: m0:
      let
        m = callM m0;
        self = {
          key = moduleKeyOf importer i m0 m;
          inherit importer i m0;
          next = moduleLevel callM self (importsOf m);
        };
      in
      self
    ) mods;
  # A tree's closure's top: the tree as importer, holding the tree's own module list (`roots`, its
  # import edges, a module named twice included).
  moduleTop =
    callM: mods:
    let
      top = {
        key = "";
        roots = moduleLevel callM top mods;
      };
    in
    top;
  # The closure from a start set: ONE `genericClosure`, a FIFO work list, so it is breadth-first,
  # imports are yielded in declaration order and the first occurrence reached wins, as nixpkgs'
  # `filterModules`. A losing occurrence takes its imports with it. The done-set is the finite set of
  # node keys, so a keyed or path import cycle closes (nixpkgs overflows there: a named byte-mode
  # boundary). Data that mints fresh keys without bound is non-well-founded and still diverges.
  closeModules =
    startSet:
    builtins.genericClosure {
      inherit startSet;
      operator = e: e.next;
    };

  # ── THE MERGE PATH'S COLLECTION: the same closure, over entries ──────────────────────────────────
  # `moduleClosure callM mods` — every module a tree reaches, one entry `{ m0; _file; content; }` per
  # node, in the closure's order: breadth-first, the first occurrence reached winning. `flat` IS this
  # list, so the module set folded equals the node set minted.
  #
  # An anonymous module never shares a node: its identity is its importer's and its position, and an
  # importer is expanded once. So the only occurrences that can lose are keyed and path ones, and
  # the merge path spells a node key for those alone (`nodeKeyOf`, the key group of `moduleKeyOf`),
  # strictly, where a level holds one. A level with none keeps every entry. A PLAIN LIST, with no
  # path and no module naming `imports`, `require` or `key`, is its own closure, and most trees are
  # one (a submodule's own module and its definitions): it is collected as its entries alone.
  #
  # `_file` is an INHERITED attribute along the import edge that reached the node FIRST (Knuth 1968):
  # the importer's resolved file flows down, and a node's own attribution overrides it. Precedence,
  # most specific first: a raw path leaf's own `_file` (the applied `m`; `m._file or m0` falls through
  # to the path for a non-attrset), else its path string (nixpkgs' `unifyModuleSyntax`: `toString
  # m._file or file`), then the entry's own `_file` (pre-application `m0`, then the applied `m`), then
  # the importer's file, then `"<unknown-file>"` at the root (nixpkgs' `unknownModule`, the label
  # `evalModules` gives an anonymous top-level module). Every arm is a string: a `_file` given as a
  # path value is `toString`ed at this one origin, so an inherited child's file is a string because its
  # importer's is (nixpkgs' `toString m._file or file`). So content passed through an unattributed
  # wrapper (`setDefaultModuleLocation F m` = `{ _file = F; imports = [ m ]; }`) is attributed to its
  # IMPORT site `F`, as nixpkgs'
  # `collectStructuredModules` threads `parentFile`. A path module is never attributed to its
  # importer: its own `_file` (a function path module's applied result included), else its path.
  # `_file` stays a thunk, forced only when a file surface is read. An
  # entry's source class is decided on the PRE-application `m0` (design spec §3) where it is read
  # (`srcClassOf`), so collecting a module pays nothing for it.
  #
  # The reservation scope (`reserved`, see `reservedHits`) rides the same edge: an entry carries it
  # only when its importer is scoped, from the importer's own `__reservedKeys` or else the importer's
  # `reserved`. `moduleEntries` takes the importer ENTRY (null at the root) rather than its file, and
  # an off-scope entry is the same three-field record as before, with no `reserved` field: the
  # off-scope path allocates nothing per entry (measured on the hub perf bench, whose
  # `deepSubmodule` alloc gate rejects one added argument or let slot here).
  moduleEntries =
    callM: importer: mods:
    map (
      m0:
      let
        m = callM m0;
      in
      if importer == null then
        {
          inherit m0;
          _file =
            if builtins.isPath m0 || isPathString m0 then
              toString (m._file or m0)
            else
              toString (m0._file or (m._file or "<unknown-file>"));
          content = m;
        }
      else if
        (importer.m0.__reservedKeys or (importer.content.__reservedKeys or (importer.reserved or null)))
        == null
      then
        {
          inherit m0;
          _file =
            if builtins.isPath m0 || isPathString m0 then
              toString (m._file or m0)
            else
              toString (m0._file or (m._file or importer._file));
          content = m;
        }
      else
        {
          inherit m0;
          _file =
            if builtins.isPath m0 || isPathString m0 then
              toString (m._file or m0)
            else
              toString (m0._file or (m._file or importer._file));
          content = m;
          reserved = importer.m0.__reservedKeys or (importer.content.__reservedKeys or importer.reserved);
        }
    ) mods;
  # A node key is an attribute name, which may carry no string context: a path module's store path
  # (or a key computed from one) names its node, and the context is not part of the name.
  nodeKeyOf =
    { m0, content, ... }:
    if builtins.isPath m0 || isPathString m0 then
      "k" + builtins.unsafeDiscardStringContext (toString (content.key or m0))
    else if isAttrs content && content ? key then
      "k" + builtins.unsafeDiscardStringContext (toString content.key)
    else
      null;
  # THE KEY COMPARISON (`__keyEq = { subject; decide; }`, den-hoag-kind-generator-collision-d4gnx).
  # `keyedDrop w x` decides an occurrence `x` whose node key the kept entry `w` already holds: `false`
  # drops it. Where neither publishes `__keyEq`, nixpkgs' key rule holds and `x` is dropped. Where
  # either does, the pair is decided, the same in both orders (ADR-0022) wherever both publish one
  # symmetric `decide`, since the kept entry's is applied: only one publishing is refused,
  # `decide w.subject x.subject` true is the one module, and false or a non-boolean is
  # refused by name; a throw inside `decide` propagates. Two occurrences of one spelled path are the one
  # file, so they keep nixpkgs' rule and neither content is read; two different path files sharing an
  # in-file key, or a path sharing its key with a content module, are decided like any other pair. The key is read off the node key, because a path's content
  # need carry no `key`. Bound here, never per level: `moduleLevels` runs once per level of every tree.
  isPathModule = m0: builtins.isPath m0 || isPathString m0;
  keqOf = e: e.content.__keyEq or (e.m0.__keyEq or null);
  keyedDrop =
    w: x:
    let
      key = builtins.substring 1 (builtins.stringLength x.k) x.k;
    in
    if isPathModule x.e.m0 && isPathModule w.e.m0 && toString x.e.m0 == toString w.e.m0 then
      false
    else if keqOf w.e == null && keqOf x.e == null then
      false
    else if keqOf w.e == null || keqOf x.e == null then
      throw "gen-merge: modules `${w.e._file}' and `${x.e._file}' share the key '${key}', and only `${
        if keqOf w.e != null then w.e._file else x.e._file
      }' publishes a key comparison (`__keyEq'). One key is one declaration: publish the comparison on both, or give them different keys."
    else
      let
        same = (keqOf w.e).decide (keqOf w.e).subject (keqOf x.e).subject;
      in
      if same == true then
        false
      else if same == false then
        throw "gen-merge: modules `${w.e._file}' and `${x.e._file}' share the key '${key}' and are not equal under its key comparison (`__keyEq'). One key is one declaration: give them different keys, or import one of them."
      else
        throw "gen-merge: the key comparison (`__keyEq.decide') of key '${key}' returned ${builtins.typeOf same}, not a boolean. `decide' answers whether two occurrences of one key are one module: true or false.";
  moduleLevels =
    callM: seen: level:
    if level == [ ] then
      [ ]
    else
      let
        keyed = any (e: nodeKeyOf e != null) level;
        at = prelude.imap0 (p: e: {
          inherit p e;
          k = nodeKeyOf e;
        }) level;
        # `listToAttrs` keeps a name's FIRST occurrence: the level's first entry per node key
        first = listToAttrs (
          concatMap (
            x:
            if x.k == null then
              [ ]
            else
              [
                {
                  name = x.k;
                  value = x;
                }
              ]
          ) at
        );
        kept =
          if keyed then
            map (x: x.e) (
              filter (
                x:
                x.k == null
                || (
                  if seen ? ${x.k} || first.${x.k}.p != x.p then keyedDrop (seen.${x.k} or first.${x.k}) x else true
                )
              ) at
            )
          else
            level;
      in
      kept
      ++ moduleLevels callM (if keyed then seen // first else seen) (
        concatMap ({ content, ... }@e: moduleEntries callM e (importsOf content)) kept
      );
  moduleClosure =
    callM: mods:
    let
      plain = moduleEntries callM null mods;
    in
    if
      all (m0: !(builtins.isPath m0 || isPathString m0)) mods
      && all (e: !(e.content ? imports || e.content ? require || e.content ? key)) plain
    then
      plain
    else
      moduleLevels callM { } plain;
  # An entry's source class: a hand-built entry states it, a collected one is classified on demand.
  srcClassOf = e: e.srcClass or (classifyModule e.m0);

  # THE TWO COLLECTIONS AGREE, checked node by node where the graph is read (never on a merge):
  # `flat` (the merge path's level walk) and the identity-keyed `genericClosure` are argued to be the
  # same nodes in the same order, and a graph reader pairs them by index, so every index is checked
  # before it is paired: the same group, the same node key on the key group, and the same source
  # shape (a path's string, an attrset's names, else its type). `alignedGraph` returns the graph or
  # refuses by name, naming the first index that disagrees.
  moduleShape =
    m0:
    if builtins.isPath m0 || isPathString m0 then
      "p" + builtins.unsafeDiscardStringContext (toString m0)
    else if isAttrs m0 then
      "a" + concatStringsSep "," (attrNames m0)
    else
      builtins.typeOf m0;
  alignedGraph =
    what: flat: graph:
    let
      n = length flat;
      agrees =
        i:
        let
          e = builtins.elemAt flat i;
          g = builtins.elemAt graph i;
          k = nodeKeyOf e;
        in
        (if k == null then builtins.substring 0 1 g.key == "a" else k == g.key)
        && moduleShape e.m0 == moduleShape g.m0;
      bad = filter (i: !(agrees i)) (prelude.genList (i: i) n);
    in
    if length graph != n then
      throw "gen-merge: ${what} reads ${toString (length graph)} module nodes where the tree collected ${toString n}; the two collections of one module set disagree"
    else if bad != [ ] then
      throw "gen-merge: ${what} pairs module node ${toString (head bad)} with a different module than the tree collected there; the two collections of one module set disagree"
    else
      graph;

  # THE FAMILY a minting tree publishes (`nta.modules`): one child per closure entry, grouped by
  # namespace, minted only when the family is read. Its ids come from the identity-keyed closure
  # (`moduleTop`), paired with the merge path's entries by index after `alignedGraph` has checked
  # every index; its content is the merge path's own entry, shared rather than applied again. Each seed
  # addresses its entry's `m0` in the host attribute `definitions`, whose last list is the tree's
  # closure (`knotDefinitions`, after the nested family's lists); each position record
  # discriminates the node by data (`mode = "module"`, den-hoag-9d80v) and carries what the node
  # answers, off the host's record: its entry and the ids its imports identify to.
  moduleFamily =
    treeId: defIndex: flat: top:
    let
      graph = alignedGraph "the module family of `${treeId}'" flat (closeModules top.roots);
      n = length flat;
      indexed = prelude.genList (
        i:
        let
          g = builtins.elemAt graph i;
        in
        {
          inherit i g;
          e = builtins.elemAt flat i;
          c = moduleCoords treeId g;
        }
      ) n;
      groupOf =
        grp: f:
        listToAttrs (
          concatMap (
            x:
            if x.c.group == grp then
              [
                {
                  name = x.c.key;
                  value = f x;
                }
              ]
            else
              [ ]
          ) indexed
        );
      byGroup = f: {
        key = groupOf "key" f;
        anon = groupOf "anon" f;
      };
    in
    {
      roots = map (moduleNodeId treeId) top.roots;
      product = byGroup (x: [
        {
          attr = "definitions";
          def = defIndex;
          at = [
            x.i
            "m0"
          ];
        }
      ]);
      positions = byGroup (x: {
        mode = "module";
        member = null;
        inherit (x.e) _file content;
        srcClass = srcClassOf x.e;
        imports = map (moduleNodeId treeId) x.g.next;
      });
    };

  # ── warm re-eval decision layer (design spec §§1-2) ─────────────────────────
  # The opt-in warm path reuses the previous eval's declared-leaf values/provenance for locs PROVABLY
  # untouched by an edit (an appended module list) and re-merges the rest inside the normal fixpoint.
  # `warmDecide` is the PURE decision half (no splicing): given the flattened module list + the EDITED
  # tail-count + the merged decl tree, it builds the bipartite contribution relation (which declared
  # leaves an edit can perturb), the coarse freeform-reuse flag, and the disabledModules refusal, then
  # hands the relation to gen-memo (`memo.warmDecision`, ADR-0008 item 2) for the reuse DECISION.
  # `mergeTree` consumes the resulting `isClean` to gate per-leaf splicing (spec §2). Testable in
  # isolation through the core seam.

  # Declared LEAVES of ONE option-decl tree — walk to `isOptLeaf` (typed registries / scalar leaves
  # included; untyped groups recurse), each loc beside the DESCRIPTOR declared there. One descent
  # with two views: `declLeafPaths` below is its loc projection (the granularity of both the
  # footprint and the splice gate), and the deprecation report reads the same entries' descriptors.
  # Two descents would be two answers to "which locs are declared leaves" that can drift apart —
  # the same reason the portable-subset lint consumes the engine's own predicates rather than its
  # own copies. Only the SPINE is walked: an entry's `opt` is the descriptor thunk, unforced here.
  # `evalModuleTree`'s `declarationGuard` is the one second descent, and it is deliberate: routing
  # the guard through this list builds and forces a loc per declared leaf that nothing reads, and a
  # boolean walk over the same branches recovers that cost. The price is that the guard's depth is
  # its own; `ci/tests-error.nix` pins it with a key set read three groups down.
  declLeafEntries =
    tree:
    let
      go =
        loc: t:
        concatMap (
          k:
          let
            v = t.${k};
            lk = loc ++ [ k ];
          in
          if isOptLeaf v then
            [
              {
                path = lk;
                opt = v;
              }
            ]
          else if isAttrs v then
            go lk v
          else
            [ ]
        ) (attrNames t);
    in
    go [ ] tree;

  # Declared-leaf locs of ONE option-decl tree — the loc projection of the walk above.
  declLeafPaths = tree: map (e: e.path) (declLeafEntries tree);

  # DEF footprint of one module's config, guided by the merged decl tree — the lint's discharge-based
  # descent (lib/lint.nix `descend`), but recording PATHS, not order-probes: it pushes config-node
  # properties down at each DECLARED-GROUP level and STOPS at a declared leaf (records `onDecl = true`)
  # or an undeclared key (records `onDecl = false` — a freeform contribution). It NEVER forces a leaf
  # value — only the config SPINE (keys), bounded by the module's structural size (spec §2: acceptable,
  # a dirty/edited module re-merges anyway). A def landing on a declared GROUP that is not an attrset
  # (a type error the cold path would throw on) is conservatively recorded as `onDecl` rather than
  # descended, so the footprint stays total.
  moduleDefFootprint =
    allOptions: content:
    let
      descend =
        opts: loc: attrs:
        concatMap (
          k:
          let
            lk = loc ++ [ k ];
            v = attrs.${k};
          in
          if (opts ? ${k}) && !(isOptLeaf opts.${k}) then
            let
              pv = pushDownProperties v;
            in
            if isAttrs pv then
              descend opts.${k} lk pv
            else
              [
                {
                  onDecl = true;
                  path = lk;
                }
              ]
          else if opts ? ${k} then
            [
              {
                onDecl = true;
                path = lk;
              }
            ]
          else
            [
              {
                onDecl = false;
                path = lk;
              }
            ]
        ) (attrNames attrs);
      rootAttrs = moduleDefOf "<gen-merge>" (
        pushDownProperties (configOf {
          inherit content;
          _file = "<gen-merge>";
        })
      );
    in
    descend allOptions [ ] rootAttrs;

  # `warmDecide { flat; editedCount; allOptions }` — the reusability predicate as a footprint pass.
  #   • EDITED  = the tail-`editedCount` entries of `flat` (collectModules is concatMap + flatten
  #               distributes over ++, and the appended list is a strict suffix, so tail-k = the
  #               flattened edited entries — an EDITED attrset module is still edited, its defs re-merge).
  #   • CLEAN   = non-edited entries whose `srcClass` is attrset / marked-pure (config-independent).
  #   • DIRTY   = every other non-edited entry (`srcClass == "dirty"`).
  # The DIRTY FOOTPRINT = the union, over DIRTY ∪ EDITED entries, of decl paths (`declLeafPaths` of the
  # entry's own `options`) and def paths landing on declared leaves (`moduleDefFootprint`). A declared
  # leaf is REUSABLE iff it is OUTSIDE this set (spec §2 — outside it, both the decl set and the def set
  # at the loc come only from CLEAN modules, so the merge inputs are identical to the previous eval).
  # FREEFORM is coarse (soundness-forced, spec §2): reuse the whole prev freeform layer iff (a) NO
  # dirty/edited entry contributes an unmatched (freeform) def path AND (b) NO edited entry contributes
  # a freeformType candidate at EITHER site (top-level `freeformType` or `_module.freeformType`) — an
  # edited freeformType flips the priority-resolved winner and changes EVERY freeform loc while naming
  # none of them. disabledModules on any edited entry ⇒ refuse warm (it would disable a clean base
  # module invisibly to the footprint — the same failure shape). Each footprint record keeps a `reason`
  # for the decision trace (spec §4).
  #
  # `disabledRefusal` IS DEFENCE ONLY while module removal is refused: `moduleSyntaxChecked` refuses
  # any entry carrying `disabledModules` by presence, and `flat` is forced through `declarationGuard`
  # first, so this refusal is unreachable through `evalModuleTree` (a warm eval over such an edit
  # refuses its trace and its `.config` alike). It is kept because it becomes live again,
  # unchanged, the moment module removal is implemented, and the unit cells that build `flat` by hand
  # still reach it.
  warmDecide =
    {
      flat,
      editedCount,
      allOptions,
      # Same default as `evalModuleTree`'s own `warmFrom ? null` (spec §§1-2): a core-seam caller
      # testing the partition/footprint/freeform halves in isolation (`ci/tests/warm.nix`) need not
      # supply a prior — `verdict`/`isClean` stays an unforced thunk unless read.
      warmFrom ? null,
    }:
    let
      n = length flat;
      headLen = if n > editedCount then n - editedCount else 0;
      editedEntries = drop headLen flat;
      nonEdited = take headLen flat;
      isCleanEntry =
        e:
        let
          c = srcClassOf e;
        in
        c == "attrset" || c == "marked-pure";
      cleanEntries = filter isCleanEntry nonEdited;
      dirtyEntries = filter (e: !(isCleanEntry e)) nonEdited;

      # One entry's footprint + freeform contributions, reason-tagged (`reasonOf kind` — "decl"/"def").
      footOf =
        reasonOf: e:
        let
          # ★ THE SECOND DOOR, and it is a SECOND CALL SITE rather than a second copy of the guard.
          # This walk reads a module's OWN raw `options`, never `allOptions`, so the guard at the
          # `allOptions` fold does not reach it: a declared-but-never-defined misuse is invisible
          # here, because `moduleDefFootprint` below is DEFINITION-driven and never visits a
          # declared-only key. Measured, one fixture, three arms: reading `.warmDecision.remerged`
          # for such a module returns `{ }` silently both at HEAD and with the fold's guard alone,
          # and refuses by name only once this call site is guarded too (ci/tests-error.nix,
          # `test-warm-remerged-declared-only-misuse-refuses-by-name`).
          declPaths = map (p: {
            path = p;
            reason = reasonOf "decl";
          }) (declLeafPaths (validateDeclSubtree [ ] (optionsOf e.content)));
          df = moduleDefFootprint allOptions e.content;
          defPaths = concatMap (
            r:
            if r.onDecl then
              [
                {
                  inherit (r) path;
                  reason = reasonOf "def";
                }
              ]
            else
              [ ]
          ) df;
          free = concatMap (
            r:
            if r.onDecl then
              [ ]
            else
              [
                {
                  inherit (r) path;
                  reason = "freeform-dirty ${e._file}";
                }
              ]
          ) df;
        in
        {
          footprint = declPaths ++ defPaths;
          inherit free;
        };

      dirtyF = map (
        e: footOf (kind: if kind == "decl" then "dirty-decl ${e._file}" else "dirty-def ${e._file}") e
      ) dirtyEntries;
      editedF = map (e: footOf (_kind: "edited-def") e) editedEntries;
      allF = dirtyF ++ editedF;
      footprint = concatMap (x: x.footprint) allF;
      freeContribs = concatMap (x: x.free) allF;

      editedFreeformType = prelude.any (
        e:
        (topFreeformOf e.content != null)
        || ((pushDownProperties ((pushDownProperties (configOf e))._module or { })) ? freeformType)
      ) editedEntries;
      reuseAllFreeform = freeContribs == [ ] && !editedFreeformType;
      disabledRefusal = prelude.any (e: e.content ? disabledModules) editedEntries;

      # ── bipartite contribution relation (design spec §2.1) — the FACT gen-memo decides over ──────
      # Nodes: one per dirty/edited ENTRY (`"entry:<n>"` — cannot collide with a JSON array string,
      # which always starts with `[`), and one per declared-leaf LOCATION it touches (the injective
      # `builtins.toJSON path` id — a dot-join collides `["a.b"]."c"` with `["a"]."b.c"`, spec §2.1
      # OQ-4). Edge: `dependencies(locationId) = [contributing entry ids]`, `dependencies(entryId) =
      # []` — the CALLER-BUILT MODE contract (gen-memo `lib/graph-view.nix`): a location's
      # dependency lists the entries that CONTRIBUTE a decl/def there (`footprint`, above), so
      # gen-graph's reverse index/`dependentsOf` walked from a dirty/edited entry lands exactly on
      # the locations it can perturb — the same set `footprintPaths` used to name directly.
      entryNodes = prelude.imap0 (i: e: {
        id = "entry:${toString i}";
        locs = prelude.unique (map (r: builtins.toJSON r.path) e.footprint);
      }) allF;
      depMap = foldl' (
        acc: en: foldl' (acc2: loc: acc2 // { ${loc} = (acc2.${loc} or [ ]) ++ [ en.id ]; }) acc en.locs
      ) { } entryNodes;
      # `nodes` carries BOTH id families, but this justification binds only the LOCATION family:
      # gen-graph's `_reverseIndex` iterates `nodes` as the "from" side of `edges`, so a location
      # absent from `nodes` never contributes a reverse edge and its dirtiness would go unindexed.
      # Entry ids are carried for the plane's contract (the CALLER-BUILT MODE contract above), not
      # for discrimination: dropping them left all 507 gate cells inert, while dropping location
      # ids reds 17/22 warm cells. `dependencies` answers both families from the ONE map — an entry
      # id is never a `depMap` key, so `or [ ]` correctly answers `[]` for it too.
      accessor = {
        nodes = (map (e: e.id) entryNodes) ++ (attrNames depMap);
        dependencies = nid: depMap.${nid} or [ ];
      };
      seeds = map (e: e.id) entryNodes;
      # gen-memo DECIDES reuse over the FACT above (ADR-0008 item 2 — one incremental plane).
      # `prior = warmFrom` is never forced on the cold path: this whole `verdict` binding stays an
      # unforced thunk chain unless `.isClean` is read, and the cold path never reads it
      # (`warmActive`'s `&&` short-circuits on `warmFrom == null` before `decision` is touched).
      verdict = memo.warmDecision accessor warmFrom seeds;
    in
    {
      inherit
        footprint
        freeContribs
        reuseAllFreeform
        disabledRefusal
        ;
      # `identitiesHeld` is the plane's THIRD decision (see gen-memo `lib/warm.nix`): given the two
      # per-instance identity maps this engine builds from `warmFrom.config` and the new `config`, it
      # admits with an empty moved set or refuses by name. It is carried through here rather than
      # reached for separately so gen-memo is asked once, on one record, for one warm evaluation.
      inherit (verdict) isClean identitiesHeld;
      modules = {
        clean = map (e: e._file) cleanEntries;
        dirty = map (e: e._file) dirtyEntries;
        edited = map (e: e._file) editedEntries;
      };
    };

  # THE EMPTY-DEFINITION RULE, and it is gen's own. With no surviving definition the type gets to
  # supply a value before this is an error, and only a type declaring none is an error. A container is
  # empty-able — `attrsOf`/`lazyAttrsOf` → `{ }`, `listOf` → `[ ]`, `nullOr` → `null`, and a
  # `submodule` or tree → its own fold over no definitions (nixpkgs' `base.config`) — while every
  # leaf (and `raw`/`anything`/`deferredModule`/`either`) declares no empty value and still throws.
  #
  # Two distinct ways to arrive with nothing, and both land here: an option that was never defined at
  # all, and an option every one of whose definitions was discharged away — `mkIf false` as the sole
  # def. `whenEmpty` is what separates "a container nobody added to", which is legitimately empty,
  # from "a value nobody supplied", which is a mistake. `{ }` is "declares none" and `{ value = null; }`
  # is a declared null; one field cannot carry both, so the answer is a record and not a value.
  #
  # A FOREIGN type states the same fact in the foreign protocol's words and nowhere else, so the
  # second arm asks the boundary. Gen-first, foreign second — the same order `mergeTypes` takes.
  whenEmptyOf =
    type:
    if type == null then
      { }
    else if type ? whenEmpty then
      type.whenEmpty
    else
      interface.importedEmpty type;
  emptyValueOr =
    type: err:
    let
      empty = whenEmptyOf type;
    in
    if empty ? value then empty.value else throw err;
  # Whether `emptyValueOr` would yield rather than throw — lets the realizer decline to short-circuit an
  # undefined option so the ONE empty-value site stays inside the fold.
  hasEmptyValue = type: (whenEmptyOf type) ? value;

  # The refusal of a declared `type` that is not one (ADR-0025 item 1): nixpkgs aborts on it at the
  # declaration's use, uncatchably, and an unjudged fold returns the definition unchecked. Asked
  # only on the arms where the engine would otherwise fold against it (`interface.typeDefect`).
  declaredTypeRefusal =
    loc: type:
    "gen-merge: option `${showOption loc}' declares a `type' that ${interface.typeDefect type}";
  elementTypeRefusal =
    loc: type:
    "gen-merge: option `${showOption loc}' is folded through an element type that ${interface.typeDefect type}";

  # DID THIS TYPE BRING A FOLD OF ITS OWN? On gen's record the presence test IS the question:
  # `mergeDefs` is there exactly when the type folds its own definitions, and a leaf simply has none.
  # On a FOREIGN record presence stopped answering it — the protocol boundary publishes a leaf fold
  # for every type it exports, so past that point every completed type has one — which is why the
  # boundary also derives a marker recording whose fold it is, and why that arm is read there rather
  # than here. A type with no fold of its own falls through to this engine's own leaf fold, which is
  # where a leaf belonged in the first place: taking the other branch for it would cost a fresh
  # `typeDefs` list and a second entry into the same fold, for the same value.
  ownFold =
    type:
    if type == null then
      null
    # A fold of its own is folded under a `check` a foreign wrapper rewrote over it, which the
    # import half answers (`interface.checkedFold`, den-hoag-4ifgb). gen-types' `rewritesCheck` is
    # restated inline for cost: a call here is an environment on every fold. The construction door
    # holds this spelling to the protocol (`lib/default.nix`).
    else if
      type ? mergeDefs && !(type ? _checkWitness && type ? check && type.check != type._checkWitness)
    then
      type.mergeDefs
    else
      interface.importedFold type;

  # The fold a type merges by WITHOUT a definition check: nixpkgs' raw `merge`, which it calls only at
  # the freeformType site. A gen type's own fold is the same at every site; a foreign one is checked
  # at option sites (`ownFold`) and unchecked here, and an imported record whose fold is checked
  # carries the unchecked one on it as `mergeDefs.unchecked`. A type with no fold of its own (a gen
  # leaf, a bare `mkType`, a foreign record stating neither `merge` nor `check`) folds by `mergeLeaf`,
  # because that is the fold the option site already gives it (`ownFold`'s `null` falls through to
  # it), so the same type folds the same at every site. For a gen leaf it is also nixpkgs' answer:
  # handed the same type, nixpkgs' freeform site folds by the `leafFold` the export publishes, which
  # agrees with `mergeLeaf`.
  rawFold =
    type:
    if type ? mergeDefs then
      type.mergeDefs.unchecked or type.mergeDefs
    else
      let
        imported = interface.importedRawFold type;
      in
      if imported == null then mergeLeaf else imported;

  # ── the merge fold (shared by evalModuleTree options + the collection strategies) ──
  # Public (loc,type,rawDefs) contract — NON-short-circuiting, and the pre-kernel fold's value on every
  # input whose type is a type, so every existing consumer of the exported `mergeDefs` escape hatch
  # (spec §1 item 6) is unchanged there; a non-type where a fold demands its element is refused by
  # name (`elementTypeRefusal`), where the pre-kernel fold took it for a leaf.
  # The opt-in fixed-input path is `mergeDefsWith true`, reached ONLY through the evalModuleTree knob.
  #
  # This is the VALUE-ONLY fold — the hot path the structural strategies (attrsOf/listOf/submodule
  # per-element merges) and the escape hatch ride. It allocates NO provenance: the always-on channel
  # (A2 spec §1) is produced by the SEPARATE `mergeDefsRichWith` below, which the realizer invokes ONLY
  # for the top-level DECLARED options, so a config's thousands of structural sub-merges pay nothing
  # for a channel they never surface. The two folds share `mergeLeaf`; their discharge/priority/verify
  # spines are deliberately kept parallel (the provenance suite's value assertions + the oracle guard
  # against drift), because routing the structural hot path through the rich `{ value; prov }` record
  # measurably regresses the collection workloads (a per-element record thrown away unread).
  #
  #   rawDefs :: [{ file; value }]   (value may carry mkMerge/mkIf/mkOverride/mkOrder)
  # Discharge properties → filterOverrides (min-priority wins) → sortProperties (order pass) →
  # dispatch: a structural type owns its combine via `.merge`; a leaf (gen-types checker, no
  # `.merge`) merges by mergeLeaf then `verify`.
  # ★ THE THREE PASSES RUN IN THAT ORDER AND MAY NOT BE REORDERED — `sortProperties` overwrites the
  # ORDER axis onto defs whose OVERRIDE priority `filterOverrides` has already consumed (the full
  # argument is at lib/priority.nix `sortProperties`). Everything downstream of the sort reads
  # `file`/`value` and never `priority`.
  # With `coreShortCircuit` it additionally honours the fixed-input core marker (spec §2.5), checked
  # BEFORE discharge:
  #   • SOLE core def at this loc  → return its `values` directly, skipping discharge/fold/verify —
  #     by contract already the full-merge output, so the result is byte-identical where the core is
  #     correct (a WRONG core surfaces here as a divergent value; the gate teeth catch it).
  #   • core def + ANY other def   → conservative fall-through: unwrap each core marker to its
  #     `values` as a plain def and run the normal spine (correctness over the skip). Byte-identical
  #     to a config that had supplied `values` in place of the marker.
  mergeDefs = mergeDefsWith false;
  # The same spine over a SUBSET of a position's definitions, whose fold the caller completes later
  # with the rest (den-hoag-fjdnf). Its result is a definition again: the merged winners under the
  # priority that selected them, so that folding it with the remaining definitions is the fold over
  # all of them (filterOverrides is a fold of the (priority, values) monoid, and a partial fold stays in
  # it only while it keeps its priority). At the default priority the wrapper is the identity and is not
  # written. With no winners the result is the monoid's identity, a definition that discharges to nothing
  # (`mkIf false`): an empty value at the default priority would beat a later `mkDefault`. One discharge
  # and one priority pass, shared by the value and its priority.
  mergeDefsPartial =
    loc: type: rawDefs:
    let
      discharged = concatMap (
        d:
        map (x: {
          inherit (d) file;
          inherit (x) value priority;
        }) (dischargeProperties d.value)
      ) rawDefs;
      r = filterOverridesRich discharged;
      winners = r.winners;
      sorted =
        if any (w: (w.value._type or null) == "order") winners then sortProperties winners else winners;
      typeDefs = map (
        w:
        if w ? orderStated then
          {
            inherit (w) file value;
            priority = w.orderPriority;
          }
        else
          { inherit (w) file value; }
      ) sorted;
      fold = ownFold type;
      result =
        if fold != null then
          fold loc typeDefs
        else if type ? verify || interface.typeDefect type == null then
          mergeLeaf loc sorted
        else
          throw (elementTypeRefusal loc type);
      checked =
        if type != null && type ? verify then
          (
            let
              e = type.verify result;
            in
            if e == null then
              result
            else
              throw "gen-merge: a definition for option `${showOption loc}' is not of the expected type: ${e}"
          )
        else
          result;
    in
    if winners == [ ] then
      {
        _type = "if";
        condition = false;
        content = { };
      }
    else if r.highestPrio == defaultPriority then
      checked
    else
      {
        _type = "override";
        priority = r.highestPrio;
        content = checked;
      };
  # Whether a definition survives discharge — nixpkgs' `isDefined = defsFinal != [ ]`, decided by
  # discharge alone because `filterOverrides` never empties a non-empty list. The `? _type` fast
  # path is nixpkgs' own: a value with no property marker cannot discharge to nothing.
  isDefinedValue = v: !(v ? _type) || dischargeProperties v != [ ];
  isDefinedBy = defs: any (d: isDefinedValue d.value) defs;
  mergeDefsWith =
    coreShortCircuit: loc: type: rawDefs:
    let
      coreDef = head rawDefs;
      soleCore = coreShortCircuit && length rawDefs == 1 && isCoreValue coreDef.value;
      normalized =
        if coreShortCircuit then
          map (d: if isCoreValue d.value then d // { value = d.value.values; } else d) rawDefs
        else
          rawDefs;
      discharged = concatMap (
        d:
        map (x: {
          inherit (d) file;
          inherit (x) value priority;
        }) (dischargeProperties d.value)
      ) normalized;
      winners = filterOverrides discharged;
      # The order pass, gated exactly as nixpkgs gates it: the overwhelming majority of locs carry no
      # order marker, and for them the sort is the identity permutation, so the scan buys the fast
      # path its skip. Everything after this point consumes `sorted`, never `winners`. The test is
      # `isOrderMarker`'s body inline, at all three twins: `or null` answers a non-attrset, and the
      # call's argument thunk per winner is not paid.
      sorted =
        if any (w: (w.value._type or null) == "order") winners then sortProperties winners else winners;
      typeDefs = map (
        w:
        if w ? orderStated then
          {
            inherit (w) file value;
            priority = w.orderPriority;
          }
        else
          { inherit (w) file value; }
      ) sorted;
      fold = ownFold type;
      result =
        if winners == [ ] then
          emptyValueOr type "gen-merge: option `${showOption loc}' has no definitions after priority resolution"
        else if fold != null then
          fold loc typeDefs
        # The element twin of `mergeDefsRichWith`'s door: a container demands its element's fold here,
        # and a value that is not a type lands on this arm. No caller of this fold means "untyped" by
        # `null`, so null is judged with the rest.
        else if type ? verify || interface.typeDefect type == null then
          mergeLeaf loc sorted
        else
          throw (elementTypeRefusal loc type);
      checked =
        if type != null && type ? verify then
          (
            let
              e = type.verify result;
            in
            if e == null then
              result
            else
              throw "gen-merge: a definition for option `${showOption loc}' is not of the expected type: ${e}"
          )
        else
          result;
    in
    if soleCore then coreDef.value.values else checked;

  # mergeDefsRichWith coreShortCircuit loc type rawDefs :: the RICH sibling — `{ value; prov }`, the
  # value plus the merge's PROVENANCE record (A2 spec §1). Used by the realizer path (`mergeOptionWith`)
  # for DECLARED options only. `value` is computed by the SAME discharge/priority/verify spine as
  # `mergeDefsWith` (kept parallel — see the note above); `prov` SHARES this call's `discharged` +
  # `filterOverridesRich` let-bindings (ONE discharge, ONE priority pass per loc). `prov` is a separate
  # lazy attr: an unforced option pays ~one record thunk (never forced).
  # FORCING CONTRACT: reading ANY field of the record (`defs`/`winners`/`priority`/`defaulted`) forces
  # this loc's contributing defs to WHNF — the record reads `discharged`, and `dischargeProperties`
  # branches on `isAttrs`, so a bare-`throw` def fires even on a plain `.defs` read (the SAME discharge
  # the value path runs to resolve priorities). What it does NOT force is the merged VALUE: the
  # structural `.merge` / leaf `verify` / `apply` live on the value path (`checked`), never reached by a
  # prov read. So provenance forces WHO-defined-what to WHNF, never the resolved value. (Weaker than
  # nixpkgs `definitionsWithLocations`, which forces nothing — byte-mode discharges eagerly for priority.)
  # `winners` alone reads further: the order pass (`sorted`) tests each winning VALUE for the order
  # marker, so it forces the values to WHNF, and a `default = throw …` fires on a `.winners` read
  # where `defs`/`priority`/`defaulted` leave it unforced (den-hoag-zakjg U1).
  #   • defs      — every contributing def post property-discharge, pre priority pass (a property tag
  #                 keeps its originating file; a false-`mkIf` sub-def has already dropped in discharge).
  #                 Per-def `priority` = its `mkOverride` wrapper's number, else the default override 100.
  #   • winners   — the defs the priority pass kept (the merge's actual inputs).
  #   • priority  — the effective (min) priority the filter selected (`highestPrio`).
  #   • defaulted — the synthetic option `default` (`file = "<default>"`, joined by `withDeclaredDefault`)
  #                 is the SOLE surviving winner ⇒ nobody else set the option (the `<default>` def won).
  # coreShortCircuit skip: the record is SYNTHESIZED from the marker (core def as sole def + winner at
  # the bare priority, defaulted=false) so the skip stays a skip — the discharge/fold spine never runs.
  mergeDefsRichWith =
    mode: loc: type: rawDefs:
    let
      coreDef = head rawDefs;
      soleCore = mode.coreShortCircuit && length rawDefs == 1 && isCoreValue coreDef.value;
      normalized =
        if mode.coreShortCircuit then
          map (d: if isCoreValue d.value then d // { value = d.value.values; } else d) rawDefs
        else
          rawDefs;
      discharged = concatMap (
        d:
        map (x: {
          inherit (d) file;
          inherit (x) value priority;
        }) (dischargeProperties d.value)
      ) normalized;
      # Value path uses the plain (allocation-free) filterOverrides — SHARED by the prov record's
      # `winners`. The prov record's `priority` reads `filterOverridesRich`'s `highestPrio` LAZILY (only
      # when `.priority` is forced), so an unforced provenance channel never pays for the rich wrapper.
      winners = filterOverrides discharged;
      # The order pass, same gate and same position as the value path's — the twin stays parallel.
      # `prov.priority` below deliberately keeps reading `discharged`/`filterOverridesRich`, i.e. the
      # OVERRIDE axis upstream of this sort: the record's `priority` field means the override number
      # the filter selected, and the order axis must not be allowed to answer that question.
      sorted =
        if any (w: (w.value._type or null) == "order") winners then sortProperties winners else winners;
      typeDefs = map (
        w:
        if w ? orderStated then
          {
            inherit (w) file value;
            priority = w.orderPriority;
          }
        else
          { inherit (w) file value; }
      ) sorted;
      # The fold dispatch, exactly as the value path reads it above — the twin stays parallel —
      # except where a report is carried and the type's fold states one (a nesting seam's
      # `mergeDefs.reported`): there ONE application yields `{ value; undeclared; }`, read apart
      # below. The condition is restated inline rather than bound: a binding here is a thunk on
      # every declared leaf.
      fold =
        if mode.carried && type != null && type ? mergeDefs.reported then
          type.mergeDefs.reported mode.strict
        else
          ownFold type;
      # A reporting seam's EMPTY value is its lax fold over no definitions, run where its reference
      # runs it (nixpkgs' `base.config`, prefix `[ ]`, as `whenEmpty` does), with the report of that
      # same fold read at this option's location. Its `whenEmpty` is the strict call, for the sites
      # that carry no report.
      result =
        if winners == [ ] && mode.carried && type != null && type ? mergeDefs.reported then
          (
            let
              r = type.mergeDefs.reported mode.strict [ ] [ ];
            in
            {
              inherit (r) value;
              undeclared = map (u: u // { path = loc ++ u.path; }) r.undeclared;
            }
          )
        else if winners == [ ] then
          emptyValueOr type "gen-merge: option `${showOption loc}' has no definitions after priority resolution"
        else if fold != null then
          fold loc typeDefs
        # The untyped option with several definitions (`mergeUntyped`, below). One definition is
        # its own value under both folds, so the single-definition case stays on the leaf fold's
        # fast path and pays one length test.
        else if type == null && length sorted > 1 then
          mergeUntyped loc sorted
        # A declared type that brought no fold and no `verify` is where a value that is not a type
        # lands, and the leaf fold would return the definition unchecked. It is judged HERE, on this
        # arm alone: the gen-typed path has already answered, and pays nothing for the question.
        else if type == null || type ? verify || interface.typeDefect type == null then
          mergeLeaf loc sorted
        else
          throw (declaredTypeRefusal loc type);
      checked =
        if type != null && type ? verify then
          (
            let
              e = type.verify result;
            in
            if e == null then
              result
            else
              throw "gen-merge: a definition for option `${showOption loc}' is not of the expected type: ${e}"
          )
        else
          result;
      prov =
        if soleCore then
          {
            defs = [
              {
                inherit (coreDef) file;
                priority = defaultPriority;
              }
            ];
            winners = [ { inherit (coreDef) file; } ];
            priority = defaultPriority;
            defaulted = false;
          }
        else
          {
            defs = map (d: { inherit (d) file priority; }) discharged;
            # `sorted`, not `winners`: this field means THE MERGE'S ACTUAL INPUTS, and after the
            # order pass those are the sorted ones. Identical list on every marker-free loc.
            winners = map (w: { inherit (w) file; }) sorted;
            priority = (filterOverridesRich discharged).highestPrio;
            # The `<default>` sentinel is engine-synthesized (never a real `_file`), so it is a safe
            # marker for "the option default supplied the value".
            defaulted = winners != [ ] && all (w: w.file == "<default>") winners;
          };
      # The undeclared-report channel (ADR-0025 item 1) — `[ ]` for every ordinary type, the same
      # default posture `coreShortCircuit ? false`/`warmFrom ? null` already take on this file: a
      # type only produces one by carrying `mergeDefs.reported` (today, only `moduleTree`'s nesting
      # seam), only where this evaluation's report is carried, and `soleCore` skips it exactly as it
      # skips the discharge/fold spine itself. It is the SAME application `result` made over
      # `typeDefs`, so the report and the value agree about which defs won.
      undeclared =
        if soleCore || !(mode.carried && type != null && type ? mergeDefs.reported) then
          [ ]
        else
          result.undeclared;
    in
    {
      value =
        if soleCore then
          coreDef.value.values
        else if mode.carried && type != null && type ? mergeDefs.reported then
          # `verify` applied here, inline, as `checked` applies it on every other path: `checked`
          # itself cannot read this branch without costing a thunk on every verified leaf.
          (
            if type ? verify && type.verify result.value != null then
              throw "gen-merge: a definition for option `${showOption loc}' is not of the expected type: ${type.verify result.value}"
            else
              result.value
          )
        else
          checked;
      # `typeDefs` is carried so the `nested` walk reads the fold's own discharged definitions
      # instead of re-running the passes (den-hoag-i4c0n C1). THE STATED PRICE: one attribute slot
      # on every rich record, and no thunk: it binds the fold's existing `typeDefs`.
      inherit prov undeclared typeDefs;
    };

  # ── A NESTED POSITION, AND THE REPORT MODE IT CARRIES (den-hoag-n6dh7 items 1, 2; gate C2) ─────
  # One record per nested tree a declared option's value holds: its `key` (the position path within
  # the option), the `address` of its seed definitions, the `loc` the placing fold receives, and its
  # `mode`. The mode is a property of the SITE, decided from the fact the rich fold dispatches on: a
  # tree typed directly on the option (`key == [ ]`) whose type states `.reported`, in an evaluation
  # whose report is carried, evaluates REPORTED, inheriting the host's strictness —
  # `mergeDefsRichWith`'s `mode.carried && type ? mergeDefs.reported` arm. Everywhere else (every
  # container element, every freeform-plane position) it is `"called"`: the child evaluates in the
  # CALLED mode of the member it evaluates under (`nests.calledMode`), as each nesting type's called
  # form does. So each position is reached in exactly one mode, and it is the mode its fold reads.
  nestedPosition =
    hostMode: type:
    {
      key,
      address,
      loc,
    }:
    {
      inherit key address loc;
      mode = positionMode hostMode type key;
    };
  positionMode =
    hostMode: type: key:
    if key == [ ] && hostMode.carried && type ? mergeDefs.reported then
      {
        carried = true;
        inherited = hostMode.strict;
      }
    else
      "called";
  # The `{ carried; inherited; }` pair a position's child evaluates in, under the member it
  # evaluates as (at a union position, the member the union's choice returns).
  positionChildMode =
    member: position: if position.mode == "called" then member.nests.calledMode else position.mode;

  # ── THE CALLED FOLD REFUSES (den-hoag-n6dh7 item 1) ─────────────────────────────────────────────
  # A nesting type declares its tree; it does not evaluate it. Every evaluating field is a named
  # refusal where it is CALLED (the 2-arity `mergeDefs`, `submodule`'s `whenEmpty.value`, the tree
  # record's `emptyTree`), naming the field and the loc: the tree is a child of the one evaluation
  # that holds it, and an evaluation reads it through the fold's threaded sibling. The exported
  # foreign `merge` does not refuse; it bridges (item 7).
  calledNestingRefusal =
    type: field: loc:
    "gen-merge: `${type}'${
      if loc == null then "" else " at option `${showOption loc}'"
    }: its called `${field}' does not evaluate the nested tree: a nested tree is a child of the one evaluation that holds it (`evalModuleTree'), read through its fold's threaded sibling, and no second evaluation is made for it";

  # THE `name` EVERY NESTED TREE STATES, AS NIXPKGS' `submoduleWith` STATES IT: its merge adds
  # `{ _module.args.name = last loc; }` to each evaluation over its base's `mkOptionDefault "‹name›"`,
  # so the position's name is a `config` value a module can override and a caller's `specialArgs.name`
  # outranks. A nested tree over definitions at a position (the positioned knots,
  # `knotChildPositioned` and `knotRootPositioned`) carries this value as the `name` key of the
  # argument sets its modules are applied to (`baseArgs`, and `declArgs` on the declaration plane);
  # it enters a merge, as one priority-100 definition, only in `positionNameOf`, when a module states
  # `name`. `moduleArgs` zips the modules' own sets alone, except where a module declares
  # `options._module`, whose `apply` nixpkgs runs over the set holding `name` (`moduleOwnArgs`). A nested tree over no definitions, and
  # every nesting type's declarations, read the placeholder module `namePlaceholder` instead. The
  # first always outranks the second, so a child never carries both. A key and not a module, because
  # the module's collection is what costs.
  positionArgsAt = loc: {
    name = if loc == [ ] then "" else prelude.last loc;
  };
  # `_module.args` merges as nixpkgs' `lazyAttrsOf raw` (`moduleArgs` in `evalModuleTreeWith`): one
  # argument's definitions are discharged and priority-filtered, and MORE THAN ONE WINNER REFUSES BY
  # NAME, naming the argument and every winning file in fold order.
  mergeModuleArg =
    name: defs:
    # One property-free definition is its own winner, decided before any binding is
    # allocated: gen-schema's instance inlet sets an argument once on every instance.
    if tail defs == [ ] && !(priority.isProperty (head defs).value) then
      (head defs).value
    else
      let
        winners = filterOverrides (
          concatMap (d: map (w: w // { inherit (d) _file; }) (dischargeProperties d.value)) defs
        );
        # Each file once, in fold order; a file carrying several definitions (an `mkMerge`
        # inside one module) says how many.
        files =
          ws:
          let
            fs = map (w: w._file) ws;
          in
          concatStringsSep ", " (
            map (
              f:
              let
                n = length (filter (x: x == f) fs);
              in
              if n == 1 then f else "${f} (${toString n} definitions)"
            ) (prelude.unique fs)
          );
      in
      if length winners == 1 then
        (head (sortProperties winners)).value
      else if winners == [ ] then
        throw "gen-merge: module argument `${name}' (`_module.args.${name}') is used but every definition of it is disabled; defined in ${files defs}"
      else
        throw "gen-merge: module argument `${name}' (`_module.args.${name}') is defined multiple times, and a module argument must be unique; defined in ${files winners}";

  # Each module's `_module.args`, one set of `{ _file; value; }` definitions per module stating any.
  # Each module's `_module.args` definition, `{ _file; args; }`, as written (`args` undischarged).
  # Pay per use: `filter` calls its predicate without allocating a thunk, so a module
  # stating no `_module` costs nothing here, and one stating no `_module.args` costs
  # its `m` alone (an `optional` call would thunk both of its arguments).
  moduleArgDefsOf =
    pushed:
    concatMap (
      p:
      let
        m = pushDownProperties p.attrs._module;
      in
      if m ? args then
        [
          {
            inherit (p) _file;
            inherit (m) args;
          }
        ]
      else
        [ ]
    ) (filter (p: p.attrs ? _module) pushed);
  moduleArgSetsOf =
    pushed:
    map (
      d:
      mapAttrs (_: value: {
        inherit (d) _file;
        inherit value;
      }) (pushDownProperties d.args)
    ) (moduleArgDefsOf pushed);

  # A positioned evaluation's `name`, as nixpkgs' `submoduleWith` resolves it: the position's
  # `last loc` is one priority-100 definition beside whatever the modules state. A module stating
  # none leaves the position's value itself, read without building the merge; one that states some
  # merges its definitions with the position's (`mergeModuleArg`), so `mkForce` wins, `mkDefault`
  # yields, and a plain definition refuses as defined twice. `stated` is the evaluation's
  # `moduleArgs`, which holds no position definition.
  positionNameOf =
    prefix: stated: pushed:
    if stated ? name then
      mergeModuleArg "name" (
        builtins.catAttrs "name" (moduleArgSetsOf pushed)
        ++ [
          {
            _file = "<position>";
            value = (positionArgsAt prefix).name;
          }
        ]
      )
    else
      (positionArgsAt prefix).name;

  declarationStratum = declarationStratumWith false redeclareDecl;
  declarationStratumPositioned = declarationStratumWith true redeclareDecl;
  declarationSpine = declarationStratumWith false spineRedeclare;
  declarationSpinePositioned = declarationStratumWith true spineRedeclare;
  # The guard's leaf: the LAST of a loc's k declarations, which is what a fold keeping the later
  # operand answers, so no step is folded. Its arity is `redeclareDecl`'s (sitesAt, loc, the loc's
  # declarations); the merge of k leaves is a leaf by construction, so the spine needs no merged
  # record. Every declaration was forced by the leaf/group test before this is asked.
  spineRedeclare = _: _: prelude.last;

  # THE STAGED DECLARATION PASSES (den-hoag-9oc7y), the declaration guard's path when its spine did
  # not resolve. Pass 0 is the guard's poisoned fold, `s0`. A node whose WHNF did not resolve there
  # (`pending`) is re-tried at pass k with `options` bound to pass k-1's declarations, stamped as
  # `declaredOptions` stamps them, so a pass reads only the settled output of strictly earlier passes
  # (ADR-0016 ruling 7, ADR-0033) and a node resolves at the least pass its reads allow. A pending node
  # must resolve to a LEAF: one resolving to a group is an option's presence moving with `options`.
  # The passes run until nothing is pending or a pass resolves nothing, and then the spine-first of the
  # groups and the residue (a node whose WHNF throws at every pass) is forced outside `tryEval`: a
  # group at pass 0, where its own demand reads the poison, and a residue node at the last pass, so a
  # read that resolved does not hide the node's own error and a cycle still bottoms out in the poison.
  # The root's key set is forced outside `tryEval` too: a module whose option key set or `imports`
  # read a refused argument refuses there, as the guard's spine always did. A module that catches a
  # stamped-view refusal can take another shape on the value side, where it reaches Nix's recursion
  # abort uncatchably; that is the guard's standing price for a module that catches it (ADR-0008 §3),
  # now reached at any pass rather than only at pass 0. One binding, because a top-level binding is a
  # load thunk the hub perf-bench prices.
  stagedDeclarations =
    positioned: args: s0:
    let
      stratum = if positioned then declarationSpinePositioned else declarationSpine;
      prefix = args.prefix;
      pendingIn =
        p: t:
        concatMap (
          n:
          let
            v = t.${n};
            w = builtins.tryEval (!(isAttrs v) || (v._type or null) == "option");
          in
          if !w.success then
            [ (p ++ [ n ]) ]
          else if w.value then
            [ ]
          else
            pendingIn (p ++ [ n ]) v
        ) (attrNames t);
      refuse =
        t: p:
        builtins.seq (isOptLeaf (getAttrByPath p t.options)) (
          throw "gen-merge: the declaration of `${showOption (prefix ++ p)}' resolved in no pass"
        );
      go =
        prev: pending: groups:
        let
          sk = stratum (args // { optionsView = stampOptions prev.sitesAt prefix prev.options; });
          tried = map (p: {
            inherit p;
            w = builtins.tryEval (
              let
                v = getAttrByPath p sk.options;
              in
              !(isAttrs v) || (v._type or null) == "option"
            );
          }) pending;
          grouped = groups ++ map (x: x.p) (filter (x: x.w.success && !x.w.value) tried);
          left = map (x: x.p) (filter (x: !x.w.success) tried);
          first = head (filter (p: builtins.elem p grouped || builtins.elem p left) pending0);
        in
        if left != [ ] && length left < length pending then
          go sk left grouped
        else if grouped == [ ] && left == [ ] then
          true
        else if builtins.elem first left then
          refuse sk first
        else
          refuse s0 first;
      pending0 = pendingIn [ ] s0.options;
    in
    if pending0 == [ ] then
      throw "gen-merge: the declaration guard's spine did not resolve, and no declaration node is unresolved"
    else
      go s0 pending0 [ ];

  # The documentation placeholder, one module shared by every nesting type: the child over no
  # definitions and the declarations (`substructure.declares`) read it.
  namePlaceholder._module.args.name = mkOptionDefault "‹name›";

  # ── THE NESTED TREE'S DOOR (den-hoag-n6dh7 items 4, 7) ───────────────────────────────────────────
  # One ROOT evaluation of a nesting SITE's tree — the site is `{ position; nests; loc; defs; }` —
  # in the mode `m` (`{ carried; inherited; }`). It is the call a nesting type's called form made,
  # field for field, built from what the type states as data: its module set plus one entry per
  # seed definition, the placing fold's `loc` as the prefix, and its own arguments, with `name`
  # carried by the positioned knot (`positionArgsAt`, resolved by `positionNameOf`).
  # It is the export BRIDGE's child (item 7, OQ11 (d)), where no gen evaluation holds the tree: one
  # root evaluation per nested tree, as many as the called form made. With no definition it is the tree over none, with `nests.empty`'s arguments, as a child with an
  # empty seed is (item 4). It is a ROOT evaluation, so the trees it holds are its own children.
  # It is driven on a root knot, never a partial one, whatever `nests.partial` says: a partial fold's value
  # is definitions a later gen fold completes, and nothing folds a foreign evaluation's value again, so
  # the export bridge's ROOT serves the full fold (den-hoag-5ov3p gate C3). Only the root: a partial tree
  # nested below it is a child of this evaluation, selected by its own type in `childTree`, and stays partial,
  # because its reader is the gen fold that consumes it (a guard carrier under a mounted aspect tree), so a
  # nixpkgs consumer at depth 1 or more reads its definitions.
  nestedTreeAt =
    m: site:
    if site.defs == [ ] then
      evalModuleTreeWith knotRoot m.carried m.inherited {
        modules = site.nests.modules ++ [ namePlaceholder ];
        inherit (site.nests) coreShortCircuit;
        inherit (site.nests.empty) prefix specialArgs check;
      }
    else
      evalModuleTreeWith knotRootPositioned m.carried m.inherited {
        modules = site.nests.modules ++ map site.nests.entry site.defs;
        prefix = site.loc;
        inherit (site.nests) specialArgs check coreShortCircuit;
      };

  # ── THE ENGINE'S THREADED TWIN (den-hoag-n6dh7 item 5) ───────────────────────────────────────────
  # The CALLED fold over the type whose fold is its threaded form, bound to the evaluation's
  # accessor `ev` (`{ position; containerNodes; child; }`). So the discharge, priority, order and
  # `verify` spine is the called fold's own — one text, not a second copy that could drift from it —
  # and a type carrying no sibling (a leaf, a foreign fold, a fold nothing nests under) folds
  # exactly as it does called: that is the twin's PRESENCE ARM (gate C3). The type is first HOMED,
  # where it is bound to its position (`interface.homedAt`): a recognised foreign container becomes
  # gen's own, and an unrecognised one declaring a gen nesting element threads through its own
  # `substSubModules` rebuild, or is refused by name before any fold is taken
  # (`interface.threadedForeign`).
  #
  # The bound record states exactly what the spine reads of a type that brings a fold: the fold,
  # the empty value and `verify` (the rest is read only where no fold is brought), so binding it
  # copies none of the type's other fields. A nesting type's reporting twin rides beside its
  # threaded fold (`.reported`, which the rich fold selects on), and its EMPTY value is its threaded
  # fold over no definitions: the child at this position with an empty seed. Its called `whenEmpty`
  # refuses (item 1).
  threadedAs =
    ev: type:
    if isAttrs type && type ? mergeDefs.threaded then
      let
        mergeDefs =
          if type.mergeDefs ? threadedReported then
            {
              __functor = _: type.mergeDefs.threaded ev;
              reported = type.mergeDefs.threadedReported ev;
            }
          # A `check` a foreign wrapper rewrote is carried onto the threaded fold HERE, before the
          # record is re-bound to the fields below, which do not include it (den-hoag-4ifgb).
          # gen-types' `rewritesCheck`, restated inline for cost; the construction door holds the
          # spelling to the protocol (`lib/default.nix`).
          else if type ? _checkWitness && type ? check && type.check != type._checkWitness then
            interface.checkedFold type (type.mergeDefs.threaded ev)
          else
            type.mergeDefs.threaded ev;
        whenEmpty =
          if type ? nests then { value = type.mergeDefs.threaded ev [ ] [ ]; } else whenEmptyOf type;
      in
      if type ? verify then
        {
          inherit mergeDefs whenEmpty;
          inherit (type) verify;
        }
      else
        { inherit mergeDefs whenEmpty; }
    else
      type;
  # Under `lazyAttrsOf`'s fold (`ev.under`, set by that fold alone), a position the key walk made a
  # CONTAINER NODE (`containerAt`, den-hoag-9d80v) is not folded inline: it is read off that node,
  # whose own fold is this one at the same `loc`, over the same definitions.
  mergeDefsThreaded =
    ev: loc: type:
    let
      t = interface.homedAt "evalModuleTree" loc type;
    in
    mergeDefs loc (
      if ev.under or false || (ev.exactAt or null) != null && unionNodeAt ev loc t then
        threadedUnder ev loc t
      else
        threadedAs ev t
    );
  # The threaded twin of `mergeDefsPartial` (den-hoag-fjdnf): the same accessor rule, folding partially.
  mergeDefsThreadedPartial =
    ev: loc: type:
    let
      t = interface.homedAt "evalModuleTree" loc type;
    in
    mergeDefsPartial loc (
      if ev.under or false || (ev.exactAt or null) != null && unionNodeAt ev loc t then
        threadedUnder ev loc t
      else
        threadedAs ev t
    );
  # The fold's half of the walk's container-node rule (`keyWalk`): a container `containerAt` holds
  # at an exact container's element (`exactAt`, never the walk's own root), other than an
  # attribute-keyed one (`keyedOverAt`), is read off its node.
  # Asked only of a marked element (`types.exactThread`), so an unmarked fold calls nothing here.
  unionNodeAt =
    ev: loc: t:
    ev.containerNodes or false
    && ev.position != [ ]
    && ev.exactAt == ev.position
    && isAttrs t
    && !(keyedOverAt loc t)
    && containerAt loc t;
  # An ATTRIBUTE-KEYED container of gen's own (`lazyAttrsOf`, or an `attrsOf` whose element is not
  # itself keyed over-approximately, or a stock one re-homed as one) at an exact container's element
  # is keyed OVER-APPROXIMATELY in the enclosing group: its candidate keys are the attribute names of
  # its definitions, already forced to WHNF by the exact container above, so keying them forces
  # nothing nixpkgs does not. An `attrsOf` over an element that would itself key over-approximately
  # is a container node instead, one per element of the exact container above, which is the unit
  # nixpkgs merges: that element's keys are its definitions' data, read when the element is. One
  # predicate, read by the walk (`keyWalk`) and the fold (`unionNodeAt`).
  keyedOverAt =
    loc: t:
    !(t ? choose || t ? __threadedForeign)
    && (
      (t.name or null) == "lazyAttrsOf"
      || ((t.name or null) == "attrsOf" && !(keyedOverMemberAt loc t.carries.element))
    );
  # Would this element key over-approximately (`keyedOverAt`), looked through `nullOr`, which adds no
  # step? Over any other element an `attrsOf` keys over-approximately itself: an element that is a
  # container is then a node in the over-approximating regime, one per inner element, read by the
  # fold through the element's own mark (`interface.mayFoldNested`), so no lazy unit is minted twice.
  keyedOverMemberAt =
    loc: t0:
    let
      m = interface.homedAt "evalModuleTree" loc t0;
    in
    if isAttrs m && (m.name or null) == "nullOr" then
      keyedOverMemberAt loc m.carries.element
    else
      keyedOverAt loc m;
  # THE FOLD'S HALF OF THE CONTAINER NODE, at gen's `defineType` door (S1 arm (v) generalized,
  # den-hoag-t1j4z Case B, ADR-0039). The walk mints a node under every over-approximating container
  # that adds a step (`keyWalk`); WHAT it minted at a position is the evaluation accessor's
  # (`containerNodeAt`, den-hoag-o3oz5), never re-decided from this record. So every container built
  # through the door reads its node at its own threaded entry, below the walk's own root, wherever
  # the walk minted one, whoever calls its fold: a consumer's fold threads the accessor it was given,
  # extended by its step, and needs nothing else. A record rewritten after it was built
  # (`// { name = … }`) reads as another type to the walk, and the fold reads what the walk minted.
  # A nested tree and a leaf are never nodes, so their folds are not wrapped; the guard reads
  # attribute presence only, because every type built pays it.
  readsMintedNode =
    self: t:
    if !(isAttrs t) || !(t ? split || t ? choose) || t ? nests || !(t ? mergeDefs.threaded) then
      t
    else
      t
      // {
        mergeDefs = t.mergeDefs // {
          threaded =
            ev:
            if (ev.containerNodes or false) && ev.position != [ ] then
              loc: defs:
              let
                minted = containerNodeAt ev;
              in
              if !(containerAt loc self) || minted == null then
                t.mergeDefs.threaded ev loc defs
              else if !(builtins.isBool minted) then
                throw (accessorUnansweredRefusal loc self)
              else if minted then
                (ev.child { inherit (ev) position; }).value
              else
                throw (containerReadAsTreeRefusal loc self)
            else
              t.mergeDefs.threaded ev;
        };
      };
  # What the key walk minted at the fold's position, as the accessor states it (`evAt`): `true` a
  # container node, `false` another child (a nested tree), `null` nothing.
  containerNodeAt =
    ev:
    ev.child {
      inherit (ev) position;
      __genMergeMinted = true;
    };
  # The fold's type is a container, and the walk keyed its position as a nested tree: the walk read
  # the type as another (a record whose `name` was rewritten after it was built). Refused by name
  # where reading a container's value off a tree's record would abort uncatchably (ADR-0025 item 1,
  # den-hoag-4zvc9).
  containerReadAsTreeRefusal =
    loc: t:
    "gen-merge: `evalModuleTree': option `${showOption loc}': its type `${t.name or "<container>"}' folds as a container, but the key walk keyed this position as a nested tree, so the two read the type's structure differently; a type record whose `name' is rewritten after it is built reads as another type to the walk. Build the type through its own constructor rather than renaming one";
  # The accessor a container's fold was handed does not answer what the walk minted (`containerNodeAt`
  # read neither `null` nor a bool): a consumer container's threaded fold rebuilt or narrowed the site
  # record its element's accessor passes to `child`. Refused by name where reading the answer would
  # abort uncatchably (ADR-0025 item 1).
  accessorUnansweredRefusal =
    loc: t:
    "gen-merge: `evalModuleTree': option `${showOption loc}': its type `${t.name or "<container>"}' folds as a container, but the evaluation accessor its fold was handed does not state what the key walk minted here: a container's threaded fold above it rebuilt or narrowed the site its accessor's `child' receives. Extend the accessor it was handed (`ev // { position = …; }`) and pass `child' its site whole";
  threadedUnder =
    ev: loc: t:
    if containerAt loc t then
      let
        read = (ev.child { inherit (ev) position; }).value;
      in
      {
        mergeDefs = _: _: read;
        whenEmpty.value = read;
      }
    else
      threadedAs ev t;

  # The evaluation's accessor at one group of a node of the one evaluation (den-hoag-n6dh7 item 5,
  # v8): a nested tree is read through the reading node's own record, as its `nested` child at the
  # group and the fold's position, never through an identifier.
  # `host`: the reading node's `reader` and its `result`, whose `_nested.positions` are the walk's
  # own records by group, from which its `nested` children are minted. The accessor answers three
  # questions: its child at a position (`child { position; }`); asked with `minted`, WHAT the walk
  # minted there (`containerNodeAt`), read off those records and never re-derived from a type:
  # `true` a container node, `false` another child, `null` nothing; and, asked with `positions`, the
  # group's records themselves, which an `attrsOf` of nested trees at the root folds instead of
  # splitting its definitions again (`types.nix` `attrsOfWith`, den-hoag-c7jkw.1). One field answers
  # all three, so an accessor record costs nothing for the second or the third.
  evAt = host: group: {
    position = [ ];
    containerNodes = true;
    child =
      site:
      if site ? __genMergeMinted then
        let
          r = host.result._nested.positions.${group}.${builtins.toJSON site.position} or null;
        in
        if r == null then null else r.mode == "container"
      else if site ? positions then
        host.result._nested.positions.${group}
      else
        host.reader.getNta "nested" group (builtins.toJSON site.position) knotAttr;
  };
  # A type bound at a declared option or at the freeform plane, threaded where it may nest and the
  # evaluation reads its nested trees as children (`mode.reader`). The public `mergeOption` carries
  # no reader, so a nesting type there folds CALLED, and refuses.
  threadedIn =
    mode: group: type:
    if mode ? reader && interface.canNest type then threadedAs (evAt mode group) type else type;

  # ── THE KEY WALK (den-hoag-n6dh7 item 2; OQ9 (M′); S1 RULED (ii) for class (b), (iii) for (a)) ──
  # Which positions of an option's value are nested trees, each with the ADDRESSES of the
  # definitions its fold receives. The walk reads the containers' own `split` (the binding their
  # value folds read, so the positions it keys are the positions a fold reads), and at each element
  # takes the fold's own passes over the element's definitions — discharge, priority, order — in
  # their path-carrying form, so each surviving definition keeps the path that reaches it.
  #
  # A definition here is `{ file; value; at; }`: `at` is its path from the addressed group's list
  # (`[ i "value" … ]`). `split` builds each element's definitions from its input's, keeping `file`,
  # so the walk hands it definitions whose `file` is the whole record and reads the address back
  # off each element's; an element adds the step that selects it from that definition's value
  # (`listOf`'s step is `[ d i ]`, whose `d` selects the DEFINITION, so its value step is `i`).
  # A list of property-free definitions is its own answer (every pass is the identity on it: one
  # bare definition each, all at the default priority, none an order marker), so it is returned
  # whole, as `dischargeProperties`' own `isProperty` fast path does per value.
  addressedDefs =
    defs:
    if all (d: !(isAttrs d.value && d.value ? _type)) defs then
      defs
    else
      let
        discharged = concatMap (
          d:
          map (x: {
            inherit (d) file;
            inherit (x) value priority;
            at = d.at ++ x.path;
          }) (dischargePropertiesAt d.value)
        ) defs;
        winners = filterOverrides discharged;
      in
      if any (w: isOrderMarker w.value) winners then
        sortProperties (
          map (w: if isOrderMarker w.value then w // { at = w.at ++ [ "content" ]; } else w) winners
        )
      else
        winners;

  # INVARIANT REFUSALS of the key walk (den-hoag-t1j4z Case B, ADR-0039). Below a step under an
  # over-approximating container, every position `containerAt` holds is a container node, a union with
  # a container member included, so the walk never keys such a container in place. These are reached
  # only where the walk and `containerAt` disagree about a type, which is a gen-merge defect, not a
  # declaration's.
  stepContainerInvariantRefusal =
    group: under: t:
    "gen-merge: nta: option `${showOption group}': invariant: the key walk reached `${t.name or "<container>"}' of nested trees below a step under `${under}' as no container node, where `containerAt' makes it one; the walk and `containerAt' disagree. This is a gen-merge defect";
  # A definition a FOREIGN merge built (the threaded split's site, below a nixpkgs container's own
  # merge) has no declaration address: the merge may reorder, filter, merge or construct its
  # definitions, and hands each only nixpkgs' `{ file; value; }`, so no declaring position survives
  # it (ADR-0034: what has no structural identity gets none, and a named refusal where one is
  # demanded). Read only by a nesting type that declares `nests.declAt`.
  foreignDeclAtRefusal =
    group: loc: t:
    "gen-merge: `declAt': option `${showOption group}': the definition at `${showOption loc}' was built by the foreign merge of `${t.name or "<container>"}', which hands each definition only `{ file; value; }' and states no declaring position, so it has no declaration address";
  unionStepContainerInvariantRefusal =
    group: under: u: pos: t:
    "gen-merge: nta: option `${showOption group}': invariant: the key walk reached `${u.name or "<union>"}' at position ${builtins.toJSON pos}, whose member `${t.name or "<container>"}' holds nested trees, below a step under `${under}' as no container node, where `containerAt' makes it one; the walk and `containerAt' disagree. This is a gen-merge defect";

  # ── THE CONTAINER NODE's POSITION (S1 arm (v), den-hoag-9d80v; den-hoag-t1j4z Case B) ──────────
  # Below a step under an over-approximating container (`lazyAttrsOf`, or any other: a consumer's
  # stepped `defineType` container, a renamed one), a position whose type keys its nested trees by
  # reading their definitions —
  # a container that is not itself a nested tree, or a union with such a member (looked through
  # `nullOr` and nested unions, as `unionKeys` walks them) — is promoted to a node of its own: the
  # node's key walk runs over its definitions only, exactly (`under = null`), so keying one of its
  # trees forces no sibling's. The one predicate is read by the walk (`keyWalk`) and by the fold
  # (`mergeDefsThreaded`), so a node the walk mints is the node the fold reads: `lazyAttrsOf` marks its
  # elements itself, and every other container's fold reads what the walk minted at its position
  # (`readsMintedNode`, at the `defineType` door). `nullOr` at the position itself adds no step and is
  # looked through by both, never promoted.
  containerAt =
    loc: t:
    isAttrs t
    && !(interface.isNesting t)
    && interface.canNest t
    && (
      if t ? choose then
        any (containerMemberAt loc) (t.carries.alternatives or [ ])
      else
        (t.name or null) != "nullOr" && t ? split
    );
  containerMemberAt =
    loc: t0:
    let
      m = interface.homedAt "evalModuleTree" loc t0;
    in
    if isAttrs m && (m.name or null) == "nullOr" then
      containerMemberAt loc m.carries.element
    else
      containerAt loc m;

  # The member a union's fold folds through: `choose`, repeated through nested unions; `null` where
  # no member takes every definition (the fold's refusal).
  chosenAt =
    loc: defs: t:
    if isAttrs t && t ? choose then
      let
        c = t.choose loc (plainDefs defs);
      in
      if c == null then null else chosenAt loc defs (interface.homedAt "evalModuleTree" loc c)
    else
      t;

  # A definition list as a fold reads it, without the walk's addresses.
  plainDefs = map (d: {
    inherit (d) file value;
  });

  # THE MEMBER A POSITION'S CHILD EVALUATES UNDER (den-hoag-n6dh7 item 2, v10): the type the host
  # fold's own `split` chain reaches at the child's position `rel`, replayed from a union's position
  # with each union's `choose` applied over that position's `loc` and definitions, and each
  # element's definitions passed through the fold's own passes first. The chain reads the bindings
  # the fold reads, so the fold's selection and the child's admission cannot disagree. `null` where
  # the chain does not reach the position: the candidate refusal.
  memberChain =
    t: rel: loc: defs:
    if !(isAttrs t) then
      null
    else if t ? choose then
      memberChain (interface.homedAt "evalModuleTree" loc (t.choose loc (plainDefs defs))) rel loc defs
    else if interface.isNesting t || !(t ? split) then
      (if rel == [ ] then t else null)
    else
      let
        # `nullOr`'s element adds no step, so it continues the chain at the same position.
        es = filter (e: take (length e.step) rel == e.step) (t.split loc (plainDefs defs));
        e = head es;
      in
      if es == [ ] then
        (if rel == [ ] then t else null)
      else
        memberChain (interface.homedAt "evalModuleTree" e.loc e.type) (drop (length e.step) rel) e.loc (
          addressedDefs (map (d: d // { at = [ ]; }) e.defs)
        );

  # `under`: `null` where every enclosing container keys EXACTLY (`attrsOf`, `listOf`, `nullOr`,
  # whose key sets already read each element's definitions to WHNF), else the name of the enclosing
  # container that OVER-APPROXIMATES (`lazyAttrsOf`, and every other split container whose fold sets
  # no mark: gen-aspects' `aspectsRoot`, or a freeform plane typed by one). The answer is a list of
  # `{ key; type; member; loc; defs; }`, where `member`
  # is the type the child evaluates under, forced only when the child's `result` reads it.
  #   · a nesting type IS a key, and its own member;
  #   · a UNION holding a CONTAINER member (`containerAt`) is keyed where it is READ: under an
  #     exact container it is a CONTAINER NODE, and at the walk's own root (an option's position, or
  #     a node's) its `choose` decides the member walked, as its fold's does, so no sibling's read
  #     runs a member's code;
  #   · so is a FOREIGN container `homedAt` threads (`__threadedForeign`): under an exact container
  #     it is a CONTAINER NODE, since only its own `merge` decides its steps; at the walk's own root
  #     it is walked through its `split`, as the position read is the position keyed;
  #   · any other UNION is walked member by member at its own position (below); the walk never
  #     applies `choose` there, so a union's member is decided where the child is read;
  #   · under an exact container, any other container is keyed where it is READ too, so no sibling's
  #     read splits or forces its definitions: an attribute-keyed one (`keyedOverAt`) keys
  #     over-approximately, by its definitions' attribute names, and every other one is a CONTAINER
  #     NODE (den-hoag-mda6f);
  #   · at the walk's own root, a container is walked through its `split`, where it keys exactly;
  #   · under an over-approximating container that ADDED NO STEP (`unique`, `coercedTo`, so the
  #     position is the walk's own root), the position is walked as the root is: that container's
  #     fold is its element's over the same definitions, so keying forces nothing the read does not;
  #   · below a step under any over-approximating container, a position `containerAt` holds is a
  #     CONTAINER NODE (arm (v), den-hoag-9d80v, generalized by den-hoag-t1j4z Case B): one record,
  #     marked `container`, whose own walk keys it over its own definitions (`containerNode`), so
  #     keying it forces no sibling; `nullOr` adds no step and is looked through.
  # Only an EXACT container's elements have their definitions forced to key them, as that
  # container's own fold forces them; an over-approximated position's definitions are a thunk,
  # read when its seed is.
  keyWalk =
    under: group: t: pos: loc: defs:
    if !(isAttrs t) || !(interface.canNest t) then
      [ ]
    else if interface.isNesting t then
      [
        {
          key = pos;
          type = t;
          member = t;
          inherit loc defs;
        }
      ]
    else if under != null && pos == [ ] then
      # AT THE WALK'S OWN ROOT (an option's position, or a container node's), UNDER A CONTAINER THAT
      # ADDED NO STEP (`unique`, `coercedTo`): the position is the one read, and its container's fold is
      # its element's over the same definitions, so keying the element forces nothing the read does
      # not (den-hoag-t1j4z, ADR-0039). It is walked as the root is. Below a step it is a container
      # node (the next arm).
      keyWalk null group t pos loc defs
    else if under != null && containerAt loc t then
      [
        {
          key = pos;
          type = t;
          member = t;
          container = true;
          inherit loc defs;
        }
      ]
    else if under == null && pos != [ ] && keyedOverAt loc t && containerAt loc t then
      # KEYED OVER-APPROXIMATELY: an attribute-keyed container at an exact container's element. Its
      # candidate keys are its definitions' attribute names, with no definedness pass, and its
      # elements are walked in the over-approximating regime (`under = "lazyAttrsOf"`), whose
      # positions key without forcing their definitions, and whose container elements are nodes
      # (none of them keys over-approximately, `keyedOverAt`). The key set is taken over the container's own
      # domain, through its fold's door (`admitsAll` over `admits`): a position with a definition
      # outside it is refused by name where it is read, before any key under it is read, so it has
      # none.
      if admitsAll t.admits defs then
        let
          # Each key's definitions, grouped once (as `mergeTree`'s `defsByKey`), in `defs`' order, so
          # each key is answered by a lookup rather than a scan of `defs`.
          defsByKey = builtins.zipAttrsWith (_: vs: vs) (
            map (
              d:
              mapAttrs (k: value: {
                inherit (d) file;
                inherit value;
                at = d.at ++ [ k ];
              }) d.value
            ) defs
          );
        in
        concatMap (
          k:
          keyWalk "lazyAttrsOf" group (interface.homedAt "evalModuleTree" (loc ++ [ k ]) t.carries.element) (
            pos ++ [ k ]
          ) (loc ++ [ k ]) (addressedDefs defsByKey.${k})
        ) (attrNames defsByKey)
      else
        [ ]
    else if under == null && pos != [ ] && containerAt loc t then
      # KEYED WHERE READ: any other container at an exact container's element (a union's `choose`, a
      # foreign container's own merge, a list's indices, which are the positions its definedness
      # pass leaves, another split container's own `split`, or an `attrsOf` over a container, whose
      # element's keys are that element's data). Under an exact container it is a CONTAINER NODE,
      # whose own walk runs only when the position is read, so no sibling's read forces or splits its
      # definitions (`unionNodeAt`).
      [
        {
          key = pos;
          type = t;
          member = t;
          container = true;
          inherit loc defs;
        }
      ]
    else if under == null && t ? choose && containerAt loc t then
      # At the walk's own root (an option's position, or a node's) the position IS the one read, and
      # a union holding a container member is keyed by the member its `choose` takes, as its fold is.
      let
        c = chosenAt loc defs t;
      in
      if c == null then [ ] else keyWalk null group c pos loc defs
    else if t ? choose then
      map (
        r:
        r
        // {
          type = t;
          member = memberChain t (drop (length pos) r.key) loc defs;
        }
      ) (unionKeys under group t pos loc defs t)
    else if !(t ? split) then
      [ ]
    else if under != null then
      (
        if (t.name or null) == "nullOr" then
          keyWalk under group (interface.homedAt "evalModuleTree" loc t.carries.element) pos loc (
            filter (d: d.value != null) defs
          )
        else
          throw (stepContainerInvariantRefusal group under t)
      )
    else
      let
        name = t.name or null;
        # `interface.keysExactly`, read inline: every container the walk splits would pay a call
        # (`ci/tests/nesting-keys.nix` `nesting-keys-keys-exactly-census` holds the two equal)
        exact = t.keysExactly or (name == "attrsOf" || name == "listOf" || name == "nullOr");
      in
      concatMap (
        e:
        keyWalk (if exact then null else name) group (interface.homedAt "evalModuleTree" e.loc e.type)
          (pos ++ e.step)
          e.loc
          (
            addressedDefs (
              map (
                # A threaded foreign split hands its foreign merge `{ file; value; }` alone, so a definition
                # that merge built carries no address back (`foreignDeclAtRefusal`); every other split is
                # gen's own and passes the carrier through. Below a foreign split the carrier is told apart
                # by its `at`, since the foreign merge may write an attrset `file` of its own. Tested inline:
                # a `let` binding costs every gen-native split a thunk.
                if t ? __threadedForeign then
                  d:
                  if isAttrs d.file && d.file ? at then
                    {
                      inherit (d.file) file;
                      inherit (d) value;
                      at = d.file.at ++ (if name == "listOf" then [ (prelude.last e.step) ] else e.step);
                    }
                  else
                    {
                      inherit (d) file value;
                      at = throw (foreignDeclAtRefusal group e.loc t);
                    }
                else
                  d: {
                    inherit (d.file) file;
                    inherit (d) value;
                    at = d.file.at ++ (if name == "listOf" then [ (prelude.last e.step) ] else e.step);
                  }
              ) e.defs
            )
          )
      ) (t.split loc (map (d: d // { file = d; }) defs));

  # A UNION's keys (v10, S1 RULED (ii)): each member that may nest, in order, at the union's own
  # position, which a union's members add no step to. A nesting member contributes that position; a
  # union member is walked by this same rule. A union holding a container member reaches this walk
  # only under an over-approximating container (`keyWalk` keys it where read otherwise). A position
  # two members key is ONE key (`listToAttrs` keeps the first). Under an
  # over-approximating container, below a step, a union with a container member is a container node
  # (`containerAt`), whose own walk takes this rule with `under = null`; at the walk's own root
  # `keyWalk` walks the union as the root is. So a container member reached here with `under` set is
  # an invariant refusal.
  unionKeys =
    under: group: u: pos: loc: defs: t:
    concatMap (
      mt0:
      let
        mt = interface.homedAt "evalModuleTree" loc mt0;
      in
      if !(isAttrs mt) || !(interface.canNest mt) then
        [ ]
      else if interface.isNesting mt then
        [
          {
            key = pos;
            inherit loc defs;
          }
        ]
      else if mt ? choose then
        unionKeys under group u pos loc defs mt
      else if !(mt ? split) then
        [ ]
      else if (mt.name or null) == "nullOr" then
        unionKeys under group u pos loc (if under == null then filter (d: d.value != null) defs else defs) {
          carries.alternatives = [ mt.carries.element ];
        }
      else if under != null then
        throw (unionStepContainerInvariantRefusal group under u pos mt)
      else
        [ ]
    ) (t.carries.alternatives or [ ]);

  # ★ GROWTH OVER EMPTY SEEDS, REFUSED BY NAME (den-hoag-n6dh7 item 4; OQ15's default (c),
  # *defaulted, reversible*). A child with an empty seed whose own walk keys an empty-seed position
  # adds a generation grown by the TYPE alone, and a recursive nesting type grows such generations
  # without end: enumeration would hang, with no abort and no refusal. A position record counts the
  # run as `emptyRun`: `0` where the seed is non-empty, else its host's own `emptyRun` plus one (a
  # root counts `0`). Where it would exceed `importedTypeWalkFuel` (the S2 walk's bound), the walk
  # refuses at that key. THE STATED PRICE: an undefined chain of `importedTypeWalkFuel` or more
  # directly typed nesting levels is refused even where it is finite; Nix has no reference equality,
  # so recursion and depth cannot be told apart, and the fuel is the bound S2 already prices.
  emptyRunRefusal =
    loc:
    "gen-merge: `evalModuleTree': option `${showOption loc}' holds a nested tree with no definition inside ${toString interface.importedTypeWalkFuel} enclosing nested trees that have none either: a nesting type that holds itself grows undefined trees without end, and the walk refuses past its fuel of ${toString interface.importedTypeWalkFuel} rather than hang. Define the position, or reach the recursion through a container whose keys are data (`attrsOf', `listOf')";

  # The declared options of a tree, in declaration order, each with the definitions the realizer
  # routed to it. ONE ROUTING (den-hoag-n6dh7 L5c): `mergeTree` already ran this descent once to
  # build `declaredConfig`, so this reads its result's exposed `declaredPairs` / `subDefs` / `opts`
  # / `loc` instead of re-running `pushDownProperties` and the key walk a second time. `r` is a
  # `mergeTree` result record; a declared GROUP's own result (`x.m`) carries the same shape, so the
  # recursion below is the same walk `mergeTree` already performed, read rather than repeated.
  realizedLeaves =
    r:
    concatMap (
      x:
      if x ? group then
        realizedLeaves x.m
      else
        [
          {
            path = r.loc ++ [ x.name ];
            opt = r.opts.${x.name};
            defs = r.subDefs x.name;
            inherit (x) m;
          }
        ]
    ) r.declaredPairs;

  # The `nested` NTA's groups for one tree: per group its `definitions` (`nestedDefinitions` reads
  # them into the host attribute every seed addresses, one list per group, by group ordinal) and its
  # position records (`nestedPosition`, which decides each position's report mode), from which the
  # builder's key → seed map is read where it is asked. A group is an option path, `toJSON`-encoded,
  # and the freeform plane's reserved `freeform` (never a JSON list). An option group's definitions
  # are the fold's: the routed definitions and the option's default, discharged, priority-resolved
  # and ordered. The freeform plane's are the coalesced definitions its fold takes whole, with nothing
  # discharged above its container.
  nestedGroups =
    args@{
      prefix,
      carried,
      strict,
      leaves,
      normalize,
      freeform,
      emptyRun,
    }:
    let
      optionGroup = l: {
        name = builtins.toJSON l.path;
        loc = prefix ++ l.path;
        type = l.opt.type or null;
        hostMode = { inherit carried strict; };
        # ONE DISCHARGE (den-hoag-i4c0n C1; item 2, gate P2): the fold's own `typeDefs`, read off the
        # option's merge record. The first arm is where forcing `m` would meet `mergeOptionWith`'s
        # "used but not defined" guard, and there the walk below answers `[ ]` too. An option that
        # declares `readOnly` or `apply` is tested by KEY: forcing `m` would force the `readOnly`
        # value, which the walk never reads, and its re-wrapped `m` carries no `typeDefs` anyway.
        # The last arm runs the passes wherever `m` carries no `typeDefs` (also a warm-reused leaf).
        definitions =
          if l.defs == [ ] && !(l.opt ? default) then
            [ ]
          else if !(l.opt ? readOnly) && !(l.opt ? apply) && l.m ? typeDefs then
            l.m.typeDefs
          else
            map (d: { inherit (d) file value; }) (
              addressedDefs (map (d: d // { at = [ ]; }) (normalize (withDeclaredDefault l.opt l.defs)))
            );
      };
      # No freeform group where the tree declares no freeform type (L5f, its freeform half), decided
      # by KEY presence (`freeform.declared`), never by the type's value: every group's read forces
      # this list's spine, so a value test would force a freeform type written through `config` on
      # every child read. The `canNest` filter over the option groups is NOT taken, for the same
      # reason: it makes the group set a function of every declared option's type.
      groups =
        map optionGroup leaves
        ++ optional freeform.declared {
          name = "freeform";
          loc = prefix;
          inherit (freeform) type;
          # Every freeform-plane position folds by the CALLED form.
          hostMode = {
            carried = false;
            inherit strict;
          };
          definitions = map (d: { inherit (d) file value; }) freeform.defs;
        };
      positionsOf =
        j: g:
        map
          (
            r:
            if emptyRun >= interface.importedTypeWalkFuel && r.defs == [ ] then
              throw (emptyRunRefusal r.loc)
            else
              # `nestedPosition`'s record, and what the child's own evaluation reads besides (the v10
              # amendment): the `member` it evaluates under (the walk's `split` chain, lazy), the
              # definitions its seed addresses, in seed order, which it evaluates (arm (B), owner
              # ruling 2026-09-28), and `emptyRun` (item 4, OQ15 (c)).
              {
                inherit (r)
                  key
                  loc
                  member
                  defs
                  ;
                address = map (d: {
                  attr = "definitions";
                  def = j;
                  inherit (d) at;
                }) r.defs;
                mode = if r ? container then "container" else positionMode g.hostMode r.type r.key;
                emptyRun = if r.defs == [ ] then emptyRun + 1 else 0;
              }
          )
          (
            keyWalk null g.loc
              (
                if
                  g.type ? carries
                  && !(
                    # presence first, so a gen root that crossed nothing pays no call
                    g.type ? substructure.mount
                    ||
                      (
                        g.type ? carries.element.substructure.mount
                        || g.type ? carries.element.carries.element.substructure.mount
                        || g.type ? carries.element.carries.element.carries.element
                      )
                      && interface.crossedRoot g.type
                  )
                then
                  g.type
                else
                  interface.homedRootAt "evalModuleTree" g.loc g g.type
              )
              [ ]
              g.loc
              (
                prelude.imap0 (
                  i: d:
                  d
                  // {
                    at = [
                      i
                      "value"
                    ];
                  }
                ) g.definitions
              )
          );
      positions = listToAttrs (
        prelude.imap0 (j: g: {
          inherit (g) name;
          value = listToAttrs (
            map (p: {
              name = builtins.toJSON p.key;
              value = p;
            }) (positionsOf j g)
          );
        }) groups
      );
    in
    # Every field is a binding the walk already holds, so the record costs no thunk: the per-group
    # `definitions` (`nestedDefinitions`) and the `nta.nested` product are derived where they are
    # read, and `inputs`, the groups' own inputs, is read back by `seedDeclAts` alone
    # (`nestedDeclAts`, den-hoag-8hlo3 U1).
    {
      inherit groups positions;
      inputs = args;
    };

  # Leaf combine — one winner passes through; multiple equal-priority winners must be equal
  # (mergeEqualOption), else a conflict. Byte-mode does not deep-merge unknown leaves.
  mergeLeaf =
    loc: winners:
    if length winners == 1 then
      (head winners).value
    else
      let
        vals = map (w: w.value) winners;
        first = head vals;
      in
      if all (v: v == first) vals then first else throw (showConflict loc winners);

  # ── mergeDefaultOption — the nixpkgs SHAPE-DIRECTED default-merge law ─────────────────────────
  # The nixpkgs `lib.mergeDefaultOption` analogue: the combination law nixpkgs applies at a position
  # where no PER-KEY type was authored. It combines by the definitions' RUNTIME SHAPE rather than by
  # requiring them to agree.
  #
  # ★★★ IT SITS BESIDE `mergeLeaf`, NOT IN PLACE OF IT. `mergeLeaf`
  # above remains this engine's no-`.merge` default and keeps its agree-or-refuse posture, and no
  # typed option's merge semantics move. Two routes inside this library reach it, both through
  # `mergeDescriptorDefault` below: `mkOptionType`'s default for a descriptor stating no fold, which
  # is nixpkgs' constructor default rather than a leaf default, and an untyped option defined more
  # than once at the four combining shapes (`mergeUntyped`, below), which is also
  # `types.unspecified`'s fold.
  # The full statement of what it means and does not claim is at the public export
  # (lib/default.nix), which is where a caller meets it.
  #
  # THE ARMS, in nixpkgs' own order (`lib/options.nix` `mergeDefaultOption`), because for a
  # HOMOGENEOUS definition list the shape predicates are mutually exclusive and the order is
  # observable only at the singleton fast path and the terminal refusal:
  #   one definition ......................... that definition's value
  #   all functions .......................... applied POINTWISE, results merged by this same law;
  #                                            "function" is nixpkgs' `lib.isFunction` (gen-prelude's
  #                                            reader): a lambda, or an attrset whose `__functor`
  #                                            yields one, such as a `setFunctionArgs` wrapper
  #   all lists .............................. concatenated
  #   all attrsets ........................... `//`-folded (SHALLOW, last definition wins per key)
  #   all bools .............................. OR-folded — differing bools do NOT refuse
  #   all strings ............................ concatenated — differing strings do NOT refuse
  #   all ints AND all equal ................. that value
  #   anything else .......................... a named refusal
  # ⇒ ONLY differing ints and type-heterogeneous definition lists reach the refusal.
  #
  # ★★ ONE MEASURED DIVERGENCE FROM nixpkgs, DECLARED RATHER THAN INHERITED — the MULTI-FUNCTION
  # arm, and it is the only arm that diverges. nixpkgs writes it
  # `x: mergeDefaultOption loc (map (f: f x) list)`, passing RAW VALUES into a parameter whose first
  # act is `getValues` (`map (x: x.value)`). That mismatch has two faces, both measured at the
  # pinned rev:
  #   · functions returning anything but an attrset carrying a `value` attribute make nixpkgs die on
  #     `expected a set but found a list` — and die UNCATCHABLY, with a live control in the same run
  #     showing an ordinary refusal on the same instrument IS catchable;
  #   · functions that DO return `{ value = …; }` have that field silently unwrapped by the stray
  #     `getValues`, so nixpkgs merges the payloads where this law merges the records.
  # Reproducing either would be bug-compatibility rather than parity, and the first would put an
  # uncatchable abort inside a law whose whole contract is a value or a named refusal (ADR-0025 §1).
  # So the recursion re-enters with each DEFINITION's value applied, which is what the arm plainly
  # means: `[ (x: [x]) (x: [x+1]) ]` applied to `1` gives `[ 1 2 ]` — pointwise then merged,
  # observably NOT composition, which would give `[ [ 2 ] ]`. It recurses over definitions rather
  # than values so the files survive it: the terminal refusal is `showConflict`, the ONE conflict
  # text, naming every definition's file (ADR-0025 item 1). Every OTHER arm is byte-equal to
  # nixpkgs' on the same input, and the parity suite asserts that against the live nixpkgs rather
  # than a transcription.
  mergeDefaultOption =
    loc: defs:
    let
      list = map (d: d.value) defs;
    in
    if length list == 1 then
      head list
    else if all prelude.isFunction list then
      (x: mergeDefaultOption loc (map (d: d // { value = d.value x; }) defs))
    else if all isList list then
      concatLists list
    else if all isAttrs list then
      foldl' (a: b: a // b) { } list
    else if all builtins.isBool list then
      foldl' (a: b: a || b) false list
    else if all builtins.isString list then
      concatStringsSep "" list
    else if all builtins.isInt list && all (x: x == head list) list then
      head list
    else
      throw (showConflict loc defs);

  # Whether the values several definers state for one key DIFFER, decided on each definer's OWN
  # value slot: `==` over a subject that contains the value (`[ v ]`), which is ADR-0034's COMPARED
  # limb. `==`'s identity short-circuit compares value SLOTS on upstream Nix and Determinate and
  # heap objects on Lix; a singleton list keeps its element's slot, so the three agree wherever
  # the definers hold one value in one slot, and a shared value is decided at its WHNF without
  # walking it. One definer never differs, and its value is not forced: the length guard lives
  # here and not at a caller, because every key of a union reaches this binding at the `withArgs`
  # relation (lib/types.nix `mkSubmodule`), and without the guard `[ v ] == head cells` forces a
  # single definer's value on Nix and Determinate and not on Lix. Its two callers are
  # `unionAgreeing` below and that relation; the core export says why they share it.
  slotsDiffer =
    vs:
    let
      cells = map (v: [ v ]) vs;
    in
    length vs > 1 && !all (c: c == head cells) cells;

  # The union of several attrset definitions, nixpkgs' `//` fold over them, with each shared key's
  # agreement (`slotsDiffer`) decided INSIDE that key's own value. The key set is the union's; reading
  # one key never forces another key's `==`, so a key that reads a sibling of the same option serves
  # as nixpkgs serves it, and a disagreement is refused where its key is read. `refusal k vs` is the
  # caller's text for key `k`, whose definers' values are `vs`. The price of the placement: with every
  # value forced, about one thunk and two calls per key over a fold that decides every shared key
  # before returning the set; a read of the key set or of one sibling pays no other key's `==`.
  unionAgreeing =
    refusal: defs:
    let
      merged = foldl' (res: d: res // d.value) { } defs;
      slots = builtins.zipAttrsWith (_: vs: vs) (map (d: d.value) defs);
    in
    builtins.mapAttrs (k: v: if slotsDiffer slots.${k} then throw (refusal k slots.${k}) else v) merged;

  # The CONSTRUCTOR'S default: the fold a `mkOptionType` descriptor stating no fold receives, as
  # nixpkgs' `mkOptionType` takes `merge ? mergeDefaultOption` (lib/interface.nix `importDescriptor`
  # applies it). It is the law above with a named refusal kept at the two arms where nixpkgs'
  # own answer is SILENT or absent — the parity criterion, owner-ruled 2026-09-25: "Take nixpkgs'
  # value where gen-merge today refuses or silently diverges, EXCEPT WHERE NIXPKGS' OWN VALUE IS
  # SILENT (keep a named refusal there)".
  #   · attrsets sharing a key with DIFFERING values: `//` keeps the last and drops the rest without
  #     a word. Disjoint keys, and shared keys carrying equal values, lose nothing and fold as above.
  #   · functions: nixpkgs aborts uncatchably, or silently unwraps a `{ value = …; }` result.
  #     Functors are functions here as in the law above; the conflict text renders one as `<a set>`.
  # The price, stated with the ruling: a nixpkgs module relying on silent last-wins attrset merging
  # under a check-only type is refused here. The exported law keeps both arms, because its ruled
  # caller (gen-aspects' freeform arm) is not this one. A disagreement is refused at the key's own
  # path (`unionAgreeing`), so a key whose definitions read a sibling of the same option serves as
  # nixpkgs does; deciding every key before returning the set would recurse uncatchably there.
  mergeDescriptorDefault =
    loc: defs:
    let
      list = map (d: d.value) defs;
    in
    if length list > 1 && all prelude.isFunction list then
      throw (showConflict loc defs)
    # Attrsets fold by `unionAgreeing`, so a disagreement is refused at its key, by the one conflict
    # text at that key's path, naming the files that set it.
    else if length list > 1 && all isAttrs list then
      unionAgreeing (
        k: _:
        showConflict (loc ++ [ k ]) (
          map (d: d // { value = d.value.${k}; }) (filter (d: d.value ? ${k}) defs)
        )
      ) defs
    else
      mergeDefaultOption loc defs;

  # The UNTYPED option's fold. nixpkgs gives an option that states no type `types.unspecified`
  # (`fixupOptionType`), a `mkOptionType` stating `name` alone, so it folds by the constructor
  # default, which here is `mergeDescriptorDefault` above. It is taken at the four shapes nixpkgs
  # serves by combining: lists concatenate, strings concatenate, bools OR, attrsets union (an equal
  # shared key serves, a differing one is refused by name). Every other shape keeps the leaf fold:
  # null, floats, paths, ints and mixed shapes serve an agreement and refuse a disagreement, which
  # accepts more than nixpkgs' law does (ADR-0039's stated refuse half), and functions are compared,
  # never applied, since nixpkgs' function arm aborts or silently unwraps. Its one caller
  # (`mergeDefsRichWith`) hands it two or more definitions.
  mergeUntyped =
    loc: defs:
    let
      list = map (d: d.value) defs;
    in
    if
      all isList list
      || all builtins.isString list
      || all builtins.isBool list
      || all isAttrs list && !all prelude.isFunction list
    then
      mergeDescriptorDefault loc defs
    else
      mergeLeaf loc defs;

  # mergeOneOption — the nixpkgs `lib.mergeOneOption` helper: exactly one definition permitted
  # (else throw). Exported for consumers whose custom `(loc, defs)` merges want unique-def semantics
  # (e.g. gen-schema's ref types).
  mergeOneOption =
    loc: defs:
    if defs == [ ] then
      throw "gen-merge: the option `${showOption loc}' is used but not defined"
    else if length defs != 1 then
      throw "gen-merge: the option `${showOption loc}' is defined multiple times, but may only be defined once"
    else
      (head defs).value;

  # The declared default seeds the fold (den-hoag-12e7r): nixpkgs' `evalOptionValue` puts it FIRST among
  # the definitions (`defs' = [ default ] ++ defs`), and every order-sensitive merge downstream reads
  # that order, a nested tree's module reversal included. The one place the default joins a definition
  # list: `mergeOptionWith`'s fold, `optionGroup`'s `definitions` and `declAtsOfGroup`'s addresses, so
  # the addresses stay aligned with the definitions they name.
  withDeclaredDefault =
    opt: defs:
    if opt ? default then
      [
        {
          file = "<default>";
          value = mkOptionDefault opt.default;
        }
      ]
      ++ defs
    else
      defs;

  # An option merge = mergeDefs + default (as the seed def, `withDeclaredDefault`) + readOnly + apply.
  # `mergeOption` is the public value-only form; `mergeOptionWith coreShortCircuit` is the RICH realizer
  # form (`{ value; prov }`), threading the opt-in kernel into the fold via `mergeDefsRichWith`. The
  # `<default>` def (`file = "<default>"`, priority 1500) is what the fold reads back for the record's
  # `defaulted` flag. NOTE: a present `default =` adds a second def, which demotes a lone core def to
  # fall-through — still byte-identical (the plain `values` beats the mkOptionDefault), only without
  # the spine skip.
  #
  # COMMON CASE (no `apply`, no `readOnly` — the bulk of the surface): the rich record is returned
  # STRAIGHT THROUGH — the realizer's value tree reads `.value`, the provenance tree reads `.prov`, and
  # NO extra attrset is allocated per option (the always-on channel's per-leaf cost stays ~1 record,
  # not a re-wrap). Only `apply`/`readOnly` options take the wrapping branch (they transform the value
  # and/or gate on def count, so they re-wrap; `.prov` rides through unchanged, still lazy behind the
  # same `_ro` gate the value forces).
  mergeOption =
    loc: optDecl: rawDefs:
    (mergeOptionWith {
      coreShortCircuit = false;
      carried = true;
      strict = false;
    } loc optDecl rawDefs).value;
  # `mode` = `{ coreShortCircuit; carried; strict; }`, one record rather than three arguments: an
  # argument added here is an environment allocated on every declared leaf, and the record is built
  # once per evaluation. `carried` says whether this evaluation's undeclared report is read by anyone;
  # `strict` is this evaluation's effective strictness, which the reporting fold hands down to the
  # nested tree whose report it carries.
  mergeOptionWith =
    mode: loc: optDecl: rawDefs:
    let
      hasApply = optDecl ? apply;
      readOnly = optDecl.readOnly or false;
      withDefault = withDeclaredDefault optDecl rawDefs;
      merged =
        # An empty-able type is NOT an error when undefined — fall through to the fold, whose
        # `winners == [ ]` arm is the single place `emptyValue` is consulted (nixpkgs answers both
        # arrivals at one site too). Only a type with no `emptyValue.value` short-circuits to the throw.
        #
        # The throw is the VALUE's, not the record's. Provenance answers who defined the option, and
        # for a leaf nobody defined that answer is a record: the one an empty-able type with no
        # definitions already publishes, and nixpkgs' `definitionsWithLocations = [ ]`. A record that
        # threw instead would leave a reader (`bandedLeaves`) only `tryEval` to learn "undefined",
        # and `tryEval` cannot tell this refusal from a module's own error raised while these same
        # definitions are collected, so a DEFINED leaf would read as undefined (den-hoag-zakjg U1).
        if rawDefs == [ ] && !(optDecl ? default) && !(hasEmptyValue (optDecl.type or null)) then
          let
            undefined = throw "gen-merge: the option `${showOption loc}' is used but not defined";
          in
          {
            value = undefined;
            undeclared = undefined;
            typeDefs = [ ];
            prov = {
              defs = [ ];
              winners = [ ];
              priority = null;
              defaulted = false;
            };
          }
        else
          # An ABSENT `type` is the untyped option; a `type` STATED as `null` is a value in type
          # position, refused where the fold forces it, like any other non-type.
          #
          # Every other type is folded as HOMED where it is bound to its position (den-hoag-n6dh7
          # item 5, gate C9): a recognised foreign container that may nest is folded as gen's own,
          # and an unrecognised one declaring a gen nesting element threads through its own rebuild
          # or is refused by name before any fold is taken (`interface.threadedForeign`). A gen leaf
          # checker (`verify`) and a gen container (`carries`) are their own home and are answered
          # here, inside the argument's one thunk, so a gen option pays a
          # presence test and not a call (ez1yq C2 `leaf-cost`). A type that may nest is folded
          # THREADED (den-hoag-n6dh7 item 5): its nested trees are children of this evaluation,
          # read at the group this option's path names, relative to the tree's prefix.
          mergeDefsRichWith mode loc (
            if optDecl ? type && optDecl.type == null then
              throw (declaredTypeRefusal loc null)
            else if (optDecl.type or null) ? verify then
              optDecl.type
            else
              threadedIn mode (builtins.toJSON (drop (length mode.prefix) loc)) (
                # a crossed module set, or a container carrying one, is mounted (`interface.crossedRoot`)
                if
                  (optDecl.type or null) ? carries
                  && !(
                    # presence first, so a gen root that crossed nothing pays no call
                    optDecl.type ? substructure.mount
                    ||
                      (
                        optDecl.type ? carries.element.substructure.mount
                        || optDecl.type ? carries.element.carries.element.substructure.mount
                        || optDecl.type ? carries.element.carries.element.carries.element
                      )
                      && interface.crossedRoot optDecl.type
                  )
                then
                  optDecl.type
                else
                  interface.homedRootAt "evalModuleTree" loc mode (optDecl.type or null)
              )
          ) withDefault;
    in
    if !hasApply && !readOnly then
      merged
    else
      let
        # The declared default counts as a setting, as nixpkgs' `evalOptionValue` counts `defs'`: a
        # readOnly declaration with a default has fixed the value, so one definition beside it is a
        # second setting (ADR-0039, den-hoag-1gv6r).
        _ro =
          if readOnly && length withDefault > 1 then
            throw "gen-merge: the option `${showOption loc}' is read-only, but it is defined ${toString (length withDefault)} times${
              if optDecl ? default then " (its declared default counts as one)" else ""
            }"
          else
            null;
        applied = if hasApply then optDecl.apply merged.value else merged.value;
      in
      {
        value = builtins.seq _ro applied;
        prov = builtins.seq _ro merged.prov;
        # Threaded unchanged — an option that is BOTH `moduleTree`-typed and carries `apply`/
        # `readOnly` must not lose its undeclared report at this second re-wrap seam.
        undeclared = builtins.seq _ro merged.undeclared;
        typeDefs = builtins.seq _ro merged.typeDefs;
      };

  # ── STRATUM 1 — THE DECLARATION FOLD. NOT A FIXPOINT ──────────────────────────────────────────
  # ADR-0033, whose operative clause is `NOTHING CONSUMES ITS OWN STRATUM'S IN-FLIGHT OUTPUT`, and
  # whose closing word names the count: `two-level types`. This engine is a two-level type system,
  # so it has exactly two strata:
  #
  #   1 · DECLARATION — `options`: a FOLD over the flattened module list. Reads nothing from 2.
  #   2 · VALUE       — `config` and the seven fields beside it: the injected evaluator's ordinary
  #                     demand-driven path over stratum 1's SETTLED output.
  #
  # Stratum 2 consuming stratum 1's settled output is exactly what the clause licenses; there is no
  # cycle here, so — in the clause's own words — there is no cycle check to run.
  #
  # ★★ WHAT A MODULE FUNCTION IS APPLIED TO HERE, AND WHY IT IS A POISON RATHER THAN `{ }`. A fold
  # over the module list must still APPLY each module, and a module's formals are `config`,
  # `options` and its own `_module.args`. None of the three is available at this stratum: `config`
  # and the module args are stratum 2's output, and `options` is THIS stratum's own in-flight
  # output. Binding any of them to `{ }` would answer SILENTLY AND WRONGLY — a declaration gated on
  # `config.flag` would quietly take the false arm — so each is bound to a thrown, `tryEval`-
  # catchable refusal naming what was demanded. What ADR-0033 forbids becomes inexpressible with a
  # reason attached, instead of `infinite recursion encountered` with none.
  #
  # ★ THE REFUSAL IS TOTAL OVER THE THREE SHAPES AND IT IS ONE MECHANISM, not three checks:
  #   · a module whose option KEY SET is a function of `config` — ADR-0033's own example of a gate
  #     conditionally declaring an option;
  #   · a module whose `imports` TARGETS are read from `config` — stratum 1 consuming stratum 2,
  #     the residue ADR-0033 leaves open and the owner ruled refused (arm A, 2026-09-14). The
  #     composition it made expressible belongs at the composing library's own stratum, which is
  #     where it has since been relocated;
  #   · a module whose option PRESENCE reads `options`, or whose declaration reads one that no
  #     earlier pass resolved — the in-flight clause read literally. A declaration that reads an
  #     earlier-resolved one (nixpkgs' `doRename`, whose alias leaf copies its target's `type`) is
  #     admitted by the guard's staged passes (`stagedDeclarations`).
  # Forcing the declaration side is what raises them, so none is a predicate that can drift from
  # the property it tests.
  #
  # ★ WHAT IS ADMITTED, MEASURED AND NOT ASSUMED: an option's VALUE reading `config`, an option's
  # TYPE ARGUMENT reading `config` (the registry idiom `mkInstanceRegistry config.<kind>`), two
  # such declarations merging, and a module arg read in a `config` section. All four are stratum-2
  # reads and none forces the poison. What refuses is the option's own IDENTITY or PRESENCE moving
  # with `config` — the class ADR-0033 rules inadmissible.
  #
  # ★★★ WHAT THIS FOLD IS NOT, MEASURED IN SITU AND NOT ASSUMED. It is the published
  # DECLARATION-ONLY entry and the engine's GUARD — it is NOT the producer of the full result's
  # `options` field. An option DESCRIPTOR carries stratum-2 values in its own fields (`default`,
  # `apply`), and those are value-plane reads ADR-0033 does not forbid:
  # `mkOption { default = config.n; }` is supported, idiomatic, and pinned by this suite. Producing
  # the result's `options` from this fold would capture the poison in every such thunk and refuse
  # them — measured, 10 cells across `merge`, `moduleArgs`, `oracle` and `differential`, every one
  # of them an option default reading `config` or a config-derived module arg.
  #
  # So the stratification is held BY THE REFUSAL rather than by the binding: the guard forces this
  # fold's declaration SPINE — the key set and the imports expansion, never a descriptor field — so
  # any module whose DECLARATION plane genuinely reads stratum 2 is refused before the real fold
  # runs. On every admitted tree, stratum 1 provably reads nothing from stratum 2, which is the
  # property ADR-0033 asserts; what would otherwise diverge as `infinite recursion encountered`
  # now refuses by name, catchably, at the fold.
  #
  # `declEntries`, `sitesAt` and `options` are published together because every refusal on this
  # plane names the files that declared the option, and a second walk to recover them would be a
  # second answer to `which module declared this` that can drift from the first.
  #
  # `positioned`: a positioned evaluation's `name` is a key of `declArgs` too, refusing as any
  # value-stratum argument does unless a caller supplied it, so a module reading `name` takes
  # `callD`'s elided application. A curried flag, and not a key of the argument set: every nested
  # evaluation's guard builds that set, and a key on it is paid per evaluation.
  #
  # `onRedeclare`: the redeclaration step, curried the same way. `declarationStratum` and
  # `declarationStratumPositioned` pass `redeclareDecl`; the guard's `declarationSpine` and
  # `declarationSpinePositioned` pass `spineRedeclare`, which keeps the later operand and merges no
  # type. The four bindings sit beside `namePlaceholder`.
  declarationStratumWith =
    positioned: onRedeclare:
    {
      modules,
      specialArgs ? { },
      prefix ? [ ],
      optionsView ? null,
    }:
    # Closedness is decided first (see THE DECLARATION GUARD), once. On a closed set `callD` returns
    # every module unchanged, so the closed branch folds with `moduleClosure (m: m)` and binds none of
    # `declArgs`, `inadmissible` and `callD`; it publishes `flat` and `validated` as well, for the
    # value stratum to share. `isList` because `declaredOptions` passes the caller's raw field. The
    # branch spells `declEntries` a second time: a shared top-level helper costs a load thunk.
    if
      isList modules
      && all isAttrs modules
      && builtins.catAttrs "__functor" modules == [ ]
      && builtins.catAttrs "imports" modules == [ ]
      && builtins.catAttrs "require" modules == [ ]
    then
      let
        flat = moduleClosure (m: m) modules;
        declEntries = prelude.imap0 (i: e: {
          idx = i;
          file = e._file;
          options = optionsOf (moduleSyntaxChecked e).content;
        }) flat;
        sitesAt = declaringSitesAt (length prefix) declEntries;
        validated = map (e: validateDeclSubtree prefix e.options) declEntries;
      in
      {
        inherit
          declEntries
          sitesAt
          flat
          validated
          ;
        options = mergeOptionDeclTrees (onRedeclare sitesAt) prefix validated;
      }
    else
      let
        inadmissible =
          subject: demand:
          throw "gen-merge: a module ${demand} while its own declarations were being folded, and the declaration stratum does not consume the value stratum's output (nothing consumes its own stratum's in-flight output, so the option key set is unconditional). Declare the option unconditionally and gate its `config' instead${
            if subject == "options" then
              ""
            else
              ", or compose the modules before evaluation rather than through `imports = [ config.… ]'"
          }";

        # A caller key among `config`/`options`/`prefix` would be written over by the right operand and
        # reach no module, so it refuses by name (ADR-0025 item 1), as at `baseArgs`. The guard is
        # inline and the key list is built only on the refusing branch: a new binding on this path
        # costs a constant thunk per nested evaluation, which the hub perf-bench prices.
        declArgs =
          (
            if !(specialArgs ? config || specialArgs ? options || specialArgs ? prefix) then
              specialArgs
            else
              let
                stated = filter (k: specialArgs ? ${k}) [
                  "config"
                  "options"
                  "prefix"
                ];
              in
              throw (
                "gen-merge: `specialArgs' cannot supply the base module argument"
                + (if length stated == 1 then " " else "s ")
                + concatStringsSep ", " (map (k: "`${k}'") stated)
                + "; the engine injects its own value there, so the caller's would be discarded rather than used"
              )
          )
          // (
            if positioned then
              {
                config = inadmissible "config" "read `config'";
                options = if optionsView == null then inadmissible "options" "read `options'" else optionsView;
                inherit prefix;
                name = specialArgs.name or (inadmissible "config" "read the module argument `name'");
              }
            else
              {
                config = inadmissible "config" "read `config'";
                options = if optionsView == null then inadmissible "options" "read `options'" else optionsView;
                inherit prefix;
              }
          );

        # `callM`'s shape, over the declaration stratum's arguments. A module arg that is not in
        # `declArgs` comes from `_module.args`, which is a `config` value and therefore stratum 2's:
        # it refuses with the same reason rather than resolving to a different one.
        #
        # `declArgs` is the RIGHT operand for `callM`'s reason: a formal it holds (specialArgs, the
        # refusing `config`/`options`, `prefix`) binds `declArgs`' OWN attribute, so every declaring
        # module sees one value slot, and a `withArgs` relation comparing what two of them pass
        # decides on that slot (`slotsDiffer`). The swap changes cell identity only, never a value.
        # Per key k: a formal in `declArgs` has `extra.k` = `declArgs.k`; a formal not in `declArgs`
        # has the inadmissible refusal in `extra` and nothing in `declArgs`; a key in `declArgs`
        # that is not a formal is absent from `extra`. Both operand orders hold one value per key.
        callD =
          m:
          if builtins.isPath m then
            callD (import m)
          else if isFunction m || m ? __functor && isFunction m.__functor && isFunction (m.__functor m) then
            let
              formals =
                if m ? __functor then m.__functionArgs or (functionArgs (m.__functor m)) else functionArgs m;
              extra = mapAttrs (
                name: _: declArgs.${name} or (inadmissible "config" "read the module argument `${name}'")
              ) formals;
            in
            # `callM`'s elision: every formal in `declArgs` means `extra // declArgs` IS `declArgs`.
            if all (name: declArgs ? ${name}) (attrNames formals) then m declArgs else m (extra // declArgs)
          else if isAttrs m then
            if m ? __functor then callD (m.__functor m) else m
          else if isPathString m then
            callD (import m)
          else
            notAModule m;

        flat = moduleClosure callD modules;
        declEntries = prelude.imap0 (i: e: {
          idx = i;
          file = e._file;
          options = optionsOf (moduleSyntaxChecked e).content;
        }) flat;
        sitesAt = declaringSitesAt (length prefix) declEntries;
      in
      {
        inherit declEntries sitesAt;
        # ONE door for the whole engine: every downstream reader (`mergeTree`'s `declaredPairs`,
        # `declLeafEntries`, `moduleDefFootprint`, `declaringSitesAt`) consumes this tree or a value
        # traced back to it, so guarding the producer here covers all five tags at any nesting depth
        # on both the `.options` and `.config` planes.
        options = mergeOptionDeclTrees (onRedeclare sitesAt) prefix (
          map (e: validateDeclSubtree prefix e.options) declEntries
        );
      };

  # THE STRATUM-1 ENTRY, published beside `evalModuleTree`. A consumer wanting DECLARATIONS without
  # values gets a door that drives no fixpoint at all — the two `.options`-only readers in this
  # ecosystem (gen-schema's `entry-type.nix` introspection and its `id-hash.nix` identity key set)
  # are asking exactly this question, and they already keep the discipline by hand, each with its
  # own comment saying it uses the locally-built merged module to avoid circularity.
  #
  # It is the SAME fold the full result's `options` field is, published twice rather than computed
  # twice: a second definition of "which options are declared" is a second answer, free to disagree.
  #
  # Its options lead and `modules` comes last, as at `evalModuleTree` (den-hoag-7gp66 P2): the same
  # two of that door's options it reads, closed, refused by name at `declaredOptions opts`.
  declaredOptions =
    prelude.door
      {
        name = "gen-merge.declaredOptions";
        optional = [
          "specialArgs"
          "prefix"
        ];
      }
      (
        o: modules:
        let
          s = declarationStratum (o // { inherit modules; });
        in
        moduleOwn.stamp (o.prefix or [ ]) (stampOptions s.sitesAt (o.prefix or [ ]) s.options)
      );

  # ── THE ONE DRIVER — this library declares no fixpoint of its own ─────────────────────────────
  # ADR-0006 / ADR-0008 §1. What was `prelude.fix (result: …)` is the SAME knot, driven by the
  # injected evaluator: the module tree is ONE node, and the self-referential `result` is an
  # ORDINARY attribute on it whose body reads itself back through `self.get`. `children` and
  # `imports` are the evaluator's required attributes and this node has neither — it is a leaf, and
  # the spawn channel is deliberately not used here (a submodule stays a nested invocation of this
  # same constructed library, which is many invocations of one instance, not many instances).
  #
  # NO CARRIER IS DECLARED AND NO CIRCULAR ATTRIBUTE IS USED, and that is what makes an ordinary
  # attribute sufficient: the returned attrset's KEY SET does not depend on the self-read, so the
  # read lands on an already-demanded position rather than re-entering the body. Measured: three
  # self-read sites enter the body ONCE, and the value is byte-equal to the same record computed by
  # Nix's own `let` self-reference — the sharing `prelude.fix` owned is now the evaluator's `_eval`
  # memo. Without that property the re-encoding would be exponential at this engine's three sites
  # (`result.options`, `result.moduleConfig`, `result.moduleArgs`, all in `baseArgs`/`extra`).
  #
  # WHAT THIS DOES NOT BUY, stated because the shape invites the over-read: containment comes only
  # from a DECLARED carrier, so an ordinary value-plane self-reference (`config.x = config.x`)
  # still aborts uncatchably, exactly as it did under `fix`. What refuses by name is the
  # DECLARATION plane, at the fold, and that is a different mechanism (`declaredOptions`).
  #
  # The roots are built once for the library rather than per call: the node set is a constant.
  knotId = "module-tree";
  knotAttr = "result";
  knotScope = scope.buildRoots {
    parentGraph = scope.vertex knotId;
    importGraph = scope.empty;
    decls.${knotId} = { };
  };
  #
  # ── THE MINTING KNOT (den-hoag-n6dh7 items 2, 4) ─────────────────────────────────────────────────
  # A ROOT evaluation's knot is a node of the kind `module-tree`, which declares ONE `nta`, `nested`:
  # its children are the nested trees its option values hold, one per nesting POSITION, minted by
  # the key walk below with Unit 1's identifier (`mintNtaId host "nested" group key`). The builder
  # reads the product the walk computes inside `result`; the seeds address the host attribute
  # `definitions`, one list of definitions per group. A child is a node of the same kind, so its
  # own nested trees are its children in turn: `evalModuleTree` is ONE `scope.eval`, and every
  # nested tree is a node of it (ADR-0006, ADR-0008 §1). The registry and the scope are constants.
  #
  # A child's `result` is its tree's evaluation, read off its host's position record, never off a
  # closure: its definitions, `loc`, report mode and member from the host's `positions` at its own
  # coordinates (`getHostAt`, the host's equation for this child: Söderberg & Hedin 2013 §2.3, §4.1).
  # Its record carries the seed, the addresses of those definitions, unread by the evaluation (arm
  # (B), `childTree`). Carrying the `nta` costs a constant per `scope.eval`
  # (the registry crossing the door); a root pays it once for every tree it holds.
  knotKindName = "module-tree";
  knotScopeMinting = scope.buildRoots {
    parentGraph = scope.vertex knotId;
    importGraph = scope.empty;
    decls.${knotId} = { };
    types.${knotId} = knotKindName;
    kinds = scope.mkKinds [
      (scope.mkKind {
        # A CANDIDATE (`childTree`) holds no nested tree of its own: its record answers as a
        # selected child's does, and only its `result` refuses, so an enumeration never meets it. A
        # CONTAINER NODE holds its elements' trees (`containerNode`).
        nta.nested =
          self: id:
          if
            id == knotId
            || interface.isNesting (self.getHostAt "positions").member
            || (self.getHostAt "positions").mode == "container"
          then
            mapAttrs (_: mapAttrs (_: q: q.address)) (self.get id knotAttr)._nested.positions
          else
            { };
        # ITS MODULE GRAPH (den-hoag-470xp): every tree, the root and each nested one, mints the
        # modules it reaches as ONE identity-keyed family, so identity never crosses trees. A module
        # node hosts no children: its position's `member` is not nesting and its `mode` is not
        # `container`, which both builders read.
        nta.modules =
          self: id:
          if id == knotId || interface.isNesting (self.getHostAt "positions").member then
            (knotModules self id).product
          else
            { };
      } knotKindName)
    ];
  };
  knotNoChildren = _: _: { };
  knotNoImports = _: _: [ ];
  # IMPORT EDGES, gen-scope's `imports` reference attribute (Hedin 2000): a module node names the ids
  # its imports identify to, a tree the ids of its own module list, anything else none. A diamond is
  # two edges into one id, and `queryReverse` answers a module's importers.
  knotImports =
    self: id:
    if id == knotId then
      (knotModules self id).roots
    else
      let
        p = self.getHostAt "positions";
      in
      if p.mode == "module" then
        p.imports
      else if interface.isNesting p.member then
        (knotModules self id).roots
      else
        [ ];
  # A tree's module family, off its closure; its seeds address the closure as the last list of the
  # tree's `definitions`, after the nested family's own.
  knotModules =
    self: id:
    let
      r = self.get id knotAttr;
    in
    moduleFamily id (length r._nested.groups) r._flat (moduleTop r._callM r._modList);
  knotDefinitions =
    let
      nestedDefinitions = n: map (g: g.definitions) n.groups;
    in
    self: id:
    let
      r = self.get id knotAttr;
    in
    if r ? _flat then nestedDefinitions r._nested ++ [ r._flat ] else nestedDefinitions r._nested;
  knotPositions =
    self: id:
    let
      r = self.get id knotAttr;
    in
    {
      nested = r._nested.positions;
      modules = if r ? _flat then (knotModules self id).positions else { };
    };
  driveKnot =
    f:
    (scope.eval { } {
      children = knotNoChildren;
      imports = knotNoImports;
      ${knotAttr} = self: id: f self (self.get id knotAttr);
    } knotScope).get
      knotId
      knotAttr;
  # `exposes`: the gen-scope evaluation itself rides the result as `_evaluation`, for this
  # library's own suites (its `allNodeIds` holds the minted children). Never the published door's.
  driveKnotMinting =
    exposes: f:
    let
      evaluation = scope.eval { } {
        children = knotNoChildren;
        imports = knotImports;
        ${knotAttr} = self: id: if id == knotId then f self (self.get id knotAttr) else childOf self id;
        definitions = knotDefinitions;
        positions = knotPositions;
      } knotScopeMinting;
      r = evaluation.get knotId knotAttr;
      # This evaluation's declaration-address tree (`seedDeclAts`), rooted at its knot, and the child
      # builder that reads it, bound once so that no child pays a partial application. These two are
      # the tree's whole charge to an evaluation that never reads `declAt`: 2 thunks per minting root
      # evaluation, none per nested tree.
      ra = seedDeclAts.addrsFor ra evaluation knotId null [ ];
      childOf = childTree ra;
    in
    if exposes then r // { _evaluation = evaluation; } else r;

  # ── A CHILD'S EVALUATION (den-hoag-n6dh7 item 4) ─────────────────────────────────────────────────
  # The call a nesting type's called form made, field for field, with each field read from the
  # host's position record at the child's coordinates: its member's module set plus one entry per
  # definition the position holds, the placing fold's `loc` as the prefix, the member's own arguments
  # (with `name` where the member injects one), in the report mode its site decides. An EMPTY
  # position evaluates with the member's `empty` arguments, as its `whenEmpty` did. The warm path
  # stays cold at a child, the documented boundary (`evalModuleTreeWith`'s `warmFrom` note).
  #
  # The definitions come off the host's equation, not through the seed (owner ruling 2026-09-28,
  # arm (B), amending v8 item 4 and OQ3 (a-ii)): the seed stays minted on the child's record as the
  # addresses of those same definitions, the constructed descent that is the termination ground,
  # and the evaluation does not resolve it: resolving each address through Unit 1's `readAddress`
  # would re-read, at a price per tree, values the position record already holds.
  #
  # A CANDIDATE (an over-approximated child the host's fold never selected, item 2) refuses here,
  # on `result` alone, before any of its member's modules is applied: its member is the one the
  # host fold's own `split` chain reaches, `choose` included, and a member that is not a nesting
  # type means the fold did not select a nested tree at this position. The rule, for a reader that
  # enumerates: a per-node reader of `result` over an enumeration reads it only for a selected child.
  #
  # A CONTAINER NODE (S1 arm (v), den-hoag-9d80v) is the one child that is not a tree: its position
  # is marked `mode = "container"` (`containerAt`), its seed addresses the position's definitions,
  # which it reads off the host's position record as a tree does (arm (B)), its own
  # `container` group keys the positions its member's walk reaches over those definitions only
  # (`under = null`, so exactly), and its `result` is `{ value; _nested; }`: the member's threaded
  # fold at the host's `loc`, reading its trees as its own children. A reader of `result` checks the
  # position's `mode` first: `.config` on a container node is a missing attribute, which `tryEval`
  # does not catch.
  containerNode =
    self: id:
    let
      p = self.getHostAt "positions";
      # Its definitions off the host's position record, as a tree's (`childTree`, arm (B)).
      defs = map (d: { inherit (d) file value; }) p.defs;
      records = keyWalk null p.loc p.member [ ] p.loc (
        prelude.imap0 (
          i: d:
          d
          // {
            at = [
              i
              "value"
            ];
          }
        ) defs
      );
      positions.container = listToAttrs (
        map (r: {
          name = builtins.toJSON r.key;
          value = {
            inherit (r)
              key
              loc
              member
              defs
              ;
            address = map (d: {
              attr = "definitions";
              def = 0;
              inherit (d) at;
            }) r.defs;
            mode =
              if r ? container then
                "container"
              else
                positionMode {
                  carried = false;
                  strict = false;
                } r.type r.key;
            emptyRun = if r.defs == [ ] then p.emptyRun + 1 else 0;
          };
        }) records
      );
      # the node's own accessor, published beside its value: a foreign chain's one fold, run at its
      # host, threads each element below this node through it (`interface.threadedForeign`)
      accessor = evAt {
        reader = self;
        result._nested = { inherit positions; };
      } "container";
    in
    {
      value = mergeDefsThreaded accessor p.loc p.member defs;
      inherit accessor;
      _nested = {
        groups = [ { definitions = defs; } ];
        inherit positions;
      };
    };
  # THE DECLARATION-ADDRESS TREE (den-hoag-mg94o; specs/2026-10-06-gen-merge-declat-linear-spec.md).
  # The declaration addresses of the seeds of `id`, the nested node placed by `p`, aligned with
  # `p.defs` (`seedsOf`): its host's group addresses (`nestedDeclAts`) under the host's own anchors,
  # the host's seeds' addresses in turn, then the key walk's steps past the group ordinal and
  # `"value"`. An address is a pure function of the ancestor chain, an inherited attribute of the
  # nested tree, so each node's is derived ONCE per evaluation (`addrsFor`): a lazy mirror of the
  # nested tree, rooted at the minting knot's driver (`driveKnotMinting`) and keyed by the
  # coordinates each child's identifier is minted from. A node's entry is built only when one of its
  # descendants asks (`addrsOf`), so an evaluation that never reads `declAt` builds none of it, and
  # the tree holds the addresses alone: it mints nothing. It lives outside the knot's attribute table
  # because gen-scope charges every attribute to every nested tree, which the bench's
  # `deepSubmodule` row prices.
  seedDeclAts =
    let
      # ── THE DECLARATION ADDRESS OF A SEED (den-hoag-8hlo3 U1; design 2026-09-30 §1, ADR-0034's rider) ──
      # Each position's seed definitions, as `positions` holds them, each spelled as the place it was
      # DECLARED: the declaring module's anchor, the option path, and the structural path the discharge
      # took (`declAtsOfGroup`, then the key walk's own steps past the group ordinal and `"value"`). A
      # nesting type that declares `nests.declAt = true` receives its seed's as `declAt` (`childTree`);
      # nothing else reads them, so every other evaluation pays for none of it.
      #
      # An anchor is gen-merge's local spelling of a module's identity (`moduleKeyOf`), chained so that it
      # is injective over the whole evaluation, every child tree included, never only within one tree:
      # - a ROOT's top-level or keyed module is its own spelling (`[ "a:<i>" ]`, `[ "k<key>" ]`);
      # - a CHILD's seed module is its host's address for that seed, so the address chains from the
      #   root through every nesting; its OWN modules (the nesting type's, which every child of that type
      #   shares) and its keyed imports sit under the child's own address, `{ module = <i | key>; }`
      #   appended, where that address is the seed's for a single-seed position and `{ loc = <loc>; }`
      #   otherwise;
      # - an anonymous import is its importer's anchor, `imports`, its index;
      # - an option default is the tree's address (none for a root) with `{ default = true; }`.
      # The attrset markers are never an option name, an attribute step or an index, so no two
      # declarations share an address. The spelling carries module identity without the mint (7gp66 OQ4
      # (b′)): keyed and path modules keep their address under reorder, an anonymous module moves with
      # its own position in its importer (design §1 item 2).
      declAnchorOf =
        r: p: seeds:
        let
          flat = r._flat;
          nFlat = length flat;
          nTop = length r._modList;
          nOwn = nTop - length seeds;
          tree =
            if p == null then
              null
            else if length seeds == 1 then
              head seeds
            else
              [ { inherit (p) loc; } ];
          under = x: if tree == null then [ x ] else tree ++ [ { module = x; } ];
          top =
            i: k:
            if tree == null then
              [ k ]
            else if i >= nOwn then
              builtins.elemAt seeds (i - nOwn)
            else
              tree ++ [ { module = i; } ];
          graph = alignedGraph "the declaration anchors" flat (
            closeModules (moduleTop r._callM r._modList).roots
          );
          anch =
            g:
            if g.importer.key == "" then
              top g.i g.key
            else if builtins.substring 0 1 g.key == "k" then
              under g.key
            else
              anch g.importer
              ++ [
                "imports"
                g.i
              ];
          # The closure keeps every unkeyed top-level module, in order, ahead of every import
          # (`moduleLevels`), so where no top-level module is keyed a top-level module's anchor is read
          # off its index, with no closure walk.
          topPlain = all (e: nodeKeyOf e == null) (
            prelude.genList (builtins.elemAt flat) (if nTop < nFlat then nTop else nFlat)
          );
        in
        mi:
        if mi == null then
          (if tree == null then [ ] else tree) ++ [ { default = true; } ]
        else
          let
            fi = nFlat - 1 - mi;
          in
          if fi < nTop && topPlain then top fi "a:${toString fi}" else anch (builtins.elemAt graph fi);
      # Each group's seed declaration addresses (den-hoag-8hlo3 U1), aligned with `definitions`, given
      # the tree's module anchors (`declAnchorOf`).
      nestedDeclAts =
        inputs: anchorOf:
        map (declAtsOfGroup inputs.normalize anchorOf) inputs.leaves
        ++ optional inputs.freeform.declared (map (d: anchorOf d.modIndex) inputs.freeform.defs);
      # ONE OPTION GROUP'S DECLARATION ADDRESSES (den-hoag-8hlo3 U1), aligned with its `definitions`: the
      # same discharge, priority and order passes in their path-carrying twin (`addressedDefs`), seeded
      # with each definition's declaring module's anchor (`anchorOf modIndex`; `anchorOf null` for the
      # option's default) and the option path, so a surviving definition keeps the address it was
      # written at, never its merge position.
      declAtsOfGroup =
        normalize: anchorOf: l:
        if l.defs == [ ] && !(l.opt ? default) then
          [ ]
        else
          map (d: d.at) (
            addressedDefs (
              map (d: d // { at = anchorOf (d.modIndex or null) ++ l.path; }) (
                normalize (withDeclaredDefault l.opt l.defs)
              )
            )
          );
      # The entry of `id`, the node placed by `p` (`null` for the root) whose seeds' addresses are
      # `seeds`: its group addresses (a container node's one group is its seeds), and one entry per
      # child, at the coordinates the child's identifier is minted from (`mintNtaId`). Both lazy.
      addrsFor = ra: self: id: p: seeds: {
        groups =
          if p != null && p.mode == "container" then
            [ seeds ]
          else
            let
              r = self.get id knotAttr;
            in
            nestedDeclAts r._nested.inputs (declAnchorOf r p seeds);
        children = mapAttrs (
          group:
          mapAttrs (
            key: q:
            addrsFor ra self (scope.mintNtaId {
              host = id;
              name = "nested";
              inherit group key;
            }) q (seedsFrom ra self id q)
          )
        ) (self.get id "positions").nested;
      };
      # The entry of `id`, reached from the root `ra` down the coordinates its identifier decodes to.
      # Only the `nested` family hosts a nested tree (a module node holds no child), so any other
      # family refuses by name rather than reading a sibling family's entry.
      addrsOf =
        ra: self: id:
        if id == knotId then
          ra
        else
          let
            c = scope.decodeNta id;
          in
          if c.name != "nested" then
            throw "gen-merge: `seedDeclAts': node `${c.group}.${c.key}' of family `${c.name}' holds no nested tree, so it has no declaration addresses (only the `nested' family does)"
          else
            (addrsOf ra self c.host).children.${c.group}.${c.key};
      seedsFrom =
        ra: self: host: p:
        let
          groups = (addrsOf ra self host).groups;
        in
        map (a: builtins.elemAt (builtins.elemAt groups a.def) (head a.at) ++ drop 2 a.at) p.address;
    in
    {
      inherit addrsFor;
      seedsOf =
        ra: self: id: p:
        seedsFrom ra self (scope.decodeNta id).host p;
    };
  childTree =
    ra: self: id:
    let
      p = self.getHostAt "positions";
      member = p.member;
      n = member.nests;
      m = if p.mode == "called" then n.calledMode else p.mode;
    in
    # A MODULE NODE (den-hoag-470xp) answers its closure entry off the host's position record, as a
    # container node reads its definitions (arm (B)), and never a tree evaluation.
    if p.mode == "module" then
      {
        inherit (p) _file content srcClass;
      }
    else if !(interface.isNesting member) && p.mode == "container" then
      containerNode self id
    else if !(interface.isNesting member) then
      throw "gen-merge: `evalModuleTree': option `${showOption p.loc}': the fold of the tree holding it did not select a nested tree at this position${
        if isAttrs member then " (it folds as `${member.name or "<unnamed>"}')" else ""
      }, so this nested tree is a candidate and is never evaluated"
    # The child of a PARTIAL nesting type (`nests.partial`, lib/types.nix `partialSubmodule`) is driven on a
    # partial knot, built here so that only a partial child pays for it, and selected as the call's head so
    # that every other child pays no argument for the choice. With an empty seed too: its declared defaults
    # are a definition at `mkOptionDefault` there as they are under one empty definition, or the empty
    # value would beat a later `mkDefault` at the default priority (den-hoag-5ov3p gate C1).
    else if p.defs == [ ] then
      (
        if n.partial or false then
          evalModuleTreeWith (knotChild // { partial = true; })
        else
          evalModuleTreeWith knotChild
      )
        m.carried
        m.inherited
        {
          modules = n.modules ++ [ namePlaceholder ];
          inherit (n) coreShortCircuit;
          inherit (n.empty) prefix specialArgs check;
        }
        self
        (self.get id knotAttr)
    # A nesting type that declares `nests.declAt` receives each seed's declaration address
    # (`seedDeclAts`), in its own call; every other child is built exactly as before, with no `declAt`
    # attribute and no `if` operand in its `modules`. The chosen call is applied once, outside the
    # `if`: applied in each branch, every tree pays 48 bytes more. A partial type declares no `declAt`
    # (lib/types.nix `mkSubmodule`), so the first branch never holds a partial child.
    else
      (
        if n.declAt or false then
          let
            declAts = seedDeclAts.seedsOf ra self id p;
          in
          evalModuleTreeWith knotChildPositioned m.carried m.inherited {
            modules =
              n.modules
              ++ prelude.imap0 (
                k: d:
                n.entry {
                  inherit (d) file value;
                  declAt = builtins.elemAt declAts k;
                }
              ) p.defs;
            prefix = p.loc;
            inherit (n) specialArgs check coreShortCircuit;
          }
        else
          (
            if n.partial or false then
              evalModuleTreeWith (knotChildPositioned // { partial = true; })
            else
              evalModuleTreeWith knotChildPositioned
          )
            m.carried
            m.inherited
            {
              modules = n.modules ++ map (d: n.entry { inherit (d) file value; }) p.defs;
              prefix = p.loc;
              inherit (n) specialArgs check coreShortCircuit;
            }
      )
        self
        (self.get id knotAttr);

  # The knots an evaluation is driven on, chosen where `evalModuleTreeWith` is bound, so a call
  # pays no argument for the choice: a root's (the minting knot), a root's whose evaluation is
  # exposed to this library's suites, and the declaration-only plain knot a type's `declares` reads
  # (it folds no value, so it holds no child). A child's knot is its own node (`childTree`). `partial`: the
  # evaluation's declared options fold partially (the realizer's `mergeOption`); only `childTree` sets it.
  knotChild = {
    partial = false;
    mints = true;
    exposes = false;
    inner = true;
    positioned = false;
    drive = null;
  };
  # A nested tree over definitions at a position: the sets its modules are applied to hold the
  # position's `name` (`positionArgsAt` of its `prefix`), resolved against the modules' own
  # definitions by `positionNameOf` only when one states it. A knot, not an argument, because the
  # argument record is built per child and every field on it is paid per child.
  knotChildPositioned = knotChild // {
    positioned = true;
  };
  knotNested = {
    partial = false;
    mints = false;
    exposes = false;
    inner = false;
    positioned = false;
    drive = driveKnot;
  };
  knotRoot = {
    partial = false;
    mints = true;
    exposes = false;
    inner = false;
    positioned = false;
    drive = driveKnotMinting false;
  };
  knotRootPositioned = knotRoot // {
    positioned = true;
  };
  knotExposed = {
    partial = false;
    mints = true;
    exposes = true;
    inner = false;
    positioned = false;
    drive = driveKnotMinting true;
  };

  # ── evalModuleTree — one call = one `evalModules`, one knot on the one evaluator ──────
  # `carried`: whether this evaluation's `undeclared` report is read. `inherited`: whether a tree
  # that carries that report is strict, which makes this evaluation refuse its own level's findings
  # as the nested tree that owns them (`_orphanCheck`). The public binding is
  # `evalModuleTreeWith true false`; only a nesting seam passes anything else: its strict fold
  # `false false`, its reporting fold `true <the carrying evaluation's effective strictness>`.
  # `knot`: which knot the evaluation is driven on (above): a root evaluation mints its nested
  # positions, and a nested evaluation made by a type's called fold does not.
  evalModuleTreeWith =
    knot: carried: inherited:
    {
      modules,
      specialArgs ? { },
      # `null`: not passed, and `_module.check` takes its option default, `true`. Passed, it enters
      # the merge as one `mkDefault` definition, as nixpkgs' deprecated `check` argument does, so a
      # module's own `_module.check` outranks it.
      check ? null,
      prefix ? [ ],
      # Opt-in fixed-input kernel (spec §2.5). Default off ⇒ ZERO behaviour change — the core marker
      # is treated as an ordinary attrset. Firing scope: the REALIZER path (declared leaf options at
      # any depth, via `mergeOptionWith`). The flag PROPAGATES through the moduleTree-as-type nested
      # eval (:519 below), so a nested tree fires consistently; only structural-type element merges
      # (attrsOf/listOf per-element folds) do NOT short-circuit — they stay byte-identical, never
      # seeing the flag (a user-supplied type closed over the plain `mergeDefs`). This matches the
      # tier-2 firing contract (core projection locs are declared-option leaves supplied by the core
      # module).
      coreShortCircuit ? false,
      # ── opt-in warm re-eval (design spec §§1-4) ────────────────────────────────────────────────
      # `warmFrom` = the PREVIOUS `evalModuleTree` result (its `config`/`provenance`/`freeformConfig`/
      # `freeformProv` ARE the memo — no new table); `editedModules` = the appended module LIST (the
      # engine flattens it internally, deriving the EDITED tail-count itself). Default null/[ ] ⇒ ZERO
      # behaviour change (the `coreShortCircuit` precedent): the decision is never forced, `mergeTree`
      # takes the cold branch, freeform re-merges cold. Warm SPLICES declared-leaf values/provenance
      # for locs OUTSIDE the dirty footprint (§2), re-merging the rest in the normal fixpoint; a leaf's
      # spliced value IS prev's memoized thunk (byte-identical by the predicate). Fires only here (the
      # top eval); the nested moduleTree-as-type merge stays COLD (a boundary, like provenance's).
      warmFrom ? null,
      editedModules ? [ ],
    }:
    let
      modList = if isList modules then modules else [ modules ];

      # Realize config against the option-decl TREE, one path at a time (nixpkgs mergeModules'):
      # a declared LEAF merges via `mergeOption` (the existing per-option behaviour); a declared
      # GROUP recurses; a config key with NO matching declaration is an UNMATCHED def, bubbled up
      # with its FULL (relative) path so the ROOT freeform can absorb it or the orphan check can
      # throw. nixpkgs is strict PER LEVEL, not only at the root — an undeclared key under an
      # intermediate group throws too (a naive recursion that dropped it would diverge). `loc` is
      # RELATIVE to `prefix`; a leaf's absolute option location is `prefix ++ loc ++ [ k ]`, while
      # unmatched paths stay relative (the root reshapes them against `prefix` via `setAttrByPath`).
      #   rawDefs :: [ { file; value } ]   (value: property-wrapped or a plain sub-attrset)
      # Signature is `warm: loc: opts: rawDefs` — `warm` is the FIRST positional (threaded unchanged
      # through the descent), described last here only because it is the warm-path add-on.
      # `warm` = the warm-splice context `{ active; isClean; prevConfig; prevProv }` (or
      # `{ active = false; }`), threaded through the descent. At a declared LEAF whose ABSOLUTE loc
      # gen-memo's `isClean` ADMITS (ADR-0008 item 2 — the incremental plane's DECISION over the
      # contribution-relation FACT `warmDecide` computes), warm SPLICES `getAttrByPath` of prev's
      # `config`/`provenance` — lazy attrpath selection, never forcing the reused thunk (spec §2).
      # SPLICE AT LEAVES ONLY: `prev.config`
      # is `recursiveUpdate freeform declared`, so a whole untyped-GROUP splice would capture stale
      # freeform descendants when the freeform plane re-merges; at an `isOptLeaf` loc the prev value is
      # declared-only (freeform never wins a declared leaf), so leaf-granularity splicing is sound —
      # untyped declared groups recurse and splice THEIR leaves.
      mergeTree =
        warm: loc: opts: rawDefs:
        let
          # Push config-node properties down one level (nixpkgs pushes at EACH descent, so a nested
          # `a.b = mkIf c { … }' distributes into `b's keys), yielding plain attrsets per module.
          # `modIndex` (the originating module instance, threaded from `topDefs`) rides every def so
          # unmatched keys can be coalesced per module at the root — see `coalesceUnmatched`.
          pushed = map (d: {
            inherit (d) file modIndex;
            attrs = pushDownProperties d.value;
          }) rawDefs;
          # The DECLARED keys' definitions, grouped once per level (nixpkgs `mergeModules'`'s
          # `pushedDownDefinitionsByName`), so each key is answered by a lookup rather than a scan of
          # `pushed`. Only the declared keys are grouped (`intersectAttrs opts`): the undeclared ones
          # are grouped by `ownUnmatched` into their own records, so no definition is recorded twice.
          # Each list keeps `pushed`'s order, the module-union order the merge reads (den-hoag-z75vj).
          defsByKey = builtins.zipAttrsWith (_: vs: vs) (
            map (
              p:
              mapAttrs (_: value: {
                inherit (p) file modIndex;
                inherit value;
              }) (builtins.intersectAttrs opts p.attrs)
            ) pushed
          );
          subDefs = k: defsByKey.${k} or [ ];

          # Each declared name yields BOTH its merged value and its provenance sub-tree from one
          # descent, as a pair `{ name; m; group? }` carrying the merge record whole: a declared LEAF →
          # `m` = the rich option merge `{ value; prov; undeclared }` (prov = the record); a declared
          # GROUP → `m` = the recursive subtree `{ value; prov; unmatched; reported }` (prov = the
          # sub-tree), marked `group = true`. The pair projects nothing; every reader below projects
          # through `x.m`. Both trees are assembled at this level by the SAME `listToAttrs` pattern, so
          # provenance mirrors config's loc structure attribute-for-attribute.
          declaredPairs = map (
            k:
            let
              lk = loc ++ [ k ];
              abs = prefix ++ lk;
            in
            if isOptLeaf opts.${k} then
              # A root `_module` leaf never splices: prev's returned `config` is `_module`-free.
              if warm.active && head lk != "_module" && warm.isClean (builtins.toJSON lk) then
                # REUSABLE — gen-memo admits this location as clean: splice prev's leaf value + provenance record
                # (the same memoized thunks). `getAttrByPath` is lazy: an unforced prev leaf stays
                # unforced, a forced one is free. Byte-identical to the cold merge by the §2 predicate
                # (both the decl set and the def set at this loc come only from CLEAN modules).
                # The decision and both splices take the RELATIVE `lk`: the footprint `isClean` decides
                # over (`declLeafPaths`/`moduleDefFootprint`) and prev's `config`/`provenance` are all
                # rooted at `[ ]` whatever the `prefix`. `abs` names nothing in them.
                {
                  name = k;
                  m = {
                    value = getAttrByPath lk warm.prevConfig;
                    prov = getAttrByPath lk warm.prevProv;
                    typeDefs = getAttrByPath lk warm.prevDefs;
                    # The reused leaf's findings are the PRIOR eval's report records at and below `abs`,
                    # passed through unchanged: both are in the absolute frame. The same §2 predicate
                    # (decls and defs here come only from clean modules) makes that report the cold
                    # merge's, so reuse survives and nothing is re-merged. The prior report holds entries
                    # at or below `abs` only from this leaf's own channel (an undeclared key elsewhere is
                    # captured above a declared leaf, never below one). Read only through the walk's
                    # declaration guard below, like the cold record's `undeclared`.
                    undeclared =
                      let
                        n = length abs;
                      in
                      filter (u: length u.path >= n && take n u.path == abs) warm.prevUndeclared;
                  };
                }
              else
                {
                  name = k;
                  m = warm.mergeOption abs opts.${k} (subDefs k);
                }
            else
              {
                name = k;
                group = true;
                m = mergeTree warm lk opts.${k} (subDefs k);
              }
          ) (attrNames opts);

          # Undeclared config keys at THIS level → unmatched defs carrying their full path + value
          # (+ the originating `modIndex`, for per-module coalescing at the root). Grouped once per
          # level, like `defsByKey`, over each entry's undeclared keys (its keys less the declared
          # ones it defines). `attrValues` of the grouping is key order and each group keeps `pushed`'s
          # order, so the list is key-major; the report and the orphan refusal read that order.
          # A level whose every definition key is declared groups nothing: the test quantifies over
          # every key of every definition, so it takes `[ ]` exactly where the grouping would build
          # it, and it forces each `p.attrs` in `pushed` order as the grouping does. On a level WITH
          # an undeclared key (a freeform level) the test is paid in front of the grouping, about 8 B
          # per key (den-hoag-r8y89 c3; den-hoag-c7jkw.3).
          ownUnmatched =
            if all ({ attrs, ... }: all (k: opts ? ${k}) (attrNames attrs)) pushed then
              [ ]
            else
              concatLists (
                builtins.attrValues (
                  builtins.zipAttrsWith (_: us: us) (
                    map (
                      p:
                      mapAttrs (k: value: {
                        inherit (p) file modIndex;
                        path = loc ++ [ k ];
                        inherit value;
                      }) (builtins.removeAttrs p.attrs (attrNames (builtins.intersectAttrs opts p.attrs)))
                    ) pushed
                  )
                )
              );
        in
        {
          value = listToAttrs (
            map (x: {
              inherit (x) name;
              value = x.m.value;
            }) declaredPairs
          );
          prov = listToAttrs (
            map (x: {
              inherit (x) name;
              value = x.m.prov;
            }) declaredPairs
          );
          typeDefs = listToAttrs (
            map (x: {
              inherit (x) name;
              value = x.m.typeDefs;
            }) declaredPairs
          );
          # TWO CHANNELS, ONE PER KIND OF RECORD, each in exactly one frame.
          # `unmatched` holds DEFINITIONS this level must dispose of, `{ file; modIndex; path; value; }`
          # with paths RELATIVE to `prefix`: this level's own and a group's. A leaf contributes none.
          # `reported` holds FINDINGS a nested tree already settled, `{ path; file; }` with paths
          # ABSOLUTE (the nested eval ran at `prefix = abs`). A finding carries no `modIndex` (it indexes
          # the PARENT's `topDefs`, and the finding came from the nested tree's modules) and no `value`
          # (so reading the report forces no nested definition value), so no definition-kind reader
          # (`coalesceUnmatched`, `freeformProvCold`) may ever meet one, and none can.
          #
          # A leaf's findings are decided from the DECLARATION, `opts.<k> ? type.mergeDefs.reported`,
          # and only where this evaluation's report is `carried`. Without one, a nested tree's leaf
          # folds strictly (`mergeDefsRichWith`'s `mode.carried`), refusing its own level's findings
          # when that level is read, so a cold leaf's `undeclared` is `[ ]` already, and a
          # warm-reused leaf's is only because an unreported eval is a nested one, which is always
          # cold. The guard states that here, where the walk decides, rather than borrowing it. Decided
          # inside this walk: every ordinary leaf type contributes `[ ]` without its merge record being
          # touched, so no definition is forced to learn it. One reader walks `reported`'s spine, the
          # `undeclared` report (no refusal reads it; see `_orphanCheck`), and a walk that read
          # `x.m.undeclared` for every leaf would force EVERY leaf's merge through it — against this engine's own
          # contract ("undefined+no-default throws only on access"). The decision lives here, and not
          # as a field on the pair, because the walk is already the point that forces it: a per-pair
          # field is a thunk and a record slot on every leaf, and deciding at pair construction would
          # force every declared type whenever `listToAttrs` forces the pairs. `group = true` records
          # the pair's kind where the group/leaf branch was taken, so the walk reads a marker rather
          # than re-deriving leafness.
          unmatched = ownUnmatched ++ concatMap (x: if x ? group then x.m.unmatched else [ ]) declaredPairs;
          # ROUTED-LEAVES EXPOSURE (den-hoag-n6dh7 L5c, "one routing"): `declaredPairs`, `subDefs`,
          # `opts` and `loc` are the descent this walk already ran to route each def to its declared
          # name. Exposing them by `inherit` binds an attribute directly to the existing thunk (no
          # new allocation); `realizedLeaves` reads them to derive `_nested`'s leaf list instead of
          # re-running `pushDownProperties` and the key walk a second time.
          inherit
            declaredPairs
            subDefs
            opts
            loc
            ;
          reported = concatMap (
            x:
            if x ? group then
              x.m.reported
            else if carried && opts.${x.name} ? type.mergeDefs.reported then
              x.m.undeclared
            else
              [ ]
          ) declaredPairs;
        };

      # ── THE DECLARATION GUARD ─────────────────────────────────────────────────────────────────
      # ADR-0033's stratification, enforced rather than arranged. `declarationSpine` applies this
      # module set with `config`, `options` and the module args bound to named refusals, and this
      # forces its declaration SPINE — every merged option path and every `imports` expansion, and
      # no descriptor field. A module whose option KEY SET or whose `imports` TARGETS are a function
      # of `config` therefore refuses by name, `tryEval`-catchably, BEFORE the real fold below can
      # reach it; today the same module reads `infinite recursion encountered` with no name and no
      # containment. A descriptor's own `default` is a stratum-2 value and is never forced here.
      #
      # It costs one declaration-side application of the module set. The value side — the merge, the
      # priority pass, the type folds — is untouched, and the guard forces no definition.
      #
      # The guard returns `declarationStratumWith`'s record for every module set. On a CLOSED set
      # (every module an attrset with no `__functor`, `imports` or `require`) `callD` and `callM` both
      # return each module unchanged, so the two strata collect one value: that record carries
      # `flat`, and the body reads `flat`, `declEntries`, `sitesAt` and the validated declarations
      # from it instead of computing them a second time. Any other set's record carries no `flat`,
      # and the body, which decides by `declarationGuard ? flat`, computes its own. On an open set the
      # guard therefore returns the stratum-1 record too, where it used to return `null`, and the
      # body's `? flat` reads keep that record live for the evaluation's lifetime (measured: max RSS
      # +1.5–5 MB, `gc.heapSize` unmoved; den-hoag-c7jkw.3 landing gate). The syntax
      # checks, the spine merge and the spine walk stay the guard's own and stay eager. Closedness is
      # decided once, in `declarationStratumWith`, spelled inline in primops: a named predicate costs
      # a load thunk.
      #
      # The spine is forced by a copy of `declLeafEntries`'s descent — the same `isOptLeaf` stop, the
      # same group recursion, so the same set of forced nodes — answered as a boolean rather than as
      # `deepSeq (declLeafPaths …)`, which builds and then forces a loc list per declared leaf that
      # nothing reads. Forcing is the whole of the guard; no path is its product. The copy inlines
      # `isOptLeaf` and reads the values by `attrValues`, which lists them in `attrNames` order, so
      # each node is forced at the same step and no binding is made per key.
      #
      # The spine needs leafness per declaring module and never the merged record, so the guard
      # reads `declarationSpine`, whose redeclaration step keeps the later operand, and forces no
      # type. A type-merge refusal surfaces from the value fold, on the read that reaches the option.
      #
      # When the spine does not resolve, the guard takes `stagedDeclarations`: the unresolved nodes are
      # re-tried against the declarations of strictly earlier passes, and only what no pass resolves
      # refuses. The guard still returns `s` either way, so the staged passes decide admission only.
      # A closed set (`s ? flat`) has no module that reads `options`, so every pass would equal the
      # first and the staged path could only re-raise its error: the spine is forced outright there,
      # with no `tryEval` record.
      declarationGuard =
        let
          spine =
            t: all (v: !(isAttrs v) || (v._type or null) == "option" || spine v) (builtins.attrValues t);
        in
        let
          s = (if knot.positioned then declarationSpinePositioned else declarationSpine) {
            inherit specialArgs prefix;
            modules = modList;
          };
        in
        if s ? flat then
          builtins.seq (spine s.options) s
        else if (builtins.tryEval (spine s.options)).success then
          s
        else
          builtins.seq (stagedDeclarations knot.positioned {
            inherit specialArgs prefix;
            modules = modList;
          } s) s;

      # The evaluation's body: the knot's own attribute, over the node's reader `self` and the
      # fixpoint `result`. A root's knot drives it; a child's knot is its own node (`childTree`).
      body = (
        self: result:
        let
          # The same refusal as at `declArgs`, spelled inline for the same reason.
          baseArgs =
            (
              if !(specialArgs ? config || specialArgs ? options || specialArgs ? prefix) then
                specialArgs
              else
                let
                  stated = filter (k: specialArgs ? ${k}) [
                    "config"
                    "options"
                    "prefix"
                  ];
                in
                throw (
                  "gen-merge: `specialArgs' cannot supply the base module argument"
                  + (if length stated == 1 then " " else "s ")
                  + concatStringsSep ", " (map (k: "`${k}'") stated)
                  + "; the engine injects its own value there, so the caller's would be discarded rather than used"
                )
            )
            // (
              # A positioned evaluation carries its `name` here, resolved as a definition
              # (`positionNameOf`) and outranked by a caller's: a key in the set every module is
              # applied to, so a module reading `name` takes `callM`'s elided application. Where a
              # module declares `options._module`, `moduleArgs` holds it, after any `apply`.
              if knot.positioned then
                {
                  options = moduleOwn.serve prefix result.optionDefs.moduleOwn (
                    serveOptions sitesAt [ ] prefix result.provenance result.optionDefs.defs result.optionDefs.values
                      result.options
                  );
                  # Modules see the `_module`-bearing view so `config._module.args` resolves (nixpkgs
                  # parity); the returned `result.config` stays `_module`-free.
                  config = result.moduleConfig;
                  inherit prefix;
                  name =
                    specialArgs.name
                      or (if allOptions ? _module then moduleArgs.name else positionNameOf prefix moduleArgs pushed);
                }
              else
                {
                  options = moduleOwn.serve prefix result.optionDefs.moduleOwn (
                    serveOptions sitesAt [ ] prefix result.provenance result.optionDefs.defs result.optionDefs.values
                      result.options
                  );
                  config = result.moduleConfig;
                  inherit prefix;
                }
            );

          # Apply a module by its declared formals, sourcing each from baseArgs then the dynamic
          # module-args set. Using `functionArgs` (static) is what breaks the spine cycle.
          # A path leaf (`./foo.nix`) — or a path inside another module's `imports` — is `import`ed
          # then re-entered (nixpkgs imports path modules), so a consumer can load a module tree from
          # `(import-tree ./dir).files`, a BARE PATH LIST. `callM` is already self-recursive, so an
          # imported path yielding a function / `__functor` / attrset is handled uniformly below.
          callM =
            m:
            if builtins.isPath m then
              callM (import m)
            else if isFunction m || m ? __functor && isFunction m.__functor && isFunction (m.__functor m) then
              let
                formals =
                  if m ? __functor then m.__functionArgs or (functionArgs (m.__functor m)) else functionArgs m;
                extra = mapAttrs (
                  name: _:
                  baseArgs.${name} or result.moduleArgs.${name}
                    or (throw "gen-merge: module argument `${name}' is not defined")
                ) formals;
              in
              # Every formal in `baseArgs` (`{ options, ... }`): `extra // baseArgs` IS `baseArgs`, key
              # for key and slot for slot, so it is passed as it stands, without building `extra` or
              # the `//` — one attrset pair per application that the hub perf-bench's schemaHosts and
              # entityMatch alloc rows priced.
              if all (name: baseArgs ? ${name}) (attrNames formals) then
                m baseArgs
              else
                # `baseArgs` is the RIGHT operand, so a formal it holds (specialArgs, `config`,
                # `options`, `prefix`) binds to `baseArgs`' OWN attribute: every module sees one value
                # slot and `==` answers alike on the three evaluators (see `slotsDiffer`). This
                # departs from nixpkgs' `applyModuleArgs`, which copies every formal: `[ fa ] == box`
                # reads true on every evaluator here. The answer is `baseArgs // extra //
                # intersectAttrs formals baseArgs` with the middle set elided, at no thunk and no
                # allocation beyond the one `//` every application already paid; the three-operand
                # spelling allocates the intersection per application and reds the hub perf-bench's
                # entityMatch alloc rows, and a `removeAttrs formals names` operand reds its kindMatch
                # thunk rows. A `_module.args` formal stays a per-application copy (a priced residue,
                # README "Known byte-mode boundaries").
                m (extra // baseArgs)
            else if isAttrs m then
              if m ? __functor then callM (m.__functor m) else m
            else if isPathString m then
              callM (import m)
            else
              notAModule m;

          # THE GUARD IS INTERPOSED HERE, and the position is the whole of its reach: every field
          # this engine publishes is derived from `flat`, so no path into the result can get past
          # the declaration guard. Hanging it on `allOptions` alone is NOT enough and that is
          # measured rather than reasoned — the VALUE path reaches `flat`'s own `imports` expansion
          # before it reaches `allOptions`, so an `imports` reading `config` recursed uncatchably
          # while the guard sat unforced one binding away.
          #
          # `flat` IS the tree's module collection (`moduleClosure`), in closure order: the fold below
          # reads it, and the minted `modules` family pairs it with the identity-keyed closure after
          # `alignedGraph` has checked every node.
          flat =
            if declarationGuard ? flat then
              declarationGuard.flat
            else
              builtins.seq declarationGuard (moduleClosure callM modList);

          # Option DECLARATIONS merge across modules into a nested TREE (nixpkgs mergeOptionDecls):
          # a second module's `options.a.b.d` recurses beside the first's `options.a.b.c` instead of
          # `//`-clobbering the `a.b` group. A RE-DECLARED leaf goes to `redeclareDecl` — the type
          # algebra answers, the non-type fields keep their ordered bias, and what the bias shadowed
          # stays reachable. gen-schema's ref-binding `apply`-override modules carry no `type` of
          # their own, so the algebra never reaches them. One-level before; a tree now, so
          # `options.a.b.c = mkOption {…}` composes den-shaped configs (`options.den.*`).
          #
          # `declEntries` carries the provenance the tree walk itself cannot see: each module's own
          # options root beside the file that declared it and its POSITION in the fold. It is read
          # through `sitesAt` — at every redeclaration step where both declarations carry a type
          # (the declared-type list decides the type), on a refusal, and when a shadow record's
          # `file` is read. The position is what a shadow record needs to name its
          # contributor; the fold therefore hands each step its own index rather than one shared
          # rule. The locs the walk hands over are PREFIXED (the fold's `loc` IS `prefix`) while
          # these trees are not, hence the `drop`.
          #
          # ★ THE SHAPE HERE IS `declarationStratum`'s, over the VALUE stratum's arguments, and the
          # guard above is what makes the two agree on everything a declaration is: the key set and
          # the imports expansion. Where they could differ is a descriptor field, which may hold a
          # stratum-2 value (its `default`, `apply`, or a `type` read from a module argument), and
          # that difference is the point.
          declEntries =
            if declarationGuard ? flat then declarationGuard.declEntries else prelude.imap0 declEntry flat;
          sitesAt =
            if declarationGuard ? flat then
              declarationGuard.sitesAt
            else
              declaringSitesAt (length prefix) declEntries;
          # ONE door for the whole engine: every downstream reader (`mergeTree`'s
          # `declaredPairs`, `declLeafEntries`, `moduleDefFootprint`, `declaringSitesAt`) consumes
          # `allOptions` or a value traced back to it, so guarding the producer here covers all
          # five tags at any nesting depth on both the `.options` and `.config` planes.
          allOptions = mergeOptionDeclTrees (redeclareDecl sitesAt) prefix (
            if declarationGuard ? flat then
              declarationGuard.validated
            else
              map (e: validateDeclSubtree prefix e.options) declEntries
          );

          # ── warm decision + splice context (design spec §§1-2) ─────────────────────────────────
          # EDITED entries by ORIGIN, from the engine's OWN closure (imports expansion is
          # config-dependent, so a caller count is untrusted): the closure is breadth-first, so an
          # appended module's imports interleave with the base's and are no tail of `flat`. The edited
          # nodes are the closure of the edited roots, moved to the tail `warmDecide` reads. A node
          # reached from both a base root and an edited root has no single origin, so warm is REFUSED
          # (cold fallback, reason stated). `decision` is LAZY — the eval PATH is
          # zero-cost when the knob is off: the cold path (`warmFrom == null`) never forces `decision`
          # (`warmActive` short-circuits on the null check), so no classification/footprint runs. (An
          # explicit read of `.warmDecision.modules` on a cold result DOES force classification — the
          # trace is data on demand, consistent with the `reused`/`remerged` cost note below.) Warm is
          # REFUSED (cold fallback) when an edited entry carries `disabledModules` (§2 guard) — defence
          # only; unreachable through `evalModuleTree` while module removal is refused
          # (`moduleSyntaxChecked`).
          # Warm is also REFUSED (cold fallback, reason stated) when `warmFrom` was evaluated under a
          # different effective strictness, or records none (a result from an evaluator that predates
          # `warmDecision.strict` reads `null`). Every reused leaf is `getAttrByPath` of the prior's
          # `config`, whose WHNF carries the PRIOR's `_orphanCheck`, so reuse across a change of
          # `check` would refuse where cold is a value, or admit where cold refuses (ADR-0008 item 2:
          # warm is byte-identical to cold). The key is on the admission, not per leaf, for that
          # reason, and it is read inline, here and in `reason`, since a `let` binding costs a thunk
          # per evaluation. At this, the only warm site, `strict` is `check` (`inherited` is `false`
          # at the top). A nested owner's own strictness changing underneath is covered by the
          # plane's standing premises: a dirty declaring module re-merges, and `specialArgs` are
          # unchanged between evaluations.
          origin =
            let
              baseLen = length modList - length editedModules;
              # the node keys come from the identity-keyed closure, in `flat`'s order (`moduleFamily`)
              top = moduleTop callM modList;
              graph = closeModules top.roots;
              roots = top.roots;
              aligned = alignedGraph "the warm origin split" flat graph;
              keyAt = i: (builtins.elemAt aligned i).key;
              editKeys = map (e: e.key) (closeModules (drop baseLen roots));
              baseKeys = listToAttrs (
                map (e: {
                  name = e.key;
                  value = true;
                }) (closeModules (take baseLen roots))
              );
              editSet = listToAttrs (
                map (k: {
                  name = k;
                  value = true;
                }) editKeys
              );
            in
            if editedModules == [ ] then
              {
                inherit flat;
                editedCount = 0;
                collision = false;
              }
            # a list that imports nothing and shares no node keeps every module in order, so its
            # edited entries are its tail
            else if
              length flat == length modList && all (e: !(e.content ? imports || e.content ? require)) flat
            then
              {
                inherit flat;
                editedCount = length editedModules;
                collision = false;
              }
            else
              {
                flat =
                  let
                    at = prelude.imap0 (i: e: {
                      inherit e;
                      k = keyAt i;
                    }) flat;
                  in
                  map (x: x.e) (filter (x: !(editSet ? ${x.k})) at ++ filter (x: editSet ? ${x.k}) at);
                editedCount = length editKeys;
                collision = prelude.any (k: baseKeys ? ${k}) editKeys;
              };
          decision = warmDecide {
            inherit (origin) flat editedCount;
            inherit
              allOptions
              warmFrom
              ;
          };
          warmActive =
            warmFrom != null
            && warmFrom.warmDecision.strict or null == strict
            && !decision.disabledRefusal
            && !origin.collision;
          warmCtx =
            if warmActive then
              {
                active = true;
                inherit (decision) isClean;
                prevConfig = warmFrom.warmDecision.uncheckedConfig;
                prevProv = warmFrom.provenance;
                prevDefs = warmFrom.optionDefs.defs;
                # The prior eval's OWN undeclared report, read by `mergeTree`'s reused leaf only when
                # the leaf's type carries `mergeDefs.reported` (see there). Its paths are absolute, the
                # frame of `mergeTree`'s `reported` channel, so the reader passes them through as is.
                prevUndeclared = warmFrom.undeclared;
                inherit mergeOption;
              }
            else
              {
                active = false;
                inherit mergeOption;
              };
          # The rich option merge (`{ value; prov }`): the realizer reads BOTH the value tree and the
          # provenance tree from one shared discharge/priority pass per declared leaf. It rides the
          # descent's context, with this node's `reader`, through which a declared option that may
          # nest reads its nested trees as this node's `nested` children (den-hoag-n6dh7 item 5);
          # `prefix` makes the option's group its path within the tree.
          #
          # On a PARTIAL knot (den-hoag-5ov3p) the record's `value` is a definition again, as
          # `mergeDefsPartial`'s is: the winners' value under the priority that selected them (bare at the
          # default priority), and with no winners the monoid's identity. The declared default is one of the
          # definitions, at `mkOptionDefault`, so a default-only option is that definition. `prov`,
          # `undeclared` and `typeDefs` ride through. Selected here, with no binding of its own, so a full
          # evaluation pays nothing for it.
          mergeOption =
            (
              if knot.partial then
                mode: loc: optDecl: rawDefs:
                let
                  r = mergeOptionWith mode loc optDecl rawDefs;
                in
                r
                // {
                  value =
                    if r.prov.winners == [ ] then
                      {
                        _type = "if";
                        condition = false;
                        content = { };
                      }
                    else if r.prov.priority == defaultPriority then
                      r.value
                    else
                      {
                        _type = "override";
                        priority = r.prov.priority;
                        content = r.value;
                      };
                }
              else
                mergeOptionWith
            )
              {
                inherit
                  coreShortCircuit
                  carried
                  strict
                  prefix
                  ;
                reader = self;
                inherit result;
              };
          # Reuse the WHOLE prev freeform layer iff the coarse flag holds (§2, soundness-forced: a
          # single edited freeformType flips every freeform loc). Else re-merge cold. Byte-identical
          # either way when the flag holds; the flag exists to keep the SKIP sound.
          reuseFreeform = warmActive && decision.reuseAllFreeform;

          # Config attrsets (shorthand-aware), config-root properties pushed to keys. Every config
          # read forces this for every entry, so it is where the module-syntax refusals fire.
          pushed = map pushedEntry flat;

          # `_module.args` merges as nixpkgs' `lazyAttrsOf raw`: each module's `_module` and `args`
          # are pushed down a level at a time (so `mkIf`/`mkMerge`/`mkOverride` around them
          # distribute as on any option path), each argument's defs are discharged and
          # priority-filtered, and MORE THAN ONE WINNER REFUSES BY NAME, naming the argument and every
          # winning file in fold order. Identical values refuse too: `raw` merges with
          # `mergeOneOption`, which compares nothing. Different argument names are a union. A
          # last-wins `recursiveUpdate` fold stood here, and the winner of a same-name pair was
          # whichever module came last. Lazy per argument: a value is forced only when it is read.
          #
          # IT IS NOT THE FREEFORM FEEDER: `freeformType` is collected PER MODULE
          # (`moduleFreeformEntries`), so N contributions reach `filterOverrides` as N defs.
          #
          # Where a module declares `options._module`, a re-declared `_module.args`' `apply` maps the
          # merged set, `name` included, as nixpkgs' does (`moduleOwnArgs`). The test is inline, so a
          # tree that declares no `options._module` allocates nothing for it.
          moduleArgs =
            if allOptions ? _module then
              moduleOwnArgs knot.positioned prefix (moduleOwnSites sitesAt prefix allOptions null "args") pushed
            else
              builtins.zipAttrsWith mergeModuleArg (moduleArgSetsOf pushed);
          # freeformType is priority-resolved (nixpkgs treats it as an option): a top-level
          # `freeformType` (bare, prio 100) beats a `_module.freeformType = mkDefault …` (prio 1000)
          # — this is how strict.nix's throw-on-unknown default yields to a kind's own freeform.
          #
          # ★ THE WINNERS ARE MERGED THROUGH THE TYPE ALGEBRA, NEVER SELECTED. `filterOverrides`
          # keeps every def of minimum priority-number and its contract says they are "all kept and
          # merged downstream"; taking `last` of them was the whole of the downstream, so two
          # equal-priority contributions destroyed one declaration with no diagnostic on any channel
          # — not `config`, not `provenance`, not `freeformProv`, not `undeclared`. This is the
          # DEFINITION-side twin of `redeclareDecl`: both read the declared-type list through
          # `mergeDeclaredTypes`, bracketed as nixpkgs' `types.optionType.merge` brackets it (the
          # last winner decides against each earlier one), and turn a refusal into a named one; the
          # two planes give one list one answer. A merge that succeeds displaces nothing, so
          # there is no `overridden` analogue here and none is wanted.
          #
          # The refusal names EVERY contributing file in fold order, undeduplicated — the same
          # convention `declaringSitesAt` gives the declaration plane, and for the same reason: the
          # pair holding the refusal is not the set of modules the author has to reconcile.
          # The refusing pair is the first step that refuses, which under the bracketing is the
          # LAST two contributions first; a relation-worded reason names the deciding (later) type
          # first, and only the null-reason fallback reads in authored order — the same text rule
          # as `redeclareDecl`, by construction, since both report `declaredRefusalText`.
          #
          # The one-winner path attempts no merge: it keeps its current cost and its current type
          # IDENTITY, which is what `strict.nix`'s throw-on-unknown default depends on.
          # The freeform declarations by KEY, value unforced: the candidates below, and the
          # `nested` product's test for a freeform group (den-hoag-i4c0n), which must not force a type.
          freeformDeclared =
            map topFreeformEntry (filter hasTopFreeform flat) ++ concatMap moduleFreeformEntries pushed;
          freeform =
            if allOptions ? _module then
              moduleOwnApply (moduleOwnSites sitesAt prefix allOptions null "freeformType") (
                resolvedFreeform freeformDeclared
              )
            else
              resolvedFreeform freeformDeclared;

          # Definition order is REVERSE flattened-module order — byte-identical to nixpkgs, which
          # collects defs last-module-first (observable in list-typed options: `[a] [b] [c]` merges
          # to `[c b a]`; verified against `lib.evalModules`). Order-independent for scalars
          # (equal-priority ⇒ conflict) and attrsets (`//`), load-bearing only for lists. One reverse
          # here; the per-level descent preserves it (nixpkgs `reverseList` once, then `zipAttrs`).
          pushedRev = reverse pushed;

          # The realizer's def stream: each module's pushed-down config, REVERSED, read through
          # `moduleDefOf` (inlined behind the presence test, so a module with no `_module` pays
          # nothing): the engine's own `_module` keys are taken out, the rest stay config. The
          # `modIndex` (position in reverse-module order) rides each def so the root freeform can
          # coalesce unmatched keys back into one wide def per originating module.
          topDefs = prelude.imap0 (i: p: {
            file = p._file;
            modIndex = i;
            value =
              if p.attrs ? _module then
                moduleRest p._file p.attrs (pushDownProperties p.attrs._module)
              else
                p.attrs;
          }) pushedRev;

          # `_module.check` is an option of this evaluation's own `_module` group (`bool`, default
          # `true`), so a module's definition merges with priorities and a conflicting pair is refused
          # by `bool`'s merge. A passed door enters as one `mkDefault` definition after the modules'.
          realized =
            (
              if check == null then
                mergeTree warmCtx [ ]
              else
                o: d:
                mergeTree warmCtx [ ] o (
                  d
                  ++ [
                    {
                      file = "<gen-merge: evalModuleTree { check }>";
                      modIndex = length d;
                      value._module.check = priority.mkDefault check;
                    }
                  ]
                )
            )
              (
                if allOptions ? _module then
                  if isOptLeaf allOptions._module then
                    if all (s: (s.decl.type.name or null) == "submodule") (sitesAt (prefix ++ [ "_module" ])) then
                      let
                        # The leaf's sub-options are a nested evaluation: read once for the four keys.
                        leafSub = moduleLeafSubOptions allOptions._module.type (prefix ++ [ "_module" ]);
                      in
                      foldl' (
                        acc: k:
                        builtins.seq (moduleOwnJudged sitesAt prefix allOptions leafSub pushed freeformDeclared k) acc
                      ) allOptions moduleOwnKeys
                    else
                      throw "gen-merge: option `${
                        showOption (prefix ++ [ "_module" ])
                      }' is declared as a single option, but the engine owns its sub-keys `args', `freeformType', `check' and `specialArgs': declare `options._module.<name>' instead; declared in ${
                        concatStringsSep ", " (map (s: s.file) (sitesAt (prefix ++ [ "_module" ])))
                      }"
                  else
                    foldl'
                      (
                        acc: k: builtins.seq (moduleOwnJudged sitesAt prefix allOptions null pushed freeformDeclared k) acc
                      )
                      (
                        allOptions
                        // {
                          _module = builtins.removeAttrs allOptions._module moduleOwnKeys // {
                            check = {
                              _type = "option";
                              type = types.bool;
                              default = true;
                            };
                          };
                        }
                      )
                      (filter (k: allOptions._module ? ${k}) moduleOwnKeys)
                else if check != null || prelude.any (d: d.value ? _module) topDefs then
                  allOptions
                  // {
                    _module = {
                      check = {
                        _type = "option";
                        type = types.bool;
                        default = true;
                      };
                    };
                  }
                else
                  allOptions
              )
              topDefs;
          declaredConfig = realized.value;
          # This evaluation's strictness for its nested trees, keyed on the door (H′): its own `check`,
          # or a carrying tree's. A module's `_module.check` decides this level's first refusal arm
          # only (`_orphanCheck`). Bound in this `let`, not the outer one, where it costs alloc.
          strict = (check == null || check) || inherited;

          # Unknown keys — at ANY depth — route as ONE freeformType def-set at the ROOT (nixpkgs
          # freeform), each reshaped to its full nested path so lazyAttrsOf/attrsOf owns the per-key
          # merge. With no freeform they are orphans → the option does not exist → throw (per level).
          # A finding is refused at its OWNER's level, when that level is read: nixpkgs' per-level rule
          # (`checkUnmatched` is `seq`'d onto its own evaluation's result only). The owner of a nested
          # tree's finding is the nested evaluation that did not merge the definition, and it refuses
          # under its EFFECTIVE strictness: its own `check` (the first arm, in its own words), or
          # `inherited`, set when an evaluation carrying its report is strict (the second arm). Both
          # arms read the owner's own `freeform`: a key the owner's `freeformType` absorbs is no
          # finding. No level refuses `realized.reported`. Deciding a descendant's findings here would
          # force every carried nested evaluation down to its option merges on this level's WHNF, and
          # a nested `mkIf` reading this tree's own config would close a cycle through the gate. So a
          # read that does not reach the owner's value (a sibling leaf, an `apply` that discards the
          # tree) is not refused, as in nixpkgs. An OUTER `freeformType` never absorbs a nested
          # finding: its key has an associated option (the declared leaf that owns the nested tree),
          # so it lies outside that type's domain ("definitions that don't have an associated
          # option"), and the owner refuses it whatever the outer `freeform` is. This extends the
          # standing divergence from `lib.evalModules` that
          # `test-a-lax-nested-tree-is-still-refused-by-a-strict-parent` pins (nixpkgs admits a strict
          # parent over a lax child) to the freeform regime.
          _orphanCheck =
            if
              (declaredConfig._module or { }).check or (check == null || check)
              && freeform == null
              && realized.unmatched != [ ]
            then
              let
                # imported here, on the refusal path only, so no success path allocates it
                undeclaredText = import ./undeclared-text.nix { inherit prelude showDefLine escapeIdentifier; };
                first = firstUnmatched realized.unmatched;
                optText = showOption (prefix ++ first.path);
                file = toString (first.file or "<unknown-file>");
                # nixpkgs' two contexts: a value that aborts uncatchably inside the print still names
                # the option and its file in the trace
                defText = builtins.addErrorContext "while evaluating the error message for definitions for `${optText}', which is an option that does not exist" (
                  builtins.addErrorContext "while evaluating a definition from `${file}'" (
                    undeclaredText.showDef first
                  )
                );
                parent = prelude.init first.path;
                # the engine-owned `_module.<k>` are declared options in nixpkgs' tree, and in this one
                # only when a module redeclares them, so they join the group's names
                siblings = attrNames (
                  foldl' (acc: seg: if isAttrs acc && acc ? ${seg} then acc.${seg} else { }) allOptions parent
                  // (if parent == [ "_module" ] then prelude.genAttrs moduleOwnKeys (_: null) else { })
                );
                head' = "The option `${optText}' does not exist. Definition values:${defText}${
                  undeclaredText.suggestion (s: showOption (prefix ++ parent ++ [ s ])) (prelude.last first.path) (
                    filter (n: parent != [ ] || n != "_module") siblings
                  )
                }";
              in
              # nixpkgs' hint test is `attrNames options == [ "_module" ]`; this tree carries `_module`
              # only when a module declares under it
              if attrNames (builtins.removeAttrs allOptions [ "_module" ]) != [ ] then
                throw head'
              else if prefix == [ ] then
                throw "${head'}\n\nIt seems as if you're trying to declare an option by placing it into `config' rather than `options'!\n"
              else
                throw "${head'}\n\nHowever there are no options defined in `${showOption prefix}'. Are you sure you've\ndeclared your options properly? This can happen if you e.g. declared your options in `types.submodule'\nunder `config' rather than `options'.\n"
            else if inherited && freeform == null && realized.unmatched != [ ] then
              throw "gen-merge: option `${
                showOption (prefix ++ (head realized.unmatched).path)
              }' is not declared by the nested tree that owns it"
            else
              null;
          # An unmatched def has THREE dispositions and no fourth: a `freeformType` absorbs it (below),
          # `check` refuses it (above), or — with neither — it is not merged into `config` at all. The
          # third is the one that returns neither a value nor a named refusal, and it is why this channel
          # exists — but the report is NOT scoped to it. Every unmatched def the freeform plane did not
          # absorb is REPORTED here, the refused ones included: the report's extension is exactly
          # `_orphanCheck`'s, so under `check = true` the same defs are listed while `config` throws.
          # Always on a result sibling, never inside `config`: `check = false`'s whole purpose is that the
          # merged value does NOT grow the key, and a report living there would change what the flag
          # produces instead of describing it.
          #
          # `check` does not gate the report — whether the engine tells the truth about what it consumed
          # is not a checking question. The freeform plane gates THIS LEVEL's own definitions only
          # (`realized.unmatched`), because there those defs ARE merged and nothing was dropped. A nested
          # tree's findings (`realized.reported`) are never absorbed (see `_orphanCheck`), so they are
          # reported under every regime, and refused by the nested tree that owns them, never here. Order: this level's own definitions first, then nested
          # findings; order is promised per key only.
          #
          # By construction, not a new tracking layer: the first part is `realized.unmatched` (the same
          # records `coalesceUnmatched` and `freeformProvCold` read) minus its `value`s, prefixed into
          # the absolute frame; the second is `realized.reported`, already absolute and appended as is.
          # Names and originating files are already carried; the VALUES are deliberately dropped, so
          # reading the report forces no definition value of this level's own. It DOES force the
          # definitions of every leaf whose declared type carries `mergeDefs.reported` (a nested tree's
          # findings cannot be named without its key set, so a moduleTree def that is a bare `throw`
          # fires here); that set is the report channel's whole domain. Inheriting that list inherits
          # its reach: like `freeformProvCold`'s records the report
          # may be OVER-INCLUSIVE — a false-`mkIf`-wrapped def still shows here, because properties are
          # discharged per key only inside `freeform.merge`, which this pass does not enter. That is the
          # report↔refusal correspondence holding rather than leaking: the same def under `check = true`
          # is refused, and a discharge filter here would desynchronise the two.
          #
          # Paths are absolute against `prefix`, like the refusal message above, and are CAPTURE
          # paths — the first undeclared name on each branch (`mergeTree`'s `ownUnmatched`). An
          # undeclared key is captured with its whole subtree, since with no declaration nothing says
          # where the option path ends and an attrset VALUE begins; a path here therefore means "this
          # loc and everything beneath it was not merged".
          undeclared =
            (
              if freeform == null then
                map (u: {
                  path = prefix ++ u.path;
                  inherit (u) file;
                }) realized.unmatched
              else
                [ ]
            )
            ++ realized.reported;
          # Coalesce the per-key unmatched defs into one wide def per originating module BEFORE the
          # freeform type's fold (see `coalesceUnmatched`) — restores nixpkgs' per-module freeform
          # shape, so `attrsOf`/`lazyAttrsOf` stays linear in sibling-key count (byte-identical
          # output). The fold is `rawFold`, not `ownFold`: nixpkgs merges the freeform plane with the
          # type's raw `merge` (`freeformType.merge prefix defs`), outside `mergeDefinitions`, so a
          # foreign type's `check` and v2 protocol do not apply here. The keys it owns are checked by
          # its own merge, as they are there. The fold demands a type, so a freeform type that is not
          # one is refused here by name, once per evaluation (`interface.typeDefect`).
          freeformConfigCold =
            if freeform == null || realized.unmatched == [ ] then
              { }
            else if interface.typeDefect freeform != null then
              throw "gen-merge: the freeform type${
                if prefix == [ ] then "" else " at `${showOption prefix}'"
              } ${interface.typeDefect freeform}"
            else
              rawFold (
                if interface.canNest freeform then
                  threadedAs (evAt {
                    reader = self;
                    inherit result;
                  } "freeform") (interface.homedAt "evalModuleTree" prefix freeform)
                else
                  freeform
              ) prefix (coalesceUnmatched false (length topDefs) realized.unmatched);
          # Warm: reuse prev's whole freeform layer (byte-identical when `reuseFreeform`), skipping the
          # freeform fold's re-run; else the cold layer. The cold thunk stays unforced under reuse.
          freeformConfig = if reuseFreeform then warmFrom.freeformConfig else freeformConfigCold;

          # Declared wins over freeform at shared paths (nixpkgs `recursiveUpdate freeform declared`);
          # for the common disjoint-key case this is just `//`.
          #
          # The RETURNED/embedded `config` stays `_module`-free, exactly like nixpkgs — its
          # `(evalModules).config` strips `_module`, so the parity oracle and every consumer that reads
          # the merged value never sees it.
          config = builtins.seq _orphanCheck uncheckedConfig;
          # The merged value BEFORE this level's refusal, which its modules receive (`moduleConfig`),
          # as nixpkgs hands them its unchecked fixpoint: a module computing `_module.check` from
          # `config` reads it without forcing the refusal that `check` decides.
          uncheckedConfig =
            if freeformConfig ? _module || declaredConfig ? _module then
              builtins.removeAttrs (recursiveUpdate freeformConfig declaredConfig) [ "_module" ]
            else
              recursiveUpdate freeformConfig declaredConfig;

          # The MODULE-VISIBLE config (`baseArgs.config`) carries `_module` as nixpkgs' does: the four
          # keys its `internalModule` declares, every evaluation, beside whatever `_module.<x>` the
          # modules' own declarations or freeform merged (the returned config drops it). Consumers read
          # the WHOLE `args` map to enumerate args dynamically: gen-schema's `mkInstanceType` sets
          # `config._module.args.${kind} = config` and den's `resolvedCtxModule` reads
          # `config._module.args` to build the entity resolution context (it can't enumerate `...`
          # function args). A positioned evaluation's `args` holds its `name`; where a module declares
          # `options._module`, `moduleArgs` already holds it, after any `apply` (`moduleOwnArgs`).
          # `check` is the strictness that governs this evaluation's refusal of an undeclared key,
          # `_orphanCheck`'s two arms: the merged `_module.check` (a module's value, else the door's,
          # else `true`), or `inherited`. That is what nixpkgs' option reports: a module's own
          # `_module.check` reads back as set, and a child of an unchecked tree's `.type` under a
          # strict parent refuses as strict and reads `true`, as nixpkgs' (whose `.type` omits the
          # legacy `check`). The view forces nothing it names.
          # The view is one expression, never a binding of its own: a binding is a thunk allocated
          # on every evaluation whether or not a module reads `config`. Each branch states its keys
          # as plain references where it can, so only `args`' extension and `specialArgs`' merge
          # are thunks.
          moduleConfig = uncheckedConfig // {
            _module =
              (
                if !(declaredConfig ? _module) && !(freeformConfig ? _module) then
                  { }
                else
                  recursiveUpdate (freeformConfig._module or { }) (declaredConfig._module or { })
              )
              // (
                if allOptions ? _module then
                  {
                    args = moduleArgs;
                    check = (declaredConfig._module or { }).check or (check == null || check) || inherited;
                    freeformType = freeform;
                    specialArgs = moduleOwnSpecialArgs (
                      prefix
                      ++ [
                        "_module"
                        "specialArgs"
                      ]
                    ) (moduleOwnSites sitesAt prefix allOptions null "specialArgs") specialArgs;
                  }
                else if knot.positioned then
                  {
                    args = moduleArgs // {
                      name = positionNameOf prefix moduleArgs pushed;
                    };
                    check = (declaredConfig._module or { }).check or (check == null || check) || inherited;
                    inherit specialArgs;
                    freeformType = freeform;
                  }
                else
                  {
                    args = moduleArgs;
                    check = (declaredConfig._module or { }).check or (check == null || check) || inherited;
                    inherit specialArgs;
                    freeformType = freeform;
                  }
              );
          };

          # ── provenance (A2 spec §1) ────────────────────────────────────────────────────────────
          # A lazy tree mirroring `config`'s loc structure. Per DECLARED-option loc the rich record
          # `realized.prov` carries (from mergeTree); per FREEFORM loc a REDUCED record built here
          # from `realized.unmatched`. `defs` = the files of the unmatched defs at that loc
          # (winners/priority/defaulted = null — "freeform / not observable", never "no override
          # present"). It reuses `realized.unmatched` — one per-key def per originating module, each
          # carrying its `file`, the SAME structures the value-side freeform coalescing consumes; it
          # does NOT re-walk modules and does NOT force config VALUES (reads only `file`/`path`). It
          # may be OVER-INCLUSIVE: a false-`mkIf`-wrapped freeform def still shows here (the freeform
          # pass, like nixpkgs, discharges per key only inside its own `.merge`, which provenance does
          # not enter). Records are grouped by their (joined) loc with one `builtins.groupBy`, which
          # keeps each group in list order and copies nothing (as `coalesceUnmatched`), then nested
          # into the attrset by a `zipAttrsWith` trie, one level per path step (as
          # `mergeOptionDeclTrees`), so no step copies a growing accumulator. A depth-1 undeclared key
          # and a deeper one can never collide (a key undeclared HERE is captured whole and never
          # descended; cf. `buildModuleUnmatched`); the mixed arm keeps `recursiveUpdate`'s answer for
          # that case anyway, so the construction is total.
          freeformProvCold =
            let
              byPath = builtins.groupBy (u: showOption u.path) realized.unmatched;
              nest =
                rs:
                builtins.zipAttrsWith
                  (
                    _: sub:
                    let
                      here = filter (r: r.rest == [ ]) sub;
                      deeper = filter (r: r.rest != [ ]) sub;
                    in
                    if deeper == [ ] then
                      (head here).record
                    else if here == [ ] then
                      nest deeper
                    else
                      recursiveUpdate (head here).record (nest deeper)
                  )
                  (
                    map (r: {
                      ${head r.rest} = r // {
                        rest = tail r.rest;
                      };
                    }) rs
                  );
            in
            nest (
              map (us: {
                rest = (head us).path;
                record = {
                  defs = map (u: { inherit (u) file; }) us;
                  winners = null;
                  priority = null;
                  defaulted = null;
                };
              }) (builtins.attrValues byPath)
            );
          # Warm: the freeform provenance layer rides the same reuse decision as its config layer.
          freeformProv = if reuseFreeform then warmFrom.freeformProv else freeformProvCold;

          # Declared provenance wins over freeform at shared paths (mirrors config's
          # `recursiveUpdate freeform declared`): a declared GROUP's sub-records overlay the freeform
          # records that bubbled through it; a declared LEAF record is never shadowed (a declared key
          # is never also unmatched).
          provenance = recursiveUpdate freeformProv realized.prov;

          # ── deprecated declared types ──────────────────────────────────────────────────────────
          # `deprecationMessage` is one of the 14 protocol fields lib/types.nix stamps onto every
          # completed type, and it was the one field this engine STORED and never read. A stored
          # field nobody consults is not a neutral placeholder: it makes a protocol-conformance
          # check that asserts PRESENCE pass while the BEHAVIOUR the field exists for is absent, so
          # a deprecated type declared here was indistinguishable from an undeprecated one. The
          # reference engine's answer is `warnDeprecation` (nixpkgs lib/modules.nix), which reports
          # the type's NAME, the option LOC and the DECLARING FILES; those are the four data this
          # record carries, from the same source field.
          #
          # ON THE RESULT, NOT ON STDERR, and that is a mechanism decision rather than a taste one:
          # Nix's eval cache swallows `trace`/`warn` output, so a printed deprecation is present on
          # the first eval and gone on every later one — a report that disappears when the answer is
          # reused reports nothing. A field on the result is the shape that needs no new vocabulary
          # and that a consumer cannot silently drop.
          #
          # THE GROUND IS PRESENCE-VS-BEHAVIOUR, DELIBERATELY NOT "a foreign mount needs it": whether
          # a gen type ever enters a nixpkgs options tree is a separate, contested question (see
          # lib/default.nix), and this report is legible either way — it is gen-merge telling the
          # truth about gen-merge's OWN declarations.
          #
          # SERIALISABLE BY CONSTRUCTION — `type` is the type's NAME, never the type VALUE. A report
          # is something a consumer prints, diffs or hands on; a type value carries functions, so a
          # record holding one could not survive `toJSON` at all.
          #
          # SCOPE, one eval: the declared leaves of THIS tree. A `submodule`'s inner options are
          # declared in a NESTED `evalModuleTree` that runs INSIDE the type's `merge`, and `merge`
          # returns the merged VALUE — byte-compat pins that shape, so the nested eval has no way to
          # hand its report back alongside the value it was called for. That is what makes one eval
          # the scope here; it is NOT that the nested view is unreachable. A consumer that wants it
          # re-derives it at the DECLARATION stratum, which the protocol already exposes: the type's
          # `getSubModules` are the sub-modules and `getSubOptions` is the nested decl tree, so
          # `evalModuleTree { } ty.getSubModules` yields the nested records without
          # touching `merge` at all. Worth knowing before reaching for it: those re-derived records
          # report `declarations = [ "<unknown-file>" ]`, because sub-modules carry no `_file` — which
          # is a reason for the parent not to fold that view into its own report rather than a
          # reason it cannot. Stamping the field is this engine's obligation; composing the strata
          # belongs to whoever composes the results (the same boundary `provenance` and the warm
          # path state for nested evals).
          #
          # LAZINESS: reading this forces each declared leaf's TYPE — that is where the field lives —
          # and no DEFINITION value; leaving it unread costs nothing. `declarations` is a per-record
          # thunk over the existing `sitesAt`, so the common case (no deprecated type) never looks a
          # declaring site up.
          deprecations =
            let
              record =
                e:
                let
                  ty = e.opt.type or null;
                  loc = prefix ++ e.path;
                in
                {
                  path = loc;
                  # Total on both: an option may carry no `type` at all (gen-schema's ref-binding
                  # `apply`-override modules), and a type may state no deprecation in either
                  # vocabulary (a bare parametric gen-types constructor states nothing at all) —
                  # neither is deprecated, and neither may abort the report. A gen type says it in
                  # gen's word; a foreign one says it in the foreign protocol's, which is read where
                  # that protocol is spelled.
                  type = ty.name or null;
                  message = if ty == null then null else ty.deprecated or (interface.importedDeprecation ty);
                  declarations = map (s: s.file) (sitesAt loc);
                };
            in
            filter (d: d.message != null) (map record (declLeafEntries allOptions));

          # ── decision trace (design spec §4) — the memoization DECISION, always-on data on the warm
          # path (the eval computes the partition anyway). Consumed by gen-memo's
          # `warmTrace`/`warmAdmits` (ADR-0031: the warm/override/trace arm moved here from
          # gen-flake's dissolved `override`). Laziness contract: `mode`/`modules` are cheap
          # (classification only);
          # `reused`/`remerged` are O(declared-locs) SPINE-forcing when read (they enumerate the loc
          # partition — never leaf values). Cold (`warmFrom == null`, a prior whose `strict` is not
          # this evaluation's, or a disabledModules refusal) ⇒ nothing spliced ⇒ `reused = [ ]`,
          # `remerged = { }`, with the cold `reason` stated. `strict` is the door-keyed strictness this
          # result was evaluated under, which the next warm admission reads (the effective check can differ).
          # `uncheckedConfig` is the config before its refusal, which a warm evaluation reads for a reused
          # leaf and the identity walk: a prior's refusal is never the next evaluation's.
          #
          # `mode` reports ADMISSION, not reuse: a warm run over a base with no clean module reads
          # "warm" and reuses nothing. `inert` says so at the cheap cost: `true` ⇔ warm was admitted
          # AND no non-edited module is clean (`modules.clean == [ ]`). It forces classification
          # only, never the loc partition. Why `inert` ⇒ `reused == [ ]`: every declared leaf is
          # declared by some module; with none clean, each is declared by a dirty or edited one and
          # so sits in the footprint; and freeform content has no clean contributor to reuse. The
          # implication is one-way: `inert = false` does not promise reuse (a clean base whose every
          # leaf the edit touches reuses nothing too) — only `reused` answers that, at spine cost.
          # A separate field rather than a third `mode` value, so every reader of `mode` as admission
          # keeps its meaning.
          warmDecision =
            let
              reusableLeaves = filter (l: decision.isClean (builtins.toJSON l)) (declLeafPaths allOptions);
              remergedList = decision.footprint ++ (if reuseFreeform then [ ] else decision.freeContribs);
              remerged = foldl' (
                acc: r:
                acc
                // {
                  ${showOption r.path} = acc.${showOption r.path} or r.reason;
                }
              ) { } remergedList;
            in
            {
              mode = if warmActive then "warm" else "cold";
              inert = warmActive && decision.modules.clean == [ ];
              reason =
                if warmFrom == null then
                  "no warmFrom (cold)"
                else if warmFrom.warmDecision.strict or null != strict then
                  "check differs from warmFrom's (warm refused)"
                else if decision.disabledRefusal then
                  "disabledModules on an edited module (warm refused)"
                else if origin.collision then
                  "an edited module reaches a module node the base also reaches (warm refused)"
                else
                  null;
              inherit strict uncheckedConfig;
              # the declaration tree the next warm evaluation walks this one's identities with: the
              # unserved one, as that evaluation walks its own (`nextIdentities`)
              options = allOptions;
              reused = if warmActive then map showOption reusableLeaves else [ ];
              remerged = if warmActive then remerged else { };
              inherit (decision) modules;
            };

          # ── the identity FACT (option-set closure, region 2) ───────────────────────────────────
          # This eval is the ONLY binding in the substrate that holds two evaluations of the same
          # module set at once — `warmFrom.config` and the `config` above — so the fact that an
          # instance's minted identity MOVED between them is nameable here and nowhere else. The
          # DECISION over the fact is gen-memo's (`decision.identitiesHeld`), like every other reuse
          # decision this engine takes; what is computed here is the two maps it decides over.
          #
          # WHY AN IDENTITY AND NOT A DECLARATION PATH. `declLeafEntries` stops at `isOptLeaf`, so on
          # the registry shape `options.hosts` IS the declared leaf and an instance's `id_hash` is
          # never a path in `allOptions` at all — `remerged` reads `{aspects, bobbins, hosts, …}` with
          # no `id_hash` key while two hosts' identities move underneath it. Deepening the leaf walk
          # would change the decision fact for every consumer of this engine to serve one predicate
          # that does not need it; the per-instance map reaches the registry shape with that
          # granularity untouched.
          #
          # THE COST, STATED. This traverses the `id_hash`-bearing values of two configs once per
          # warm re-compose, and it FORCES — which the splice deliberately does not (a spliced leaf
          # stays prev's thunk). That forcing is what makes the refusal total: an identity nobody
          # demanded is an identity that can move unobserved, and a refusal reaching only the
          # demanded ones is one a caller evades by not looking. The bound is the number of minted
          # instances, not the option tree. The COLD path is untouched — `warmActive` is false, the
          # walk never runs, and `identityHeld` is `[ ]` for the same zero-behaviour-change reason
          # `warmFrom`/`coreShortCircuit` default off.
          #
          # MEMBERSHIP IS DECIDED BY THE DECLARATION, never by inspecting a value (ADR-0034's three
          # regimes, read onto this walk; owner-ruled 2026-09-25 on den-hoag-72izy, reversing
          # den-hoag-9iobq's value-first rule 1). An instance is a position whose declaration
          # declares an `id_hash` option — what the one mint stamps (gen-schema `lib/id-hash.nix`).
          # So the walk forces container and group spines and each instance's `id_hash`, and no
          # other declared leaf: an undefined or throwing leaf nobody read stays unread, as cold
          # leaves it (ADR-0008 §2).
          #
          # ── THE BOUND IS THE DECLARATION STRATUM, AND THE CONFIG IS NEVER EXPLORED ──────────────
          # The map is read at positions DERIVED from the declaration side, and the config is read
          # only AT those positions. That is what makes the walk terminate by construction rather
          # than by a cycle guard: a value cycle lives at or below a position whose declared type
          # carries nothing (a derivation is `package`/`raw`/`anything` — and `drv.out == drv`, so
          # every ordinary derivation is self-referential; a completed option type reaches its own
          # cycle at `ty.carries.element.functor.type`, i.e. inside a value sitting at `attrsOf
          # raw`), and a terminal type is where the descent STOPS. An unguarded value walk diverges
          # on both, and `builtins.tryEval` does not contain the abort.
          #
          # Every recursive step consumes either a declaration key (a finite tree), a value key below
          # a container (a finite attrset), or one type constructor (`carries.element` of
          # `carries.element` of … — a finite term). None of them can be renewed by the value.
          #
          # THE POSITIONS ARE NOT `declLeafPaths`, and the paragraph above says why: `declLeafEntries`
          # stops at `isOptLeaf`. The stratum that holds an instance's coordinate is the option tree
          # EXPANDED THROUGH THE TYPE VOCABULARY — a declared leaf is asked what it carries, in the
          # vocabulary `lib/types.nix` already uses to decide the same question at type-construction
          # time (`mkTypeWith`'s `declaresRole`/`carriesSomething`), read through `lib/interface.nix`
          # so a FOREIGN type answers in its own spelling with no second copy of the question — the
          # same boundary call shape `deprecations` above takes for `importedDeprecation`.
          #
          # THE REACH, STATED RATHER THAN LEFT TO BE DISCOVERED. A minted instance must sit at a
          # position whose declared type carries identity; an identity in an untyped slot is not
          # tracked. Not in the map, even when the value there IS an instance on the ecosystem's own
          # `hasId` test: a value AT or BELOW a `raw`/`anything`/`package` leaf, an element of a
          # container of one (`attrsOf raw`), a member of a union (`either` declares nothing of its
          # own, so which member a value is cannot be read off the declaration), and the whole
          # freeform layer, and a foreign module set its declaration does not place at the position
          # (`importedHeldAt`: a container forwarding its element's `getSubModules`, or option records
          # stating no `loc`), at a declared position and as a gen container's element alike. A
          # position whose declaration places an instance there and whose value is not one (nixpkgs'
          # `deferredModuleWith` holds a module) is refused by name, never skipped: no declaration
          # field says so. The refusal domain is the MINTED instances of this option tree, which is
          # what the bound above names; a value carried into an untyped slot is
          # compared by the byte oracle and not by this fact. A self-referential value at a typed
          # STRUCTURAL position is still reachable in principle, since the value's own keys guide that
          # arm — it is a strictly smaller residual than a cycle guard's, and neither a derivation nor
          # a completed type can occupy one.
          identityMapOf =
            declTree: cfg:
            let
              # The lockstep descent: declaration `d` and value `v` at loc `l`, one step each.
              # An INSTANCE is a position whose declaration declares an `id_hash` option, which is
              # what the one mint stamps (ADR-0034: decided at the declaration, never by inspecting
              # a value). Only that instance's `id_hash` is read. `null` there is a nullable's
              # absent instance.
              go =
                loc: d: v:
                if isOptLeaf d then
                  below loc (d.type or null) v
                else if isAttrs d && d ? id_hash && isOptLeaf d.id_hash then
                  # The value contradicting its declaration is refused by name, in the VALUE position
                  # so the refusal fires exactly where `v.id_hash` was forced: gen-memo forces a new
                  # position's key, never its value.
                  (
                    if v == null then
                      { }
                    else
                      {
                        ${showOption loc} =
                          if isAttrs v && v ? id_hash then
                            v.id_hash
                          else
                            throw "gen-merge: `evalModuleTree' at option `${showOption loc}': the warm identity walk reads the option as an instance (its declaration declares `id_hash'), and the value there is ${
                              if isAttrs v then "a set without `id_hash'" else "a ${builtins.typeOf v}"
                            }: the type declared there holds its module set somewhere its declaration does not say";
                      }
                  )
                else if isAttrs d && isAttrs v then
                  # an evaluation's config holds no `_module` (`uncheckedConfig` drops it), so the engine's group is not read
                  foldl' (
                    acc: k:
                    if k == "_module" && !(v ? _module) then acc else acc // go (loc ++ [ k ]) d.${k} (v.${k} or null)
                  ) { } (attrNames d)
                else
                  { };

              # An ELEMENT position IS a declared leaf whose type is the element type — which is what
              # `attrsOf`/`listOf` say themselves, descending to the element under their placeholder
              # segment in `substructure.declares`. Spelling it as a descriptor keeps ONE entry point
              # into the descent, so the `id_hash` test is not written twice.
              elemDecl = ty: {
                _type = "option";
                type = ty;
              };

              # Below a declared leaf, by the TYPE'S OWN ANSWER.
              #
              # A NESTING SEAM STOPS THE WALK, read off the gen-native mark before any protocol read
              # — the fence `mergeTypes` already has. `(evalModuleTree …).type` refuses `functor`, so
              # asking it `importedCarried` would throw on a warm read that cold serves. Its own
              # truthful answer is `nestedTypes = { }` (it wraps no element type), and a nested
              # tree's eval is always cold, the same boundary provenance draws.
              below =
                loc: ty: v:
                if !(isAttrs ty) then
                  { }
                else
                  let
                    element = interface.importedCarried "element" ty;
                    # Where the type's own `declares` puts its element: `loc` for a wrapper, one
                    # segment below for a container, `null` for a type carrying no single element.
                    elementAt = interface.importedElementPrefix ty loc;
                  in
                  # AN ELEMENT THAT CARRIES NOTHING declares no instance at any depth (`listOf str`,
                  # `attrsOf raw`, `nullOr str`), so neither the value nor the type's level is read.
                  if
                    element != null
                    && interface.importedCarried "element" element == null
                    && (interface.importedSubstructure element).modules == null
                  then
                    { }
                  # A WRAPPER THAT ADDS NO PATH LEVEL (gen's `nullOr`, any type whose `declares`
                  # hands its element the same prefix) holds its element's value AT
                  # this position, so it is re-entered here with the element type rather than
                  # iterated: the value's keys are the element's own options, not entries.
                  else if element != null && elementAt == loc then
                    below loc element v
                  # AN ELEMENT WHOSE POSITION THE TYPE DOES NOT STATE: the type carries an element but
                  # has no rebuild to ask where it sits — a raw foreign record (nixpkgs' `listOf`,
                  # `nullOr`, `uniq`, …), or one that crossed stating its own relation and so owes no
                  # `recarry`. Wrapper and container cannot be told apart, and either guess reads the
                  # wrong level; the functor payload would answer only by being read for what the type
                  # carries, which it does not state. So its entries are not walked: a moved identity
                  # there is served warm, equal to cold. The module-set arm below is not a fallback
                  # either: it would hand the ELEMENT's declarations to the container's value at the
                  # container's own loc, and read an entry name as an instance.
                  else if element != null && elementAt == null then
                    { }
                  else if element != null then
                    # A container: one level into the VALUE's keys or indices, each with the element
                    # type. Asked FIRST, because a container's module set IS its element's — a
                    # registry would otherwise answer the module-set arm below and skip the key level
                    # its instances live at.
                    #
                    # ── ONE EXPANSION FOR THE WHOLE CONTAINER, AT THE PLACEHOLDER ────────────────
                    # Handing every key the element DESCRIPTOR re-enters the module-set arm below at
                    # that key's own loc, and `substructure.declares` is a nested `evalModuleTree`
                    # TAKING THE PREFIX — so the element's entire declaration eval re-runs once per
                    # ENTRY and Nix shares nothing between the applications. On a registry that is
                    # the dominant cost of this whole walk, and it buys nothing: what a container's
                    # element declares does not vary with the key, and every vocabulary that answers
                    # this question says so itself. `attrsOf`/`listOf` expose the element's surface
                    # under a LITERAL PLACEHOLDER segment (`lib/types.nix:366` and `:324`), and
                    # nixpkgs' `getSubOptions` appends the same two placeholders — which is what
                    # makes the hoist legible across `interface` rather than a gen-side shortcut.
                    # Expanding at `loc ++ [ placeholder ]` is therefore the DECLARATION STRATUM's
                    # own coordinate for this position, bound once here and shared by every entry;
                    # the per-key coordinate stays on `loc`, which is what the map is keyed by.
                    #
                    # The element's own answer is asked, not the container's, and only when the
                    # element is not ITSELF a container: a nested container's expansion would append
                    # a second placeholder and answer for the element's element, one level below the
                    # keys this arm is walking. That case keeps the descriptor and re-hoists at its
                    # own level. A foreign element is asked where its module set sits, as the
                    # module-set arm below asks, at the placeholder coordinate its declaration was
                    # stamped at: one forwarding its set to a level further down (a `coercedTo` over
                    # a `listOf`, a stripped `listOf`) holds no instance at the entry, and its entries
                    # are not walked.
                    let
                      edAt =
                        ph:
                        let
                          elemSub = interface.importedSubstructure element;
                        in
                        if interface.importedCarried "element" element != null || elemSub.modules == null then
                          elemDecl element
                        else
                          let
                            d = elemSub.declares (loc ++ [ ph ]);
                          in
                          if element ? substructure || interface.importedHeldAt (loc ++ [ ph ]) d then d else { };
                    in
                    if isAttrs v then
                      let
                        ed = edAt "<name>";
                      in
                      foldl' (acc: k: acc // go (loc ++ [ k ]) ed v.${k}) { } (attrNames v)
                    else if isList v then
                      let
                        ed = edAt "*";
                      in
                      foldl' (acc: m: acc // m) { } (prelude.imap0 (i: x: go (loc ++ [ (toString i) ]) ed x) v)
                    else
                      { }
                  else
                    let
                      sub = interface.importedSubstructure ty;
                    in
                    # A type naming a module set: expand what it DECLARES and re-enter the lockstep
                    # descent at the same loc. `substructure.declares` runs a nested `evalModuleTree`
                    # with no defs supplied, so the expansion is a declaration-side spine eval and no
                    # instance-authored value is forced.
                    if sub.modules == null then
                      { }
                    else
                      let
                        decl = sub.declares loc;
                      in
                      # A gen record states its module set by its own construction; a foreign one is
                      # asked where the set sits, and one holding it below its position is not walked.
                      if ty ? substructure || interface.importedHeldAt loc decl then go loc decl v else { };
            in
            go [ ] declTree cfg;

          identityHeld =
            if !warmActive then
              [ ]
            else
              decision.identitiesHeld
                {
                  # Lazy, and read only inside the refusal — see gen-memo's note on the same argument.
                  remerged = attrNames warmDecision.remerged;
                }
                {
                  # EACH CONFIG IS WALKED WITH ITS OWN TREE. `warmFrom` is a prior result record and
                  # this one exports `options = allOptions`, so the prior tree is already in hand.
                  # Using `allOptions` for both would be wrong and silently so: a decl-side edit that
                  # ADDS an option is the discrimination the warm path exists to make, and one that
                  # REMOVES an option leaves the next tree under-describing the prior config.
                  priorIdentities = identityMapOf warmFrom.warmDecision.options warmFrom.warmDecision.uncheckedConfig;
                  nextIdentities = identityMapOf allOptions config;
                };

        in
        {
          inherit
            config
            identityHeld
            moduleConfig
            moduleArgs
            provenance
            undeclared
            deprecations
            freeformConfig
            freeformProv
            warmDecision
            ;
          optionDefs = {
            defs = realized.typeDefs;
            values = realized.value;
            # The evaluated half of the engine's own `_module` records (`moduleOwn.serve`), read only
            # where a record is served: each key's value off the module-visible view, and the
            # definitions nixpkgs' option for it reads. `check` is an option of `realized` wherever a
            # module or the door touches `_module`, and its default alone otherwise.
            moduleOwn =
              let
                # GATE PROBE: the four values off their own bindings, never through `moduleConfig`
                m = {
                  args =
                    if allOptions ? _module || !knot.positioned then
                      moduleArgs
                    else
                      moduleArgs // { name = positionNameOf prefix moduleArgs pushed; };
                  check = (declaredConfig._module or { }).check or (check == null || check) || inherited;
                  freeformType = freeform;
                  specialArgs =
                    if allOptions ? _module then
                      moduleOwnSpecialArgs (
                        prefix
                        ++ [
                          "_module"
                          "specialArgs"
                        ]
                      ) (moduleOwnSites sitesAt prefix allOptions null "specialArgs") specialArgs
                    else
                      specialArgs;
                };
                realizedCheck = (realized.typeDefs._module or { }).check or null;
                # in nixpkgs' definition order, the module list reversed
                ff = moduleOwn.winners (
                  reverse (
                    map (c: {
                      file = c._file;
                      value = c.type;
                    }) (filter (c: c.type != null) freeformDeclared)
                  )
                );
              in
              {
                args = {
                  value = m.args;
                }
                // moduleOwn.winners (
                  (
                    if knot.positioned then
                      [
                        {
                          file = moduleOwn.file;
                          value.name = (positionArgsAt prefix).name;
                        }
                      ]
                    else
                      [ ]
                  )
                  ++ reverse (
                    map (d: {
                      file = d._file;
                      value = d.args;
                    }) (moduleArgDefsOf pushed)
                  )
                );
                check =
                  if realizedCheck == null then
                    {
                      value = m.check;
                      defs = [
                        {
                          file = moduleOwn.file;
                          value = true;
                        }
                      ];
                      prio = 1500;
                    }
                  else
                    {
                      value = m.check;
                      defs = map (d: {
                        inherit (d) value;
                        file = if d.file == "<default>" then moduleOwn.file else d.file;
                      }) realizedCheck;
                      prio =
                        let
                          p = provenance._module.check.priority;
                        in
                        if p == null then 9999 else p;
                    };
                freeformType = {
                  value = m.freeformType;
                }
                // (
                  if ff.defs == [ ] then
                    {
                      defs = [
                        {
                          file = moduleOwn.file;
                          value = null;
                        }
                      ];
                      prio = 1500;
                    }
                  else
                    ff
                );
                specialArgs = {
                  value = m.specialArgs;
                  defs = [
                    {
                      file = moduleOwn.file;
                      value = specialArgs;
                    }
                  ];
                  prio = 100;
                };
              };
          };
          options = allOptions;
          # THE NESTED POSITIONS OF THIS TREE (den-hoag-n6dh7 item 2): one group per declared
          # option, in declaration order, and one for the freeform plane, last. Read by the minting
          # knot alone, and built only on an evaluation that mints.
          # THE MODULE GRAPH OF THIS TREE (den-hoag-470xp): the closure the family `nta.modules` mints
          # from, one node per entry, and only when the family is read (`knotModules`).
          _flat = flat;
          _modList = modList;
          _callM = callM;
          _nested =
            if knot.mints then
              nestedGroups {
                inherit prefix carried strict;
                # A child's own run is on its position record; a root counts `0` (item 4).
                emptyRun = if knot.inner then (self.getHostAt "positions").emptyRun else 0;
                leaves = realizedLeaves realized;
                normalize =
                  if coreShortCircuit then
                    map (d: if isCoreValue d.value then d // { value = d.value.values; } else d)
                  else
                    defs: defs;
                freeform = {
                  declared = freeformDeclared != [ ];
                  type = freeform;
                  defs =
                    if freeform == null || realized.unmatched == [ ] then
                      [ ]
                    else
                      coalesceUnmatched true (length topDefs) realized.unmatched;
                };
              }
            else
              null;
        }
      );
      result = knot.drive body;
    in
    # A CHILD of the one evaluation is its knot's own node, so its evaluation is the BODY, which the
    # child applies to its reader and its own attribute (`childTree`): the evaluation that holds it
    # reads `config` and `undeclared` off that record, and nothing reads the rest of the published one.
    if knot.inner then
      body
    else
      {
        # ── the refusal's ONE forcing site ────────────────────────────────────────────────────────
        # Interposed on the EXPORTED config, never on `result.config`. The two are the same value, and
        # the difference is who reads which: modules inside the fixpoint see `result.moduleConfig`,
        # which is built FROM the unchecked config, so seq-ing the identity verdict onto the inner binding
        # would make a module's ordinary `config.x` read force a walk over the config that read is
        # helping to produce — infinite recursion, not a refusal. Out here nothing in the fixpoint can
        # reach it, and every consumer of a warm re-compose goes through this attribute.
        #
        # Cold costs nothing: `identityHeld` is `[ ]` without touching either config.
        config = builtins.seq result.identityHeld result.config;
        options =
          let
            entries = prelude.imap0 declEntry result._flat;
          in
          moduleOwn.serve prefix result.optionDefs.moduleOwn (
            serveOptions (declaringSitesAt (length prefix) entries) [ ] prefix result.provenance
              result.optionDefs.defs
              (builtins.seq result.identityHeld result.optionDefs.values)
              result.options
          );
        inherit (result)
          provenance
          # The unmatched definitions this eval did not merge into `config`, the REFUSED ones included —
          # `check` does not gate it (see above) — empty whenever a freeformType absorbed them, and empty
          # for a fully-declared config.
          undeclared
          # The declared options of this eval whose TYPE carries a `deprecationMessage`, each with the
          # message, the type's name and the files that declared the option — empty when no declared
          # type is deprecated, which is the ordinary case.
          deprecations
          # Freeform layers exposed as internal memo fields (public surface = the five above):
          # a CHAINED warm re-eval reuses `warmFrom.freeformConfig`/`freeformProv` directly (spec §2).
          freeformConfig
          freeformProv
          optionDefs
          # The memoization decision trace (spec §4); `mode = "cold"` on a plain compose (no warmFrom).
          warmDecision
          ;
        # The tree AS a type — lets a parent tree nest this one (submodule recursion / freeform). Nested
        # evals are always COLD (no `warmFrom` threaded) — a documented boundary, like provenance's.
        #
        # ── AN OPTION TYPE, BUILT AT THE CROSSING SITE (den-hoag-foreign-mount-parity-knhyg) ─────────
        # The value is a type of the vocabulary's own kind, built by `strategies.defineType` exactly as
        # `submodule` is (`lib/types.nix` `mkSubmodule`): a fold, a domain, a carried module set and its
        # rebuild, a relation, and the substructure triple. `defineType` is the one crossing site, so
        # the type answers the whole foreign protocol by derivation (`lib/interface.nix` `exportType`),
        # and a real `lib.evalModules` mounts it: bare, inside every member-taking combinator, and in
        # its docs.
        #
        #   * THE NAME IS `submodule`, nixpkgs' name for a type whose definitions are modules: nixpkgs
        #     merges raw sub-option declarations into an option whose type is named `submodule`
        #     (`mergeModules'`), and its container phrases and refusals name it so. The name carries
        #     nixpkgs' `submoduleWith` payload with it (`exportType`, role `moduleSet`), whose
        #     `shorthandOnlyDefinesConfig` is `false` here: every definition is read as a module, as
        #     the reference `(evalModules …).type` reads it. `submodule` states `true`, and each
        #     relation refuses the other's datum by name, as nixpkgs refuses two such declarations.
        #   * THE RELATION unions in authored order (`pm ++ modList`), as nixpkgs' `binOp` does, and
        #     merges `specialArgs` by `//`, refusing a key both state.
        #   * THE FREEFORM DATUM is this evaluation's resolved freeform type, `unroledNested`, derived
        #     from the published closure (`_flat`) by the body's own functions when the type is read,
        #     never carried as a field of every evaluation result.
        #   * `getSubOptions` is the tree's declarations under the foreign prefix, a standalone
        #     evaluation (`evalModuleTreeUnchecked`), as nixpkgs' `extendModules { prefix }` is, so it
        #     evaluates its own nested trees, whose records are the evaluated ones (`serveOptions`).
        type =
          let
            # ONE fold value, whose two evaluating forms READ the tree rather than evaluate it
            # (den-hoag-n6dh7 items 1, 4, 5). The tree is a child of the one evaluation that holds it,
            # and `threaded` / `threadedReported` read it through that evaluation's accessor: the site
            # names this tree's `nests`, the fold's `loc` and its `defs`. `threaded` is the STRICT fold,
            # for every site that carries no undeclared report (a container element, a freeform plane):
            # a finding in the child is refused by name when this value is read, as nixpkgs refuses per
            # level. `threadedReported` is the one reporting caller's (the rich realizer fold): the
            # value and the report off ONE read (ADR-0025 item 1). Its child inherits the carrying
            # evaluation's strictness on its position record, so a strict carrier's finding is refused
            # by the tree that owns it. Each refuses a definition outside `admits` before the read
            # (`refusingOutside`). The CALLED forms (`__functor`, `.reported`) refuse by name (item 1).
            strictValue =
              loc: n:
              if n.undeclared == [ ] then
                n.config
              else
                throw (
                  "gen-merge: "
                  + concatStringsSep "; " (
                    map (
                      u:
                      "option `${showOption u.path}' is not declared by the nested tree that owns it (defined in ${u.file})"
                    ) n.undeclared
                  )
                  + "; "
                  + (if loc == [ ] then "the tree" else "the tree at `${showOption loc}'")
                  + " is merged where no undeclared report is carried"
                );
            site = ev: loc: defs: {
              inherit (ev) position;
              inherit nests loc defs;
            };
            nestingFold = {
              __functor =
                _: loc: _:
                throw (calledNestingRefusal "submodule" "mergeDefs" loc);
              reported =
                _: loc: _:
                throw (calledNestingRefusal "submodule" "mergeDefs.reported" loc);
              threaded =
                ev:
                refusingOutside "submodule" isModuleValue (
                  loc: defs: strictValue loc (ev.child (site ev loc defs))
                );
              # `strict` is the child's `mode.inherited` by construction (both are the carrying
              # evaluation's strictness); it is kept so the signature stays `.reported`'s.
              threadedReported =
                ev: _strict:
                refusingOutside "submodule" isModuleValue (
                  loc: defs:
                  let
                    n = ev.child (site ev loc defs);
                  in
                  {
                    value = n.config;
                    inherit (n) undeclared;
                  }
                );
            };
            # The nested tree AS DATA (den-hoag-n6dh7 item 1): what its child evaluates, field for
            # field: `entry` is one definition read as `defsAsModules false` reads it (every definition
            # is a module, as the reference `(evalModules …).type` reads it), `empty` is the arguments
            # of the fold over no definitions, `calledMode` is the pair a called site's child runs in,
            nests = {
              modules = modList;
              inherit specialArgs check coreShortCircuit;
              entry = d: head (defsAsModules false [ d ]);
              empty = {
                prefix = [ ];
                inherit specialArgs check;
              };
              calledMode = {
                carried = false;
                inherited = false;
              };
            };
            # The fold over no definitions, CALLED, refuses (item 1): an undefined tree is the child
            # with an empty seed, which the threaded fold reads (`threadedAs`).
            emptyTree.value = throw (calledNestingRefusal "submodule" "whenEmpty" null);
          in
          let
            over =
              ms:
              (evalModuleTreeUnchecked {
                modules = ms;
                inherit specialArgs check coreShortCircuit;
              }).type;
            freeform = resolvedFreeform (
              map topFreeformEntry (filter hasTopFreeform result._flat)
              ++ concatMap moduleFreeformEntries (map pushedEntry result._flat)
            );
          in
          strategies.defineType {
            name = "submodule";
            mergeDefs = nestingFold;
            whenEmpty = emptyTree;
            admits = isModuleValue;
            shorthandOnlyDefinesConfig = false;
            inherit nests specialArgs;
            unroledNested = if freeform == null then { } else { freeformType = freeform; };
            carries.moduleSet = modList;
            recarry = c: over c.moduleSet;
            typeMergeRel =
              other:
              let
                pm = interface.importedOffered "moduleSet" other;
                partnerArgs = other.specialArgs or { };
              in
              if (other.name or null) != "submodule" then
                { refused = "`submodule' and `${interface.nameOf other}'"; }
              else if pm == null then
                let
                  joined = interface.joinInStatedRelation {
                    name = "submodule";
                    payload = interface.moduleSetPayload {
                      modules = modList;
                      inherit specialArgs;
                      shorthandOnlyDefinesConfig = false;
                    };
                  } other;
                in
                if joined == null then
                  {
                    refused = "`submodule' and a partner whose module set is stated beside parameters this one does not carry, under no relation of its own";
                  }
                else
                  { merged = joined; }
              # The one datum two `submodule' declarations must agree on beside the name, and the
              # reason names it, since the names agree.
              else if (other.shorthandOnlyDefinesConfig or null) != false then
                {
                  refused = "`submodule' reading every definition as a module, and a `submodule' reading an attribute-set definition as config";
                }
              else if builtins.intersectAttrs specialArgs partnerArgs != { } then
                { refused = "two `submodule' declarations stating the same specialArgs"; }
              else
                {
                  merged =
                    (evalModuleTreeUnchecked {
                      modules = pm ++ modList;
                      specialArgs = specialArgs // partnerArgs;
                      inherit check coreShortCircuit;
                    }).type;
                };
            substructure = {
              modules = modList;
              declares =
                prefix:
                (evalModuleTreeUnchecked {
                  modules = modList ++ [ namePlaceholder ];
                  inherit prefix specialArgs check;
                }).options;
              rebuild = over;
            };
          };
      }
      // (if knot.exposes then { inherit (result) _evaluation; } else { });
  # The published door's engine: a ROOT evaluation, which mints its nested positions.
  evalModuleTreeUnchecked = evalModuleTreeWith knotRoot true false;
  # The same, with the gen-scope evaluation on the result as `_evaluation` (this library's suites).
  evalModuleTreeExposed = evalModuleTreeWith knotExposed true false;
  # A NESTED evaluation, made by a nesting type's called fold (`lib/types.nix` `submodule`): it
  # mints nothing, because its tree is a position of the evaluation that holds it.
  evalModuleTreeNested = evalModuleTreeWith knotNested true false;

  # The published door is OPTIONS FIRST, `modules` LAST (den-hoag-7gp66 P2, R7): the closed options
  # set is a `prelude.door`, refused by name and catchably at `evalModuleTree opts`'s own WHNF, so
  # `evalModuleTree { specialArgs = …; }` is a value a caller can map over module lists. The module
  # list is the subject, a positional operand with no field contract. The `{ }` options call takes
  # the constructor's fast path and runs no check. The nesting seam and every internal caller call
  # `evalModuleTreeUnchecked` (or `evalModuleTreeWith`) with a record built here, not a caller's.
  evalModuleTreeOptions = [
    "specialArgs"
    "check"
    "prefix"
    "coreShortCircuit"
    "warmFrom"
    "editedModules"
  ];
  evalModuleTree = prelude.door {
    name = "gen-merge.evalModuleTree";
    optional = evalModuleTreeOptions;
  } (o: modules: evalModuleTreeUnchecked (o // { inherit modules; }));
in
{
  inherit
    evalModuleTree
    # The engine behind the door (a root evaluation), and the nested evaluation a nesting type's
    # called fold makes (lib/types.nix): each builds its record literally, so the door's caller check
    # has nothing to decide. Not published.
    evalModuleTreeUnchecked
    evalModuleTreeNested
    evalModuleTreeExposed
    # Stratum 1 on its own — the declaration fold, published so a consumer wanting declarations
    # without values drives no fixpoint at all. Public (see lib/default.nix); it is also the fold
    # `evalModuleTree`'s declaration GUARD runs, so the two can never answer differently about
    # which options a module set declares.
    declaredOptions
    mergeDefs
    mergeDefsPartial
    mergeOption
    mergeOneOption
    # This engine's own no-`.merge` default — one winner passes, equal winners collapse, unequal
    # winners are refused by option path. Exported for the same reason `mergeTypes` is: a type in
    # lib/types.nix asks the identical question at the identical stratum (`anything`'s
    # non-structural arm, where a "merge" of two scalars degenerates to agree-or-refuse), and one
    # binding is what keeps the vocabulary's answer and the engine's from drifting apart. Internal
    # seam only — the public `lib/default.nix` surface is unchanged.
    mergeLeaf
    # The shared-key "differ" notion, exported for the same reason: `unionAgreeing`'s shared keys
    # and the `withArgs` relation's base arguments (lib/types.nix `mkSubmodule`) ask one question,
    # and one binding keeps the two answers from drifting apart.
    slotsDiffer
    # The per-key union both attrset folds return: `mergeDescriptorDefault` here and the `attrs`
    # type (lib/types.nix). They differ only in the refusal text, which each passes in.
    unionAgreeing
    isDefinedValue
    isDefinedBy
    # The shape-directed default-merge law (nixpkgs `lib.mergeDefaultOption` parity) — a surface
    # BESIDE `mergeLeaf`, which stays this engine's own no-`.merge` default. See the public export
    # in lib/default.nix.
    mergeDefaultOption
    # `types.unspecified`'s fold and `types.optionType`'s (lib/types.nix), the engine's own untyped
    # fold and freeform-type merge, so a served record's type folds as the engine does.
    mergeUntyped
    mergeTypeDefs
    showOption
    setDefaultModuleLocation
    defsAsModules
    # The module question's fourth shape, read by `isModuleValue` and the lint's `collect` as well
    # as the loader, so the admission predicate cannot fall behind what `callM` imports.
    isPathString
    # The module-value domain and the structural fold's domain guard, read by `./types.nix`'s
    # module-valued types and by the tree's own `type`, so the two files state one domain.
    isModuleValue
    refusingOutside
    # The walk's spelling of the door's quantifier, read by the agreement cell beside the door.
    admitsAll
    mkCoreValue
    # `pureModule` (design spec §3 / §5) — the author's clean-module assertion; wraps a function module
    # in the `{ __pureModule = true; __functor = …; }` shape `classifyModule` reads pre-application.
    pureModule
    # Classification/collection predicates shared with the portable-subset lint (lib/lint.nix) so the
    # lint's view of "declared leaf vs group / config-shorthand / imports / decl-tree merge" cannot
    # DRIFT from the engine's. This group is EXACTLY what the lint consumes, and none of it is on the
    # public `lib/default.nix` surface.
    isOptLeaf
    # The module-classification key lists themselves (den-hoag-1n12c) — published on `core` so the
    # public `moduleSyntax` record (lib/default.nix) can be built from the SAME bindings `configOf`
    # enforces with, never a second spelling of them.
    structuringKeys
    moduleDefOf
    structuredKeys
    shorthandMetaKeys
    functorRecordKeys
    configOf
    moduleSyntaxChecked
    notAModule
    importsOf
    mergeOptionDecls
    # The guarded pair-merge of two TYPES. It lives here rather than in lib/types.nix because the
    # DECLARATION stratum asks the same question as the ELEMENT stratum, and one binding is what
    # keeps their answers identical; lib/types.nix consumes it back through this seam.
    mergeTypes
    # The same relation answering with its REASON — for a caller that reports rather than dispatches.
    mergeTypesReason
    # Their descent past the pre-flight, for a relation's own recursion (`lib/types.nix`
    # `mergeElemTypes`): an operand there is a sub-tree of one the entry already walked.
    mergeTypesWithin
    mergeTypesReasonWithin
    # A nested tree's position record and the report mode its child evaluates in (den-hoag-n6dh7),
    # on the internal seam for the key walk that mints the children.
    nestedPosition
    positionChildMode
    # The nested tree's door and the engine's threaded twin (den-hoag-n6dh7 items 4, 5, 7): the
    # containers in `./types.nix` fold each element through the twin, and the suites read the door.
    nestedTreeAt
    mergeDefsThreaded
    mergeDefsThreadedPartial
    readsMintedNode
    calledNestingRefusal
    namePlaceholder
    # The nixpkgs `optionType` PROTOCOL BOUNDARY (lib/interface.nix), reached through this seam by
    # everything above it — the type vocabulary exports through it, this engine reads foreign types
    # through it, and the public surface stamps through it. ONE binding, so the library cannot hold
    # two views of what the foreign protocol says.
    interface
    # `classifyModule` (design spec §3) — the source-class predicate threaded onto every collected
    # entry as `srcClass`; shared with the warm re-eval path and the classify suite.
    classifyModule
    # Warm re-eval decision layer (design spec §§1-2) — `moduleClosure` (the merge path's module
    # collection; the warm path partitions it by origin over the identity-keyed closure) + the pure `warmDecide` predicate and its footprint
    # helpers, and `moduleKeyOf`, the identity rule the lint shares. On the internal core seam only;
    # the splice EXECUTION rides `evalModuleTree`.
    moduleClosure
    moduleKeyOf
    # the graph-read path's node-by-node agreement check, for its own cell (`module-graph.nix`)
    alignedGraph
    warmDecide
    declLeafPaths
    moduleDefFootprint
    ;
}
