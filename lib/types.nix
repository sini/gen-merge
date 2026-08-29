# Structural merge-strategy types (spec §2 + §4).
#
# These are the MERGE half — the types that own how their defs combine. Each carries a `.mergeDefs
# loc defs`. Leaf CHECKING types (str/int/bool/enum/path/…) come from gen-types (injected), NOT here
# — gen-merge answers "how do defs combine?", gen-types answers "is v well-typed?" (spec §4). `raw`
# and `anything` live here because they are defined by their MERGE behavior (one-def / recursive),
# not by a value predicate.
#
# ★★★ THE VOCABULARY UTTERS NO FOREIGN CONSTANT. What a type says about itself it says in gen's own
# words — `verify`/`admits` for its domain, `mergeDefs` for its fold, `typeMergeRel` for whether two
# of them merge, `carries`/`recarry` for what it wraps, `substructure` for what it declares,
# `whenEmpty` for what it is worth when nobody defined it. The nixpkgs `optionType` protocol — its
# fourteen field names, its payload spellings, its `option-type` tag — lives in ONE unit,
# `lib/interface.nix`, and a type acquires it only by being exported through that boundary. A foreign
# name appearing in this file is the boundary leaking, and `ci/tests/interface.nix` is what says so.
{
  prelude,
  core,
}:
let
  inherit (prelude)
    isList
    isAttrs
    isFunction
    concatMap
    concatLists
    concatStringsSep
    map
    attrNames
    elemAt
    listToAttrs
    foldl'
    optional
    filter
    head
    tail
    length
    all
    imap0
    ;
  inherit (core)
    evalModuleTree
    mergeDefs
    mergeLeaf
    showOption
    setDefaultModuleLocation
    interface
    ;

  # mkOption — a plain descriptor; evalModuleTree reads .type/.default/.apply/.readOnly. Identity
  # (tagged) so the gen-aspects/gen-schema re-host is a `lib.mkOption` → `mkOption` rename.
  mkOption = descriptor: descriptor // { _type = "option"; };

  # ── the gen-native type constructor ─────────────────────────────────────────────────────────────
  # A gen type IS its record. `mkType` adds the one thing every type owes and most do not state — a
  # TYPE-MERGE RELATION — and enforces the one thing a wrapping type may not inherit.
  #
  # THE DEFAULT RELATION IS THE NULLARY ONE: a type with no parameters merges with a same-named
  # partner and refuses everything else. That is right for a type that takes no parameters and WRONG
  # for one that does — two `attrsOf` over different element types would report "mergeable" and
  # silently keep the first — so every parameterised constructor below states its own.
  #
  # ── the sub-protocol is a REQUIRED FORMAL of a wrapping type, not a default ─────────────────────
  # A leaf's answers are that it declares nothing, has NO module-set concept (which is what `null`
  # says, and the only thing it says — a module set that exists and is empty reports `[ ]`), and has
  # nothing to rebuild. They are wrong for every type that wraps another, and a wrapping type left on
  # them reports "declares nothing" indistinguishably from a type that genuinely declares nothing — a
  # consumer reflecting a declared surface off it then fails CLOSED and silently. A default cannot be
  # right for both, so a type that CARRIES something answers all three itself or is refused here, by
  # name. The missing declaration is the design choice; making the field required makes it total.
  #
  # THE DOMAIN IS WHAT THE TYPE CARRIES — a property of the constructor, read off the record, not of
  # any measurement. Two ways a record says it carries something: a `carries` role (an element type,
  # a union's members, a module set) or a substructure that names a module set. Everything else is
  # outside BY THE DOMAIN rather than by a carve-out:
  #   · a leaf carries neither;
  #   · `either`/`oneOf` carry MEMBERS, and they introduce no path level, so `{ }` is their correct
  #     `declares` answer — which they state, rather than inherit;
  #   · `deferredModule` carries a module set, and that set is EMPTY. gen-merge ships no
  #     `deferredModuleWith`/`staticModules`, so it is empty BY CONSTRUCTION rather than by
  #     omission — a fact to report (`[ ]`), not an absence (`null`). It is therefore IN this domain
  #     by the module-set arm and answers all three itself, below.
  #
  # `||` short-circuits, and the order is load-bearing: a container's module set IS its element's, so
  # reading it to decide the domain would force the element type at construction. A `carries` role is
  # settled before that read happens.
  subFormals = [
    "declares"
    "modules"
    "rebuild"
  ];

  # A partner's name, for a refusal — total over anything that can arrive as a merge operand.
  #
  # ★ A REFUSAL'S REASON IS A NOUN PHRASE NAMING THE PAIR, never a sentence repeating the verdict.
  # The relation's reason is read back at the declaration site, which has already said "declared with
  # types that do not merge" before it opens the parenthesis; a reason that says so again produces
  # `types that do not merge (types do not merge: …)`. So every refusal below names the two operands
  # and, where there is one, the DISCRIMINATING FACT — which is the part the reader does not already
  # have from the sentence around it.
  nameOf = other: if isAttrs other then other.name or "<unnamed>" else "<not a type>";
  # `self` is what this type's own default relation answers WITH — the value a caller actually holds.
  # It is threaded rather than closed over locally because a type built through `defineType` is used
  # in its EXPORTED form, and a relation answering with the un-exported twin would hand a consumer a
  # merged type its foreign engine cannot read. One knot, tied where the two forms are made.
  mkTypeWith =
    self: t:
    let
      name = t.name or "raw";
      declaresRole = t ? carries;
      carriesSomething = declaresRole || ((t.substructure or { }).modules or null) != null;
      missingSub = filter (f: !((t.substructure or { }) ? ${f})) subFormals;
      # ★ `recarry` IS OWED BY A TYPE THAT DECLARES A ROLE, and it is the last carried-role formal that
      # was left un-total. The boundary reads it UNCONDITIONALLY to rebuild this type over another
      # payload, so a carrying record without it constructs, exports, and then detonates with a bare
      # missing-attribute error the moment a foreign engine applies the functor — an interpreter error
      # naming neither the type nor the field, which is the exact shape making every other formal here
      # required was meant to remove.
      #
      # SCOPED TO THE ROLE, not to carrying in general: `deferredModule` carries a module set through
      # its substructure without declaring a role, so it has no payload to be rebuilt over and owes
      # none. The domain is what the record SAYS it carries, as everywhere else in this check.
      missingRecarry = if declaresRole && !(t ? recarry) then [ "recarry" ] else [ ];
      missing = missingSub ++ missingRecarry;
      nullaryRel =
        other:
        if isAttrs other && (other.name or null) == name then
          { merged = self; }
        else
          { refused = "`${name}' and `${nameOf other}'"; };
    in
    if carriesSomething && missing != [ ] then
      throw (
        "gen-merge: the structural type `${name}' carries a parameter but does not supply "
        + concatStringsSep ", " (map (f: "`${f}'") missing)
        + "; a type that carries something answers for it rather than inheriting a leaf's answers"
      )
    else
      t // { typeMergeRel = t.typeMergeRel or nullaryRel; };

  # The gen record alone, answering with itself. This is the substrate vocabulary with nothing of the
  # foreign protocol on it, and it is what the boundary is handed.
  mkType =
    t:
    let
      self = mkTypeWith self t;
    in
    self;

  # defineType — the gen record AND its expression in the foreign protocol, as one value.
  #
  # ★ THIS IS THE CROSSING SITE, AND THERE IS ONE OF IT. Every type this library constructs is built
  # here, so "which values carry the foreign protocol, and where did they acquire it" has a
  # one-line answer instead of a survey. THAT THE SAME VALUE CARRIES BOTH IS FORCED, not convenient:
  # the published `types` namespace is the drop-in a foreign module system mounts, and the type a
  # consumer writes there is handed to this library's own fold as readily as to a foreign one. What
  # the boundary buys is not that the two vocabularies live in different values — it is that only ONE
  # unit knows how to get from the first to the second, and that everything above states itself in
  # the first alone.
  defineType =
    t:
    let
      exported = interface.exportType (mkTypeWith exported t);
    in
    exported;

  # mkOptionType — the (loc,defs) custom-merge escape hatch (spec §1 item 6). Its descriptor is
  # written in the FOREIGN protocol's words (`check`, `merge`, `emptyValue`, …) because that is what
  # a nixpkgs `mkOptionType` drop-in means, so it is exactly a round trip through the boundary: the
  # descriptor comes IN through the import environment, acquires the relation every gen type owes,
  # and goes back OUT through the export environment. Consumers write
  # `mkOptionType { name = "aspect"; merge = loc: defs: …; }` and get a type that both gen-merge
  # (dispatches on `.mergeDefs`) and nixpkgs (reads the full protocol) accept.
  mkOptionType =
    descriptor:
    let
      answer = interface.importType descriptor;
    in
    if answer ? refused then throw answer.refused else defineType answer.imported;

  # Merge two ELEMENT types — the element stratum's name for `core.mergeTypes` (lib/modules.nix),
  # which is guarded on both halves and stated there. It is the SAME binding the DECLARATION stratum
  # consults when one option is declared twice, which is what makes "these two types do not merge"
  # one answer in this library rather than two that can drift apart.
  mergeElemTypes = core.mergeTypes;

  # A CONTAINER'S RELATION, shared by every type parameterised by one element. Two containers merge
  # iff their elements merge, and the result is this container rebuilt over the merged element.
  #
  # ★ ROW-FREE, AND THAT IS WHAT MAKES IT GEN'S OWN. The partner arrives as a TYPE, not as a functor
  # payload both sides must agree on the shape of, so a partner that spells its parameter some other
  # way is still a legible operand — its element is read through the boundary's import environment,
  # which is the one place that knows any spelling but this one.
  elementRel =
    name: rebuild: element: other:
    if !(isAttrs other) || (other.name or null) != name then
      { refused = "`${name}' and `${nameOf other}'"; }
    else
      let
        partnerElem = interface.importedCarried "element" other;
      in
      if partnerElem == null then
        { refused = "`${name}' and a partner that states no element type of its own"; }
      else
        let
          merged = mergeElemTypes element partnerElem;
        in
        if merged == null then
          {
            refused = "`${name}' over `${nameOf element}' and `${name}' over `${nameOf partnerElem}', whose element types do not merge";
          }
        else
          { merged = rebuild merged; };

  # An element's substructure, whichever vocabulary it speaks. A gen type answers from its own
  # record; a foreign one is read through the import environment; a bare parametric constructor (a
  # gen-types `enum`/`struct`/`union` reaching the namespace unapplied) is not a record at all and
  # gets a leaf's answers, which are the true ones for it.
  subOf = element: interface.importedSubstructure element;
  # Whether an element has a substructure of its own to substitute into — asked at the boundary,
  # because the answer depends on which vocabulary the element states it in.
  carriesSub = interface.importedRebuilds;

  # Turn a def value into a module (located) for a nested evalModuleTree.
  defToModule = d: setDefaultModuleLocation (toString (d.file or "<def>")) d.value;

  # submodule — recurse into a nested evalModuleTree over the submodule module + all defs; binds the
  # per-key `name` (spec §1 item 3). One nested fixpoint per merge (spec §1 item 4).
  submodule =
    modOrMods:
    let
      mods = if isList modOrMods then modOrMods else [ modOrMods ];
    in
    defineType {
      name = "submodule";
      # A submodule's definitions ARE modules: `mergeDefs` hands each through `defToModule` to a
      # nested `evalModuleTree`, so the domain is `isModuleValue`'s and not "any value". nixpkgs
      # reaches the same three shapes through its `path` check, which additionally admits a string
      # beginning with `/`; the same deliberate narrowing as `deferredModule` below, and for the same
      # reason.
      admits = isModuleValue;
      # A CONTAINER nobody added to is legitimately empty; only a type that declares no empty value
      # is an error when undefined.
      whenEmpty.value = { };
      # What this type is parameterised BY. A submodule carries a MODULE SET, which is why its
      # relation unions rather than merges: an option declared as a submodule in two modules ends up
      # declaring the union of what they declare. On a nullary relation the second declaration would
      # be discarded silently.
      carries.moduleSet = mods;
      recarry = c: submodule c.moduleSet;
      typeMergeRel =
        other:
        if !(isAttrs other) || (other.name or null) != "submodule" then
          { refused = "`submodule' and `${nameOf other}'"; }
        else
          let
            partnerMods = interface.importedCarried "moduleSet" other;
          in
          if partnerMods == null then
            {
              refused = "`submodule' and a partner whose module set is stated beside parameters this one does not carry";
            }
          else
            { merged = submodule (mods ++ partnerMods); };
      substructure = {
        # What a consumer learns from this type with NO value in hand, the twin of `mergeDefs`:
        #   declares = prefix: (evalModuleTree { inherit modules prefix; }).options
        # Reads `.options` off the same nested fixpoint the fold builds, with no defs supplied, so
        # the two halves cannot disagree about what a submodule declares and no instance-authored
        # value is forced.
        declares =
          prefix:
          (evalModuleTree {
            modules = mods;
            inherit prefix;
            specialArgs = {
              name = if prefix == [ ] then "" else prelude.last prefix;
            };
            check = true;
          }).options;
        modules = mods;
        # Rebuild this type over the module set a consumer supplies. REPLACES `mods` — it does NOT
        # append: a foreign module system builds the replacement as this type's OWN modules
        # (relocated) plus any sibling declarations, so concatenating would re-include `mods` a
        # second time, double-evaluating the base module (a readOnly config value — e.g.
        # gen-schema's `den.schema._kindNames` — then throws "defined 2 times").
        rebuild = m: submodule (if isList m then m else [ m ]);
      };
      mergeDefs =
        loc: defs:
        (evalModuleTree {
          modules = mods ++ map defToModule defs;
          prefix = loc;
          specialArgs = {
            name = if loc == [ ] then "" else prelude.last loc;
          };
          check = true;
        }).config;
    };

  # listOf — concat all list defs in order (byte-mode drops the order pass; spec §7), each element
  # merged through the element type (a submodule element becomes an instance; a leaf is verified).
  listOf =
    element:
    defineType {
      name = "listOf";
      # `mergeDefs` walks each definition with `imap0`, so a definition that is not a list is one
      # this type cannot consume — the domain, stated where the type is built.
      admits = isList;
      whenEmpty.value = [ ];
      carries.element = element;
      recarry = c: listOf c.element;
      typeMergeRel = elementRel "listOf" listOf element;
      substructure = {
        # Descend to the element type under the positional placeholder segment.
        declares = prefix: (subOf element).declares (prefix ++ [ "*" ]);
        # A container's module set IS its element's, and substituting one rebuilds the container over
        # the substituted element.
        modules = (subOf element).modules;
        rebuild = m: listOf (if carriesSub element then (subOf element).rebuild m else element);
      };
      mergeDefs =
        loc: defs:
        concatMap (
          d:
          imap0 (
            i: v:
            mergeDefs (loc ++ [ (toString i) ]) element [
              {
                inherit (d) file;
                value = v;
              }
            ]
          ) d.value
        ) defs;
    };

  # attrsOf / lazyAttrsOf — per-key merge through the element type. Byte-mode output is identical
  # for both (Nix values are already lazy — spec §1 item 2); kept as distinct names for the surface.
  attrsOfWith =
    tyName: element:
    defineType {
      name = tyName;
      # `mergeDefs` takes the key union across the definitions and indexes each by key, so a
      # definition that is not an attrset is one this type cannot consume.
      admits = isAttrs;
      whenEmpty.value = { };
      carries.element = element;
      recarry = c: attrsOfWith tyName c.element;
      # gen-merge keeps `attrsOf`/`lazyAttrsOf` as distinct type NAMES where nixpkgs unifies both
      # under one constructor discriminated by a payload field. Distinct names are the conservative
      # direction: the two never merge with each other, and neither merges with the unified foreign
      # one. The rebuild keeps THIS container's name, so the distinction survives substitution.
      typeMergeRel = elementRel tyName (attrsOfWith tyName) element;
      substructure = {
        # Descend to the element under the per-key placeholder segment, so an `attrsOf (submodule …)`
        # registry exposes its INSTANCE option surface to an introspecting consumer.
        declares = prefix: (subOf element).declares (prefix ++ [ "<name>" ]);
        modules = (subOf element).modules;
        rebuild = m: attrsOfWith tyName (if carriesSub element then (subOf element).rebuild m else element);
      };
      mergeDefs =
        loc: defs:
        let
          # key union via attrset fold — a list `unique` is O(k²) in key count
          keys = attrNames (foldl' (acc: d: acc // d.value) { } defs);
        in
        listToAttrs (
          map (k: {
            name = k;
            value = mergeDefs (loc ++ [ k ]) element (
              concatMap (
                d:
                optional (d.value ? ${k}) {
                  inherit (d) file;
                  value = d.value.${k};
                }
              ) defs
            );
          }) keys
        );
    };
  attrsOf = attrsOfWith "attrsOf";
  lazyAttrsOf = attrsOfWith "lazyAttrsOf";

  # deferredModule (spec §1 item 7) — collect defs into ONE module (via imports), located; NEVER
  # forced by the composition plane. Output is a plain, import-usable module value (nixpkgs-faithful:
  # a deferred module's fold produces `{ imports = [ … ]; }`), handed opaque to the terminal.
  deferredModule = defineType {
    name = "deferredModule";
    # A type carrying no domain at all accepts every definition, which is right only for a type whose
    # fold really does accept any value. This one's does not: `mergeDefs` wraps each def into an
    # `imports` list, and the engine's `callM` (lib/modules.nix) can apply only a path, a function, a
    # `__functor` attrset, or a plain attrset. Any other value is carried into `imports` unexamined
    # and handed to whoever imports it, so the definition is accepted HERE and fails somewhere else —
    # with no option path and no definition file. A check that cannot fail is not a check.
    #
    # STRICTER than nixpkgs on one shape, deliberately: nixpkgs reuses its `path` predicate, which
    # also admits a STRING beginning with `/`. `callM` dispatches on `builtins.isPath`, so such a
    # string would pass through as a module VALUE — admitting it here would re-create the exact
    # silent acceptance this domain exists to close.
    admits = isModuleValue;
    # ── the module set is EMPTY, and empty is not absent ─────────────────────────────────────────
    # `null` and `[ ]` are two different facts, and a single `null` cannot carry both: `null` says
    # "this type has no sub-module concept at all" (a leaf's answer), `[ ]` says "this type has a
    # module set and there is nothing in it". Reported as `null`, this type's "has nothing to
    # declare" was indistinguishable from a leaf's "declares nothing" — the missing distinction is
    # the design choice, so the encoding states it. gen-merge ships no
    # `deferredModuleWith`/`staticModules`, which is exactly WHY the set is empty by construction
    # rather than by omission, and why reporting it is a statement of fact and not a stub.
    #
    # The three answers are stated together because a consumer reads them together: a foreign module
    # system branches on whether the module set is null and, on every other type, REPLACES the
    # option's type with the rebuild. So a non-null module set with a leaf's null rebuild would hand
    # every mounted option a null type — the encoding and the rebuild are one decision, not two.
    substructure = {
      declares = _prefix: { };
      modules = [ ];
      # Rebuilding over the empty set is this same type. Over a NON-EMPTY one there is nothing to
      # build: without a static-module parameter the modules could only be dropped, and a rebuild
      # that silently discards what it was handed is the wrong value with no diagnostic. Refuse by
      # name instead.
      rebuild =
        m:
        if m == [ ] then
          deferredModule
        else
          throw (
            "gen-merge: `deferredModule' cannot be rebuilt over a module set of "
            + toString (length m)
            + "; it carries no static modules and dropping them would lose the declarations silently"
          );
    };
    mergeDefs = loc: defs: {
      imports = map (
        d: setDefaultModuleLocation "${toString (d.file or "<def>")}, via option ${showOption loc}" d.value
      ) defs;
    };
  };

  # The module-value domain, shared by the two types whose definitions ARE modules (`submodule`,
  # `deferredModule`) so the two cannot drift into answering it differently. The engine's `callM`
  # applies a path, a function, a `__functor` attrset or a plain attrset, and nothing else.
  isModuleValue = v: isAttrs v || isFunction v || builtins.isPath v;

  # Membership predicate for union dispatch. gen-types leaf checkers expose `verify` (v → null|err);
  # gen-merge structural types expose `admits` (v → bool). Prefer `verify` FIRST — a gen-types
  # `check` is curried (not v → bool), so it must never be applied here — and fall through to the
  # import environment for a FOREIGN element, which states its domain in the foreign protocol's
  # words and nowhere else.
  #
  # A STRUCTURAL TYPE OWES ITS OWN ANSWER HERE, and "accepts anything" is not one: it is right for a
  # type whose fold really does accept any value (`raw`, `anything`), and a standing lie for one
  # whose fold does not. Left on it inside a union it is worse than imprecise — the union's domain is
  # a disjunction over its members, so ONE member answering "yes" to everything makes the whole union
  # unable to refuse anything, and the definition the member cannot consume reaches the interpreter
  # instead (`either`, below).
  isValid =
    t: v:
    if t ? verify then
      t.verify v == null
    else if t ? admits then
      t.admits v
    else
      let
        foreign = interface.importedAdmits t;
      in
      if foreign == null then true else foreign v;

  # nullOr / option — a MERGE-aware nullable (NOT a gen-types verify-only `option`, which would drop
  # a wrapped merge-type's behaviour, e.g. a ref field's coercion). null defs drop; non-null defs
  # merge through the element type (leaf verify or ref/submodule merge, via mergeDefs).
  nullOr =
    element:
    defineType {
      name = "nullOr";
      # A nullable option nobody defined IS null. Distinct from the containers only in which empty
      # value it names.
      whenEmpty.value = null;
      carries.element = element;
      recarry = c: nullOr c.element;
      typeMergeRel = elementRel "nullOr" nullOr element;
      substructure = {
        # Pass straight through to the element, adding NO path segment. A nullable introduces no path
        # level — `nullOr (submodule …)` declares exactly what the submodule declares, at the same
        # location — which is why this differs from `attrsOf`'s `<name>` and `listOf`'s `*`.
        declares = (subOf element).declares;
        # A nullable declares exactly what its element declares, so it carries exactly its element's
        # module set too.
        modules = (subOf element).modules;
        rebuild = m: nullOr (if carriesSub element then (subOf element).rebuild m else element);
      };
      admits = v: v == null || isValid element v;
      mergeDefs =
        loc: defs:
        let
          nonNull = filter (d: d.value != null) defs;
        in
        if nonNull == [ ] then null else mergeDefs loc element nonNull;
    };
  option = nullOr;

  # either A B — recursion-safe lazy union: merge through the member that accepts EVERY definition,
  # or refuse by name (byte-mode best-effort; the surface's only use is aspectOrFn where A's domain
  # is total).
  either =
    a: b:
    defineType {
      name = "either";
      # The members are carried POSITIONALLY, not as a set — `either str int` and `either int str`
      # are distinct types, and two `either`s merge iff both members merge pairwise.
      carries.alternatives = [
        a
        b
      ];
      recarry = c: either (head c.alternatives) (elemAt c.alternatives 1);
      typeMergeRel =
        other:
        if !(isAttrs other) || (other.name or null) != "either" then
          { refused = "`either' and `${nameOf other}'"; }
        else
          let
            alts = interface.importedCarried "alternatives" other;
          in
          if alts == null || !(isList alts) || length alts != 2 then
            { refused = "`either' and a partner that states no member pair"; }
          else
            let
              left = mergeElemTypes a (head alts);
              right = mergeElemTypes b (elemAt alts 1);
            in
            if left == null || right == null then
              { refused = "`either' and `either', whose members do not merge pairwise"; }
            else
              { merged = either left right; };
      substructure = {
        # A union's members introduce no path level, so it declares nothing of its own — stated
        # rather than inherited, because the pair lives in `carries` and this does not read it.
        declares = _prefix: { };
        modules = null;
        rebuild = _m: null;
      };
      admits = v: isValid a v || isValid b v;
      # A UNION'S FOLD IS TOTAL: every definition is merged through a member that accepts it, or the
      # merge refuses by name. Choosing the member from the FIRST definition's shape and then merging
      # ALL of them through it hands a definition that member cannot consume straight to the
      # interpreter, which answers with a raw type error naming neither the option nor the file that
      # wrote the definition — and that abort escapes `tryEval`, so no caller can turn it into a
      # diagnostic either. The predicate is the members' own, the same one `admits` above is the
      # disjunction of; what is resolved ONCE over the whole definition set, rather than per
      # definition against a member already chosen, is WHICH member — and that leaves no branch that
      # can hand on a definition its member rejects. Nothing is filtered: a set no member takes whole
      # has no merge to perform, and the refusal is the answer. A homogeneous set is unchanged — the
      # member selected from its first definition is the member that accepts them all.
      #
      # THE MEMBERS' ANSWERS ARE THIS RULE'S PRECONDITION, which is why the structural types above
      # state their domains: a member that accepts every definition by default would be picked for a
      # set it cannot merge and the refusal could never fire. A member that genuinely accepts
      # anything (`raw`, `anything`, and a consumer type declaring so on purpose) still does, and is
      # still chosen first.
      mergeDefs =
        loc: defs:
        let
          accepts = t: all (d: isValid t d.value) defs;
          # With no definitions there is nothing to place and nothing to refuse, and the member
          # decides only which empty value the fold goes on to ask for.
          chosen =
            if defs == [ ] then
              b
            else if accepts a then
              a
            else if accepts b then
              b
            else
              null;
          # Per member, the definitions IT could not take. Neither list is empty at the refusal — a
          # member rejecting nothing would have been chosen — and between them they name every
          # definition the author has to reconcile, which is more than the one pair the interpreter
          # would have collided on.
          rejects = t: map (d: toString (d.file or "<def>")) (filter (d: !(isValid t d.value)) defs);
        in
        if chosen == null then
          throw "gen-merge: option `${showOption loc}' has definitions no single `either' member accepts (`${a.name}' rejects ${concatStringsSep ", " (rejects a)}; `${b.name}' rejects ${concatStringsSep ", " (rejects b)})"
        else
          mergeDefs loc chosen defs;
    };

  # oneOf [t1 t2 …] — n-ary either (right-nested). One use on the surface (schema either-chains).
  oneOf =
    ts:
    if ts == [ ] then
      throw "gen-merge: oneOf: empty type list"
    else if length ts == 1 then
      head ts
    else
      either (head ts) (oneOf (tail ts));

  # raw — opaque single value; it brings no fold of its own, so the engine's leaf fold (one winner,
  # or equal winners) is what folds it, and the boundary publishes that same fold outward.
  raw = defineType {
    name = "raw";
  };

  # anything — recursive value merge (lists concat, attrsets per-key recurse, else the ENGINE'S LEAF
  # FOLD). Used by non-strict instance freeform + niche raw-ish spots; byte-mode-adequate, not the
  # full nixpkgs `types.anything` module-composition of function values.
  #
  # ★★★ THE NON-STRUCTURAL ARM IS `mergeLeaf`, NOT A SELECTION. It used to be `prelude.last vals`:
  # two UNEQUAL equal-priority definitions returned one of them and destroyed the other with no
  # diagnostic on any channel, where nixpkgs' `anything.merge` reaches `mergeEqualOption` and THROWS
  # (measured at the pinned rev: `"x"`/`"y"` returns a value here and refuses there). This is the
  # value-plane twin of the freeform selection `den-hoag-5r1a7` removed one file over, and the same
  # argument settles it — except that "merge" DEGENERATES on two scalars: equal ones merge to that
  # value, unequal ones have nothing to merge, so the arm collapses exactly onto `mergeEqualOption`'s
  # own semantics. That relation already lives in this engine as `mergeLeaf` — it is what `raw` folds
  # by, and what every no-`.merge` leaf folds by — so the arm CONSULTS it rather than restating it,
  # and the two neighbouring answers to one question cannot drift apart.
  #
  # `loc` and `file` are therefore threaded through the recursion where the old fold dropped both at
  # the door. A refusal names the FULL path — `mergeLeaf` reports through `showOption loc` — so a
  # conflict under a nested key names that key rather than the option root, which is the same
  # `loc ++ [ k ]` descent nixpkgs' `(attrsOf anything).merge` makes.
  mergeAnythingDefs =
    loc: defs:
    if defs == [ ] then
      throw "gen-merge: anything: no definitions"
    else if all (d: isList d.value) defs then
      concatLists (map (d: d.value) defs)
    else if all (d: isAttrs d.value) defs then
      let
        keys = attrNames (foldl' (acc: d: acc // d.value) { } defs);
      in
      listToAttrs (
        map (k: {
          name = k;
          value = mergeAnythingDefs (loc ++ [ k ]) (
            concatMap (
              d:
              optional (d.value ? ${k}) {
                inherit (d) file;
                value = d.value.${k};
              }
            ) defs
          );
        }) keys
      )
    else
      mergeLeaf loc defs;
  anything = defineType {
    name = "anything";
    mergeDefs = mergeAnythingDefs;
  };
in
{
  inherit
    mkOption
    mkOptionType
    # The two halves of a type's construction, on the internal seam rather than the public surface:
    # `mkType` is the gen record alone (what the boundary is handed, and what a C-2 reading is taken
    # on), `defineType` is that record expressed in the foreign protocol as well (what every
    # constructor above builds, and the library's single crossing site).
    mkType
    defineType
    submodule
    listOf
    attrsOf
    lazyAttrsOf
    deferredModule
    nullOr
    option
    either
    oneOf
    raw
    anything
    ;
}
