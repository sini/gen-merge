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
    isDefinedValue
    isDefinedBy
    showOption
    setDefaultModuleLocation
    defsAsModules
    isPathString
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
      # was left un-total. The boundary reads it to rebuild this type over another payload wherever it
      # DERIVES the relation, so a carrying record without one that is not answered for otherwise
      # constructs, exports, and then detonates with a bare missing-attribute error the moment a
      # foreign engine applies the functor — an interpreter error naming neither the type nor the
      # field, which is the exact shape making every other formal here required was meant to remove.
      #
      # SCOPED TO THE ROLE, not to carrying in general: `deferredModule` carries a module set through
      # its substructure without declaring a role, so it has no payload to be rebuilt over and owes
      # none. The domain is what the record SAYS it carries, as everywhere else in this check.
      #
      # AND SCOPED TO A REBUILD THIS BOUNDARY ACTUALLY PERFORMS. `recarry' is owed because the export
      # half rebuilds the type over another payload to derive a relation for it. A record that came
      # in STATING its own relation is answered by that instead and is never rebuilt that way, so it
      # owes nothing. `retainedRelation' is gen's own word for that fact and its PRESENCE is the
      # whole question — this file asks what the record says about itself in this library's
      # vocabulary, and the shape of what was retained stays behind the boundary, where it belongs.
      missingRecarry =
        if declaresRole && !(t ? recarry) && !(t ? retainedRelation) then [ "recarry" ] else [ ];
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

  # The base module arguments a submodule's own evaluation WRITES OVER whatever a caller supplies.
  # `name` is injected by the two `evalModuleTree` calls below; `config`, `options` and `prefix` are
  # injected by the engine itself at BOTH strata — `lib/modules.nix:1267` (declaration) and `:1529`
  # (value) — and in both the caller's set is on the LEFT of `//`, so the engine's key wins. A caller
  # stating one of these would have it silently discarded, which is exactly the loss the inlet exists
  # to prevent, so `withArgs` refuses it by name at the moment the caller states it.
  submoduleReservedArgs = {
    name = null;
    config = null;
    options = null;
    prefix = null;
  };

  # submodule — recurse into a nested evalModuleTree over the submodule module + all defs; binds the
  # per-key `name` (spec §1 item 3). One nested fixpoint per merge (spec §1 item 4).
  #
  # ★ THE CALLER'S BASE MODULE ARGS RIDE ON THE TYPE, NOT ON THE CONSTRUCTOR. `isModuleValue` admits
  # any attrset, so a constructor form — `submodule { modules = …; specialArgs = …; }` — is
  # indistinguishable from a config-shorthand module that happens to set `modules`, and the misread
  # is SILENT. The inlet is therefore a method on the built type, `(submodule mods).withArgs { … }`,
  # which no module value can be mistaken for. `evalModuleTree` already takes `specialArgs ? { }`, so
  # this EXPOSES a channel one level down rather than adding one.
  #
  # ★ THE ARGS ARE A PLAIN DESCRIPTOR ATTRIBUTE AND NOT A SECOND CARRIED ROLE, and that is forced:
  # `interface.roleOf` throws when `carries` names more than one role, because the foreign protocol
  # has exactly one payload slot. `exportType` ends `t // { … }` — a pass-through — so an ordinary
  # attribute crosses the boundary untouched and a gen partner's is readable from the relation.
  #
  # ★★ EVERY REBUILD RE-ENTERS `mkSubmodule`, WHICH IS WHY THERE IS ONE. Three expressions in this
  # record rebuild the type — `recarry`, `substructure.rebuild`, and the relation's union — and one
  # that re-entered the args-less published constructor would drop the caller's args silently.
  # `substructure.rebuild` is the one that looks like an edge case and is not: a foreign engine calls
  # `substSubModules` on EVERY option whose type has a module set (nixpkgs `fixupOptionType`),
  # including a single declaration, and gen's own containers delegate their rebuild to their
  # element's — so `attrsOf ((submodule mods).withArgs { … })` would lose the args without ever
  # crossing the boundary.
  mkSubmodule =
    args: modOrMods:
    let
      mods = if isList modOrMods then modOrMods else [ modOrMods ];
      # The args a nested evaluation runs with. The substrate's `name` is injected LAST, so its key
      # wins by construction rather than by the caller having behaved.
      argsAt = loc: args // { name = if loc == [ ] then "" else prelude.last loc; };
      # A submodule reads its definitions as nixpkgs `types.submodule` does: `mergeDefs` hands them
      # through `defsAsModules true` to a nested `evalModuleTree`, so an attrset def is CONFIG and a
      # function or path def is a MODULE, and the domain is `isModuleValue`'s and not "any value":
      # nixpkgs `submoduleWith`'s `isAttrs x || isFunction x || path.check x`, as at `deferredModule`.
      # Bound once: the fold's domain check below reads this same binding.
      admits = isModuleValue;
    in
    defineType {
      name = "submodule";
      # What a caller supplied through `withArgs`, stated in gen's own words. Empty for a submodule
      # nobody added to, which is what makes the union below total.
      specialArgs = args;
      # THE INLET. Refusal lives HERE — one place, where the caller states the key — rather than at
      # the eval sites, where the loss would already have happened and the name would be gone.
      withArgs =
        a:
        let
          reserved = filter (k: submoduleReservedArgs ? ${k}) (attrNames a);
        in
        if reserved != [ ] then
          throw (
            "gen-merge: `withArgs' cannot supply the base module argument"
            + (if length reserved == 1 then " " else "s ")
            + concatStringsSep ", " (map (k: "`${k}'") reserved)
            + "; a submodule's own evaluation injects over whatever a caller supplies there, so the "
            + "value would be discarded rather than used"
          )
        else
          mkSubmodule (args // a) mods;
      inherit admits;
      # With no surviving definition the value is the module set evaluated over NO definitions, as
      # nixpkgs `submoduleWith`'s `emptyValue.value = base.config`: `base` is evaluated at no prefix
      # with the documentation placeholder as `name`, so its defaults read as they would there and an
      # undefined sub-option refuses by name.
      whenEmpty.value =
        (evalModuleTree {
          modules = mods;
          prefix = [ ];
          specialArgs = args // {
            name = "‹name›";
          };
          check = true;
        }).config;
      # What this type is parameterised BY. A submodule carries a MODULE SET, which is why its
      # relation unions rather than merges: an option declared as a submodule in two modules ends up
      # declaring the union of what they declare. On a nullary relation the second declaration would
      # be discarded silently.
      carries.moduleSet = mods;
      recarry = c: mkSubmodule args c.moduleSet;
      typeMergeRel =
        other:
        if !(isAttrs other) || (other.name or null) != "submodule" then
          { refused = "`submodule' and `${nameOf other}'"; }
        else
          let
            partnerMods = interface.importedCarried "moduleSet" other;
            # A partner's base module args are read off the descriptor attribute directly, for the
            # reason stated above: it is an ordinary attribute and survives export.
            #
            # ★ SCOPED TO GEN'S OWN MERGE PATH — `lib/modules.nix`'s `mergeTypes`, which is what the
            # declaration stratum consults when one option is declared twice. A FOREIGN engine merges
            # two declarations through `functor.binOp` (`lib/interface.nix:665-675`) instead, and
            # that arm recarries BOTH operands off the LEFT type, so it compares this type's args
            # with themselves: no conflict can be seen there and the left declaration's args win
            # silently. That path is not reachable with a gen partner anyway — `importedCarried`
            # requires a payload stating the module set ALONE, and a foreign `submoduleWith` states
            # its own parameters beside it, which the arm above already refuses by name.
            partnerArgs = other.specialArgs or { };
            conflicting = filter (k: (partnerArgs ? ${k}) && partnerArgs.${k} != args.${k}) (attrNames args);
          in
          if partnerMods == null then
            {
              refused = "`submodule' and a partner whose module set is stated beside parameters this one does not carry";
            }
          # The module sets UNION, so the args must too — and two declarations that disagree about
          # what a base module argument IS are a conflict this library names rather than resolves by
          # declaration order.
          else if conflicting != [ ] then
            {
              refused =
                "two `submodule' declarations stating different values for the base module argument"
                + (if length conflicting == 1 then " " else "s ")
                + concatStringsSep ", " (map (k: "`${k}'") conflicting);
            }
          else
            { merged = mkSubmodule (args // partnerArgs) (partnerMods ++ mods); };
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
            specialArgs = argsAt prefix;
            check = true;
          }).options;
        modules = mods;
        # Rebuild this type over the module set a consumer supplies. REPLACES `mods` — it does NOT
        # append: a foreign module system builds the replacement as this type's OWN modules
        # (relocated) plus any sibling declarations, so concatenating would re-include `mods` a
        # second time, double-evaluating the base module (a readOnly config value — e.g.
        # gen-schema's `den.schema._kindNames` — then throws "defined 2 times").
        rebuild = m: mkSubmodule args m;
      };
      # A definition outside `admits` is refused here, naming the option and the file, before the
      # module reader would refuse it without either (`refusingOutside`).
      mergeDefs = refusingOutside "submodule" admits (
        loc: defs:
        (evalModuleTree {
          modules = mods ++ defsAsModules true defs;
          prefix = loc;
          specialArgs = argsAt loc;
          check = true;
        }).config
      );
    };

  # The published constructor — signature UNCHANGED, and args-less by construction. A caller adds
  # base module args to the TYPE it returns, never to this.
  submodule = mkSubmodule { };

  # listOf — concat all list defs in order (byte-mode drops the order pass; spec §7), each element
  # merged through the element type (a submodule element becomes an instance; a leaf is verified).
  listOf =
    element:
    let
      # `mergeDefs` walks each definition with `imap0`, so a definition that is not a list is one
      # this type cannot consume — the domain, stated where the type is built and bound once: the
      # fold's domain check reads this same binding and refuses the definition by name.
      admits = isList;
    in
    defineType {
      name = "listOf";
      inherit admits;
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
      # A position whose every definition was discharged is DROPPED, as nixpkgs' `listOf` drops it.
      # The index is taken BEFORE the drop, as nixpkgs indexes inside its `filter`, so a survivor's
      # loc (and a submodule element's `name`) is its source position whatever an earlier sibling's
      # condition says.
      mergeDefs = refusingOutside "listOf" admits (
        loc: defs:
        concatMap (
          d:
          concatLists (
            imap0 (
              i: v:
              optional (isDefinedValue v) (
                mergeDefs (loc ++ [ (toString i) ]) element [
                  {
                    inherit (d) file;
                    value = v;
                  }
                ]
              )
            ) d.value
          )
        ) defs
      );
    };

  # attrsOf / lazyAttrsOf — per-key merge through the element type. They differ where nixpkgs' do: a
  # key whose every definition was discharged is DROPPED by `attrsOf` and KEPT by `lazyAttrsOf` (at
  # the element's empty value), so `attrsOf`'s key set forces each key's definitions to WHNF.
  attrsOfWith =
    tyName: element:
    let
      # `mergeDefs` takes the key union across the definitions and indexes each by key, so a
      # definition that is not an attrset is one this type cannot consume. Bound once: the fold's
      # domain check reads this same binding and refuses the definition by name.
      admits = isAttrs;
    in
    defineType {
      name = tyName;
      inherit admits;
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
      # The fold is selected ONCE, when the type is built, and not per call: the lazy fold's text is
      # the hub bench's `wideFreeform` hot path, whose allocation bound has no headroom for a test
      # inside it. The domain check wraps whichever fold was selected, so the selection stays here.
      mergeDefs = refusingOutside tyName admits (
        if tyName == "attrsOf" then
          loc: defs:
          listToAttrs (
            concatMap (
              k:
              let
                ds = concatMap (
                  d:
                  optional (d.value ? ${k}) {
                    inherit (d) file;
                    value = d.value.${k};
                  }
                ) defs;
              in
              optional (isDefinedBy ds) {
                name = k;
                value = mergeDefs (loc ++ [ k ]) element ds;
              }
            ) (attrNames (foldl' (acc: d: acc // d.value) { } defs))
          )
        else
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
          )
      );
    };
  attrsOf = attrsOfWith "attrsOf";
  lazyAttrsOf = attrsOfWith "lazyAttrsOf";

  # attrs — the NULLARY container: an attribute set whose KEYS are its whole content, with no element
  # type to descend into. The injected leaf library answers "is this value an attribute set", which is
  # a predicate over ONE value; a module system asks two further questions a predicate cannot state —
  # what zero definitions are worth, and how several of them combine. Those are properties of a merge
  # STRATEGY, and every other container in this file already answers them here.
  #
  # ★ THE NAME COLLIDES, AND THE COLLISION IS DECLARED IN TWO PLACES BECAUSE IT IS TWO COLLISIONS.
  # The EXPORT collision — this name is already in the leaf library's export environment — is admitted
  # by the `attrs` allowlist entry at `lib/default.nix`, which keeps the shadowed predicate reachable.
  # The TYPE-MERGE collision is new at this name and is not the same fact: unlike `listOf`/`attrsOf`,
  # whose two spellings disagree in their NAMES and so never meet as merge operands, both spellings
  # here are literally `attrs`. That is what the stated relation below answers.
  attrs =
    let
      # The domain stays the predicate's. What this type does with a definition OUTSIDE that domain
      # is stated by its fold because the engine does not state it: the post-fold check reads
      # `verify`, and a structural type carries `admits`, so the engine never consults `admits` on
      # the option-fold path. Bound once, for `admits` and for the fold's domain check alike.
      admits = isAttrs;
    in
    defineType {
      name = "attrs";
      inherit admits;
      whenEmpty.value = { };
      # STATED, NOT INHERITED, AND TWO-LEVEL. The default nullary relation matches on `.name` alone,
      # which is right for a name this library alone mints. This is not one of those, so a name-only
      # relation would answer `merged` to any same-named partner and silently adopt a fold that is not
      # this one's. The second level asks the DISCRIMINATING FACT — did the partner bring a fold of its
      # own? — through `mergeDefs`, the same presence test the engine's own dispatch asks.
      #
      # ★ THREE ANSWERS, AND THE THIRD IS WHY THERE ARE NOT TWO. Collapsing the name mismatch and the
      # foldless same-name case into one `else` reports "a partner named `attrs'" about a partner named
      # `string', and reaches the refusal shape this file's discipline forbids — the same name on both
      # sides of the pair, which tells the reader nothing they did not already have.
      typeMergeRel =
        other:
        if !(isAttrs other) || (other.name or null) != "attrs" then
          { refused = "`attrs' and `${nameOf other}'"; }
        else if other ? mergeDefs then
          { merged = attrs; }
        else
          { refused = "`attrs' and a partner named `attrs' that states no fold of its own"; };
      # THE FOLD IS TOTAL OVER ITS INPUT IN BOTH DIRECTIONS, and each refusal is a catchable throw
      # naming the option, this type, and the files that wrote the definitions at fault.
      #
      # ★ THE DOMAIN CHECK RUNS BEFORE THE FOLD, matching `either`'s fold below — and it has to run
      # there rather than after. The engine's `verify` dispatch reads the FOLDED result, so a definition
      # this type cannot consume would reach `//` first and the interpreter would answer with a raw
      # type error naming neither the option nor the file, an abort no caller can turn into a
      # diagnostic. The check is `refusingOutside`, the one every structural container here uses.
      #
      # ★ A SURVIVING SAME-KEY COLLISION IS AN UNRESOLVED AMBIGUITY, NOT AN OVERRIDE (ADR-0029). By the
      # time this fold runs the priority pass has already resolved every INTENDED override, so a key two
      # definitions still both set is a disagreement nobody expressed, and letting fold order drop one
      # side is the silent-loss shape this project refuses. Disjoint keys union; a collision refuses by
      # name, and names the key — which is the part the author has to go and reconcile.
      mergeDefs = refusingOutside "attrs" admits (
        loc: defs:
        let
          keys = attrNames (foldl' (acc: d: acc // d.value) { } defs);
          collided = filter (k: length (filter (d: d.value ? ${k}) defs) > 1) keys;
          collidingFiles = map (d: toString (d.file or "<def>")) (
            filter (d: filter (k: d.value ? ${k}) collided != [ ]) defs
          );
        in
        if collided != [ ] then
          throw "gen-merge: option `${showOption loc}' has `attrs' definitions that collide at ${
            concatStringsSep ", " (map (k: "`${k}'") collided)
          } (${concatStringsSep ", " collidingFiles})"
        else
          foldl' (res: d: res // d.value) { } defs
      );
    };

  # deferredModule (spec §1 item 7) — collect defs into ONE module (via imports), located; NEVER
  # forced by the composition plane. Output is a plain, import-usable module value (nixpkgs-faithful:
  # a deferred module's fold produces `{ imports = [ … ]; }`), handed opaque to the terminal.
  deferredModule =
    let
      # A type carrying no domain at all accepts every definition, which is right only for a type
      # whose fold really does accept any value. This one's does not: `mergeDefs` wraps each def into
      # an `imports` list, and the engine's `callM` (lib/modules.nix) can apply only a path, a string
      # naming an absolute path, a function, a `__functor` attrset, or a plain attrset. Any other
      # value carried into `imports` unexamined would be refused by whoever imports it — accepted
      # HERE and failing somewhere else, with no option path and no definition file. So the fold
      # refuses it here, by name, through the same binding it states as `admits`.
      #
      # The domain is nixpkgs `deferredModuleWith`'s `isAttrs x || isFunction x || path.check x`,
      # whose `path` predicate admits a STRING beginning with `/` as well as a path; `callM` imports
      # both.
      admits = isModuleValue;
    in
    defineType {
      name = "deferredModule";
      inherit admits;
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
      mergeDefs = refusingOutside "deferredModule" admits (
        loc: defs: {
          imports = map (
            d: setDefaultModuleLocation "${toString (d.file or "<def>")}, via option ${showOption loc}" d.value
          ) defs;
        }
      );
    };

  # The module-value domain, shared by the two types whose definitions ARE modules (`submodule`,
  # `deferredModule`) so the two cannot drift into answering it differently. The engine's `callM`
  # applies a path, a string naming an absolute path, a function, a `__functor` attrset or a plain
  # attrset, and nothing else; the string test is the loader's own `isPathString`, so this domain is
  # nixpkgs `pathWith { absolute = true; }` beside attrsets and functions, context irrelevant.
  isModuleValue = v: isAttrs v || isFunction v || builtins.isPath v || isPathString v;

  # A STRUCTURAL FOLD IS TOTAL OVER ITS INPUT: a definition outside the type's stated domain is
  # refused catchably, naming the option, the type and the files, BEFORE the fold runs — otherwise
  # it reaches `imap0`/`//`/`?` and the interpreter aborts with a raw type error naming neither, or
  # (`deferredModule`) is accepted here and fails wherever it is imported. The engine's post-fold
  # check reads `verify`, never `admits`, so each structural constructor applies this to its own
  # fold, passing the SAME binding it states as `admits`; its domain check therefore cannot disagree
  # with the `check` it exports. It tests the surviving definitions (after discharge, priority and
  # order), where nixpkgs' `checkedAndMerged` tests `defsFinal`, and forces each only to WHNF, which
  # the engine's discharge has already done. The refusal list is built only on refusal.
  refusingOutside =
    tyName: inDomain: fold: loc: defs:
    if all (d: inDomain d.value) defs then
      fold loc defs
    else
      throw "gen-merge: option `${showOption loc}' has definitions `${tyName}' cannot consume (${
        concatStringsSep ", " (map (d: toString (d.file or "<def>")) (filter (d: !(inDomain d.value)) defs))
      })";

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
    attrs
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
