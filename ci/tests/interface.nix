# The PROTOCOL BOUNDARY, and the four predicates that decide whether it is worth having.
#
# `lib/interface.nix` exists on a conditional licence: build the boundary, and if it turns out to be
# ceremony and unnecessary complexity, collapse it back into gen-merge. A condition nobody can read is
# not a condition, so this suite is where the four ceremony predicates PRODUCE VALUES rather than
# opinions. Three of them live here; the fourth (C-4, the engine's dispatch basis) is behavioural and
# lives in `type-merge-relation.nix`, where it was red before the rewire and green after.
#
#   T3   the foreign protocol is uttered in EXACTLY ONE unit — the claim the boundary is FOR
#   C-1  the unit only forwards          → count the classes; DERIVED must exceed FOREIGN CONSTANT
#   C-2  a field set with no translation → no derived field is read off a gen field of the same name
#   C-3  the boundary is crossed one direction only → the inbound arm is present AND reached
#   O2   the foreign engine's behaviour survives the translation, against a REAL `lib.evalModules`
#
# ★★ EVERY ABSENCE CLAIM HERE CARRIES A LIVE CONTROL IN THE SAME RUN, because every one of them is a
# claim that a scan found nothing — and a scan that cannot find anything reports exactly that. The
# T3 cells scan a seeded source that MUST come back positive; the C-2 cell poisons a gen source and
# MUST throw. Without those the whole suite is consistent with a predicate that never matched.
{
  interface,
  genMerge,
  genMergeCore,
  genMergeVocab,
  nixpkgsLib,
  genPrelude,
  lib,
  ...
}:
let
  ifc = interface;
  V = genMergeVocab;
  fourteen = ifc.exportFields;
  classes = ifc.exportClasses;
  derivedFields = builtins.attrNames classes.derived;

  # ── T3, arm one: the library SOURCE ─────────────────────────────────────────────────────────────
  # Tokenise rather than substring-match. A substring scan cannot tell `functor` from `__functor` or
  # `typeMerge` from `typeMergeRel`, and this document's own basis records a scan whose only hit for a
  # protocol field was inside a COMMENT — so comments come off first and the rest is split on
  # non-identifier characters, which makes "does this file name that field" an exact question.
  stripComments =
    text:
    lib.concatStringsSep "\n" (
      map (line: lib.head (lib.splitString "#" line)) (lib.splitString "\n" text)
    );
  identifiersOf =
    code: builtins.filter builtins.isString (builtins.split "[^A-Za-z0-9_]+" (stripComments code));

  walk =
    dir:
    lib.concatLists (
      lib.mapAttrsToList (
        name: type:
        if type == "directory" then
          walk (dir + "/${name}")
        else if lib.hasSuffix ".nix" name then
          [ (dir + "/${name}") ]
        else
          [ ]
      ) (builtins.readDir dir)
    );
  sourceOf = name: text: {
    inherit name;
    ids = identifiersOf text;
    code = stripComments text;
  };
  libSources = map (p: sourceOf (builtins.baseNameOf (toString p)) (builtins.readFile p)) (
    walk ../../lib
  );

  # WHICH OF THE FOURTEEN ARE LEXICALLY SCANNABLE, stated rather than glossed. Five of them —
  # `name`, `description`, `check`, `merge`, `_type` — are ordinary words this library uses for its
  # own things (`mkOption`'s tag, `evalModuleTree`'s `check` argument, every `merge`-prefixed
  # binding), so a token scan for them would report hits that are not the foreign protocol at all. A
  # scan that has to be argued with is not an oracle. Those five are covered by ARM TWO instead,
  # which is name-blind: it asks who MINTS the field, not who spells it.
  scannable = [
    "descriptionClass"
    "deprecationMessage"
    "emptyValue"
    "getSubOptions"
    "getSubModules"
    "substSubModules"
    "typeMerge"
    "nestedTypes"
    "functor"
    # Not one of the fourteen, but the payload spelling and the marker are foreign data on the same
    # terms, and leaking either leaks the protocol just as surely.
    "elemType"
    "_protoLeafMerge"
  ];
  filesNaming = tok: map (s: s.name) (builtins.filter (s: builtins.elem tok s.ids) libSources);

  # ★ THE TAG IS A STRING LITERAL, NOT AN IDENTIFIER, so the token scan above is STRUCTURALLY BLIND TO
  # IT: splitting on non-identifier characters turns `"option-type"` into `option` and `type`, two
  # ordinary words. It is foreign data on exactly the terms the fourteen are — a value uttered outside
  # the boundary leaks the protocol just as surely as a field name — so it gets a SUBSTRING row of its
  # own rather than riding an arm that cannot see it. The quotes are part of the needle: they are what
  # separate the tag from prose about option types.
  literalTag = ''"option-type"'';
  filesContaining = s: map (x: x.name) (builtins.filter (x: lib.hasInfix s x.code) libSources);

  # THE SEEDED CONTROLS, same predicates, same run. A synthetic source that DOES carry each needle
  # must come back carrying it, and one that carries it only in a COMMENT must not; if either row
  # stops discriminating, the scans above have gone quiet for a reason that is not cleanliness.
  seededSource = sourceOf "seeded-control.nix" ''
    # a comment naming emptyValue and "option-type", neither of which must be seen
    leak = t: t.getSubModules or null;
    tag = { _type = "option-type"; };
  '';

  # ── T3, arm two: WHO MINTS THE FIELD ────────────────────────────────────────────────────────────
  # Name-blind and total over all fourteen. A gen record built to the substrate vocabulary carries
  # none of the foreign protocol; the same record, exported, carries all of it. So the boundary is
  # where the fourteen come FROM, whatever any file happens to spell.
  probeElement = genMerge.types.str;
  probeGen = V.mkType {
    name = "probe";
    verify = v: if builtins.isInt v then null else "not an int";
    mergeDefs = _loc: defs: (builtins.head defs).value;
    whenEmpty.value = 0;
    deprecated = "probe is deprecated";
    carries.element = probeElement;
    recarry = c: V.listOf c.element;
    substructure = {
      declares = _prefix: {
        probeDeclares = true;
      };
      modules = [ ];
      rebuild = _m: null;
    };
  };
  probeExported = ifc.exportType probeGen;

  # ── C-2: the boundary must not read a gen field of a DERIVED field's own name ───────────────────
  # Mechanical, and it does not depend on reading the boundary's source. Hand `exportType` the SAME
  # gen record with every derived field's own NAME additionally present and set to a throw. If any
  # derivation read `t.<that name>` the export detonates; if none does, the export is unchanged. The
  # domain is the DERIVED ten and not the fourteen: the two name-carried fields are the same word on
  # both sides BY CONSTRUCTION and the two constants read nothing at all.
  poison = f: throw "the boundary read `${f}' off the gen record, which is C-2";
  poisonedGen =
    probeGen
    // builtins.listToAttrs (
      map (f: {
        name = f;
        value = poison f;
      }) derivedFields
    );

  # Everything a derived field can be asked, forced. Functions cannot be compared in Nix, so each one
  # is APPLIED and its answer is what the comparison sees — which is the stronger reading anyway: two
  # exports agree when they BEHAVE the same, not when they happen to share a closure.
  summarise = t: {
    admitsAnInt = t.check 3;
    rejectsAString = t.check "x";
    folds =
      t.merge
        [ "o" ]
        [
          {
            file = "a";
            value = 7;
          }
        ];
    empty = t.emptyValue;
    wraps = builtins.attrNames t.nestedTypes;
    deprecation = t.deprecationMessage;
    declares = builtins.attrNames (t.getSubOptions [ ]);
    moduleSet = t.getSubModules;
    rebuild = t.substSubModules [ ];
    functorName = t.functor.name;
    functorPayload = builtins.attrNames t.functor.payload;
    mergesWithItsOwnFunctor = (t.typeMerge t.functor) != null;
  };

  # ── C-3: the inbound arm, present and REACHED ───────────────────────────────────────────────────
  # A type carrying ONLY the foreign protocol — no gen relation, no gen fold. Nothing in the engine
  # can answer a question about it except through the import environment, so if the engine answers at
  # all, the inbound arm ran.
  foreignOnlyType = name: {
    inherit name;
    typeMerge = f: if (f.name or null) == name then foreignOnlyType name else null;
    functor = {
      inherit name;
      type = foreignOnlyType name;
      payload = null;
      binOp = _a: _b: null;
    };
  };
  foreignOnlyFold = {
    name = "foreignFold";
    merge = _loc: defs: "folded ${toString (builtins.length defs)}";
  };

  # ── O2: mounted in a REAL `lib.evalModules` ────────────────────────────────────────────────────
  mountType =
    t: def:
    (nixpkgsLib.evalModules {
      modules = [
        { options.x = nixpkgsLib.mkOption { type = t; }; }
        { config.x = def; }
      ];
    }).config.x;
  gauge = V.defineType {
    name = "gauge";
    verify = v: if builtins.isInt v then null else "expected an int";
  };
  # MUTANT ONE — the value predicate mis-translated: it rejects everything. A mount must be REFUSED.
  gaugeRejectsAll = V.defineType {
    name = "gauge";
    verify = _v: "never valid";
  };
  # MUTANT TWO — the fold mis-translated: it returns a value the definition did not supply. This one
  # does not abort, which is the point — it is caught by DISAGREEING with the native arm, and a
  # mutant that could only be caught by an abort would not test the translation at all.
  gaugeFoldsWrong = V.defineType {
    name = "gauge";
    verify = v: if builtins.isInt v then null else "expected an int";
    mergeDefs = _loc: defs: (builtins.head defs).value + 1;
  };
  caught = v: !(builtins.tryEval (builtins.deepSeq v v)).success;
in
{
  flake.tests.interface = {
    # ── T3 ────────────────────────────────────────────────────────────────────────────────────────
    # EXACT SET, not presence: the answer is the file list, so a second file naming a protocol field
    # fails with that file's name in the diff rather than flipping a boolean.
    test-foreign-protocol-is-uttered-in-exactly-one-unit = {
      expr = builtins.listToAttrs (
        map (tok: {
          name = tok;
          value = filesNaming tok;
        }) scannable
      );
      expected = builtins.listToAttrs (
        map (tok: {
          name = tok;
          value = [ "interface.nix" ];
        }) scannable
      );
    };

    # THE TAG, as a substring rather than a token, because the scan above cannot see a string literal.
    test-the-option-type-tag-is-uttered-in-exactly-one-unit = {
      expr = filesContaining literalTag;
      expected = [ "interface.nix" ];
    };

    # THE SCAN CAN FIND THINGS, and it ignores comments. Both halves matter: the first says the cell
    # above is a measurement rather than a broken predicate, the second says a protocol field
    # DISCUSSED in a comment is not a leak — which is the distinction the whole scan turns on.
    test-control-source-scan-sees-a-seeded-leak-and-not-a-comment = {
      expr = {
        seenInCode = builtins.elem "getSubModules" seededSource.ids;
        seenInComment = builtins.elem "emptyValue" seededSource.ids;
        # The SAME two halves for the substring row, whose needle the token scan cannot represent at
        # all — so without these the tag cell above would be an unarmed assertion sitting beside an
        # armed one and reading exactly like it.
        tagSeenInCode = lib.hasInfix literalTag seededSource.code;
        tagSeenInComment = lib.hasInfix "neither of which" seededSource.code;
        wholeWordsOnly = {
          # `typeMergeRel` must not read as `typeMerge`, and `__functor` must not read as `functor`.
          relationIsNotTheProtocolField =
            builtins.elem "typeMergeRel" (identifiersOf "typeMergeRel = x;")
            && !(builtins.elem "typeMerge" (identifiersOf "typeMergeRel = x;"));
          functorAttrIsNotTheProtocolField = !(builtins.elem "functor" (identifiersOf "m ? __functor"));
          # And the tag really is invisible to the token arm, which is WHY it needs its own row.
          tagIsNotAToken = !(builtins.elem "option-type" (identifiersOf ''x = "option-type";''));
        };
      };
      expected = {
        seenInCode = true;
        seenInComment = false;
        tagSeenInCode = true;
        tagSeenInComment = false;
        wholeWordsOnly = {
          relationIsNotTheProtocolField = true;
          functorAttrIsNotTheProtocolField = true;
          tagIsNotAToken = true;
        };
      };
    };

    # ARM TWO, name-blind and total over the fourteen: the substrate record carries none of them but
    # the one that is name-carried, and the export carries every one. This is the half that covers
    # `name`/`description`/`check`/`merge`/`_type`, which no token scan can speak about.
    test-the-fourteen-are-minted-at-the-boundary-and-nowhere-else = {
      expr = {
        onTheGenRecord = builtins.filter (f: probeGen ? ${f}) fourteen;
        missingFromTheExport = builtins.filter (f: !(probeExported ? ${f})) fourteen;
      };
      expected = {
        # `name` is NAME-CARRIED: it is correctly the same word on both sides, and it is the only one.
        onTheGenRecord = [ "name" ];
        missingFromTheExport = [ ];
      };
    };

    # ── C-1: the unit only forwards ───────────────────────────────────────────────────────────────
    # The partition must be TOTAL and DISJOINT over the fourteen — a field in two classes or in none
    # makes the count below unreadable — and DERIVED must exceed FOREIGN CONSTANT. There is no
    # FORWARDED class and a field fitting none of the three is a finding, which is what
    # `unclassified` reports.
    test-c1-the-class-partition-is-total-and-derived-dominates = {
      expr =
        let
          all = derivedFields ++ classes.foreignConstant ++ classes.nameCarried;
        in
        {
          unclassified = builtins.filter (f: !(builtins.elem f all)) fourteen;
          notAProtocolField = builtins.filter (f: !(builtins.elem f fourteen)) all;
          doubleClassified = builtins.length all != builtins.length fourteen;
          derived = builtins.length derivedFields;
          foreignConstant = builtins.length classes.foreignConstant;
          nameCarried = builtins.length classes.nameCarried;
          derivedExceedsForeignConstant =
            builtins.length derivedFields > builtins.length classes.foreignConstant;
        };
      expected = {
        unclassified = [ ];
        notAProtocolField = [ ];
        doubleClassified = false;
        derived = 10;
        foreignConstant = 2;
        nameCarried = 2;
        derivedExceedsForeignConstant = true;
      };
    };

    # EVERY DERIVED FIELD NAMES A GEN SOURCE, and no source is the field's own name. The second half
    # is C-2 stated over the published table; the cell below is C-2 stated over the behaviour.
    test-c1-every-derived-field-names-a-differently-named-source = {
      expr = builtins.filter (f: classes.derived.${f} == f) derivedFields;
      expected = [ ];
    };

    # ── C-2: a field set with no translation ──────────────────────────────────────────────────────
    # Poison every derived field's own NAME on the gen record. If the boundary reads any of them the
    # export detonates; it does not, so every derived field came from a differently-named datum.
    test-c2-the-boundary-reads-no-gen-field-of-a-derived-fields-own-name = {
      expr = summarise (ifc.exportType poisonedGen);
      expected = summarise probeExported;
    };

    # THE CONTROL, same poison, same run: poison a GEN SOURCE instead and the export MUST detonate.
    # Without this row the cell above is equally consistent with a `summarise` that forces nothing.
    #
    # ★ THE FUNCTION-VALUED ROWS ARE APPLIED, NOT MERELY FORCED, and this row is where that was
    # measured rather than reasoned: a function is already in weak head normal form, so forcing one
    # reaches no throw inside its body. Written as a bare force, `verify` and `typeMergeRel` both
    # reported "no detonation" — a control silently declaring itself unarmed on exactly the two
    # fields whose derivations are functions.
    test-control-c2-poisoning-a-gen-source-does-detonate = {
      expr = {
        verifyPoisoned = caught ((ifc.exportType (probeGen // { verify = poison "verify"; })).check 3);
        foldPoisoned = caught (ifc.exportType (probeGen // { mergeDefs = poison "mergeDefs"; })).merge;
        emptyPoisoned =
          caught
            (ifc.exportType (probeGen // { whenEmpty = poison "whenEmpty"; })).emptyValue;
        carriesPoisoned = caught (ifc.exportType (probeGen // { carries = poison "carries"; })).nestedTypes;
        substructurePoisoned =
          caught
            (ifc.exportType (probeGen // { substructure = poison "substructure"; })).getSubModules;
        deprecatedPoisoned =
          caught
            (ifc.exportType (probeGen // { deprecated = poison "deprecated"; })).deprecationMessage;
        relationPoisoned =
          let
            e = ifc.exportType (probeGen // { typeMergeRel = poison "typeMergeRel"; });
          in
          caught (e.typeMerge probeExported.functor);
      };
      expected = {
        verifyPoisoned = true;
        foldPoisoned = true;
        emptyPoisoned = true;
        carriesPoisoned = true;
        substructurePoisoned = true;
        deprecatedPoisoned = true;
        relationPoisoned = true;
      };
    };

    # ── C-3: the boundary is crossed BOTH directions ──────────────────────────────────────────────
    # Present, and REACHED from the engine's own type merge: a pair carrying only the foreign protocol
    # merges, and nothing but the import environment could have answered for it.
    test-c3-the-inbound-arm-is-reachable-from-the-engine = {
      expr = {
        present = ifc ? importType;
        foreignPairMerges = genMergeCore.mergeTypes (foreignOnlyType "fx") (foreignOnlyType "fx") != null;
        foreignPairAcrossNamesRefuses =
          genMergeCore.mergeTypes (foreignOnlyType "fx") (foreignOnlyType "fy") == null;
        # The VALUE path reaches it too: a type whose only fold is the foreign one still folds.
        foreignFoldRuns = genMerge.mergeDefs [ "o" ] foreignOnlyFold [
          {
            file = "a";
            value = 1;
          }
        ];
      };
      expected = {
        present = true;
        foreignPairMerges = true;
        foreignPairAcrossNamesRefuses = true;
        foreignFoldRuns = "folded 1";
      };
    };

    # THE CONTROL: strip the foreign protocol from the same fixtures and the same questions answer
    # differently. Without it, "the foreign pair merges" is equally consistent with an engine that
    # merges anything, and "the foreign fold runs" with one that folds by luck.
    test-control-c3-without-the-foreign-protocol-the-same-fixtures-do-not-answer = {
      expr = {
        strippedPairDoesNotMerge =
          genMergeCore.mergeTypes (builtins.removeAttrs (foreignOnlyType "fx") [
            "typeMerge"
            "functor"
          ]) (foreignOnlyType "fx") == null;
        # With no fold of its own in EITHER vocabulary the engine's own leaf fold takes the value.
        strippedFoldFallsToTheLeafFold =
          genMerge.mergeDefs [ "o" ] (builtins.removeAttrs foreignOnlyFold [ "merge" ])
            [
              {
                file = "a";
                value = 1;
              }
            ];
      };
      expected = {
        strippedPairDoesNotMerge = true;
        strippedFoldFallsToTheLeafFold = 1;
      };
    };

    # ── O2: the foreign engine's behaviour survives the translation ───────────────────────────────
    # Asserted on the RESOLVED CONFIG VALUE out of a real `lib.evalModules`, never on evaluation
    # alone: a type that merely evaluates has been mounted, not exercised.
    test-o2-an-exported-type-resolves-inside-a-real-evalModules = {
      expr = {
        gen = mountType gauge 7;
        # THE NATIVE ARM: the equivalent foreign-native type reaches the same value, so "it resolved"
        # is a statement about agreement rather than about this type alone.
        native = mountType nixpkgsLib.types.int 7;
      };
      expected = {
        gen = 7;
        native = 7;
      };
    };

    # THE MUTANT ARM, same run, and it must FAIL. One derived field is deliberately mis-translated in
    # each fixture: the first inverts the value predicate and must be REFUSED by the foreign engine;
    # the second corrupts the fold and is caught by DISAGREEING with the native arm rather than by
    # aborting — a mutant catchable only by an abort would be testing the interpreter, not the
    # translation.
    test-o2-a-mis-translated-derived-field-is-rejected = {
      expr = {
        rejectsAllIsRefused = caught (mountType gaugeRejectsAll 7);
        foldsWrongDisagreesWithTheNativeArm =
          mountType gaugeFoldsWrong 7 != mountType nixpkgsLib.types.int 7;
        # CONTROL: the un-mutated twin, same shape, same mount, is accepted and agrees.
        unmutatedIsAccepted = !(caught (mountType gauge 7));
      };
      expected = {
        rejectsAllIsRefused = true;
        foldsWrongDisagreesWithTheNativeArm = true;
        unmutatedIsAccepted = true;
      };
    };
  };
}
