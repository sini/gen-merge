# WHAT A TYPE CARRIES HAS ONE SOURCE (`lib/interface.nix` `statedRoles`), and a functor payload is
# read only for what a type MERGES on (`importedOffered`).
#
# A descriptor says what it carries in the carrying spellings — `nestedTypes` (`elemType`, or a
# union's `left`/`right`), a top-level `elemType`, or a module set in `getSubModules` — and the
# import's `carries` and the refusal's domain both read that one binding. The functor payload is the
# parameter a type offers to merge on; the container relations read it through `importedOffered`,
# whole and in its role's shape, and never through what the partner carries. The cells below pin
# each class one field apart, the relation reading what a type offers, the read-whole guard held for
# an IMPORTED partner as for a raw one, and the identity walk's stop where a type carries an element
# but states no position for it.
{
  genMerge,
  interface,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  gt = gm.types;
  t = nixpkgsLib.types;
  inherit (gm) evalModuleTree mkOption mkForce;
  imp = gm.mkOptionType;

  keysOf = x: if builtins.isAttrs x then builtins.attrNames x else [ ];
  # Whether a gen nesting record over `nested` imports refused, or "throws" where deciding it throws.
  nestingDecided =
    nested:
    let
      e = builtins.tryEval (
        interface.importType (
          base
          // {
            name = "box";
            nests = true;
            mergeDefs.threaded = true;
            nestedTypes = nested;
          }
        )
        ? refused
      );
    in
    if e.success then e.value else "throws";
  ok = e: (builtins.tryEval (builtins.deepSeq e e)).success;
  read =
    d:
    let
      a = interface.importType d;
    in
    if a ? refused then
      "refused"
    else
      let
        ty = imp d;
      in
      if !(ok (builtins.mapAttrs (_: builtins.typeOf) ty)) then
        "throws"
      else
        {
          carries = keysOf (ty.carries or { });
          nestedTypes = keysOf ty.nestedTypes;
        };
  sub3 = {
    getSubOptions = _: { };
    getSubModules = null;
    substSubModules = _: null;
  };
  base = {
    check = _: true;
    merge = _loc: defs: (builtins.head defs).value;
  };
  rel = {
    name = "box";
    type = _p: null;
    binOp = a: _b: a;
  };

  merged =
    a: b:
    let
      r = gm.mergeTypes a b;
    in
    if r == null then "REFUSED" else r.name;
  ev =
    tys: val:
    let
      res = evalModuleTree {
        modules = map (ty: { options.p = mkOption { type = ty; }; }) tys ++ [ { p = val; } ];
      };
      ty = builtins.tryEval (builtins.deepSeq res.options.p.type.name res.options.p.type.name);
      v = builtins.tryEval (builtins.deepSeq res.config.p res.config.p);
    in
    if ty.success then
      "MERGED ${ty.value} / ${if v.success then "ACCEPTED" else "REJECTED"}"
    else
      "REFUSED";

  # gen-schema's `refined` shape: the base's fields, its own relation, a `null` payload
  refinedLike =
    b:
    let
      self = imp (
        removeAttrs b [
          "functor"
          "typeMerge"
        ]
        // {
          __base = b;
          typeMerge =
            f:
            let
              p = f.type or null;
              j = if p ? __base then gm.mergeTypes b p.__base else null;
            in
            if j == null then null else refinedLike j;
          functor = {
            name = "refined<${b.name}>";
            type = self;
            payload = null;
            binOp = _a: _b: null;
          };
        }
      );
    in
    self;

  # a wrapper adding no path level, stated in the carrying spelling with a relation of its own
  spindle =
    el:
    imp {
      name = "spindle";
      check = v: v == null || el.check v;
      merge = loc: defs: el.merge loc defs;
      nestedTypes.elemType = el;
      getSubOptions = el.getSubOptions;
      getSubModules = el.getSubModules;
      substSubModules = m: spindle (el.substSubModules m);
      functor = {
        name = "spindle";
        payload = null;
        binOp = _a: _b: null;
        type = _p: spindle el;
      };
    };
  # a container stating its element in `nestedTypes` beside a payload that is the element itself
  bobbin =
    el:
    imp {
      name = "bobbin";
      check = builtins.isAttrs;
      merge = loc: defs: (gt.attrsOf el).merge loc defs;
      nestedTypes.elemType = el;
      getSubOptions = prefix: el.getSubOptions (prefix ++ [ "<name>" ]);
      getSubModules = el.getSubModules or null;
      substSubModules = _m: bobbin el;
      functor = {
        name = "bobbin";
        payload = el;
        binOp = a: b: if gm.mergeTypes a b == null then null else a;
        type = bobbin;
      };
    };

  # ── the identity walk, 72izy's instrument shape: a minted instance in the base forces the walk ──
  idMod =
    { config, ... }:
    {
      options.id_hash = mkOption { type = gt.str; };
      options.spool = mkOption {
        type = gt.str;
        default = "";
      };
      config.id_hash = "thimble:" + builtins.hashString "sha256" config.spool;
    };
  idSub = gt.submodule idMod;
  coldOf = mods: evalModuleTree { modules = mods; };
  warmOf =
    base: edited:
    evalModuleTree {
      modules = base ++ edited;
      warmFrom = coldOf base;
      editedModules = edited;
    };
  anchor = [
    { options.reg = mkOption { type = gt.attrsOf idSub; }; }
    {
      _file = "anc";
      config.reg.p.spool = "anchor";
    }
  ];
  # an unrelated edit re-composes warm; the reading is whether the warm read is total and equals cold
  hold =
    ty: v:
    let
      base = anchor ++ [
        { options.h = mkOption { type = ty; }; }
        {
          _file = "sb";
          config.h = v;
        }
      ];
      edit = [
        {
          _file = "o";
          options.other = mkOption { type = gt.str; };
          config.other = "o";
        }
      ];
      w = (warmOf base edit).config;
    in
    ok w && builtins.toJSON w == builtins.toJSON (coldOf (base ++ edit)).config;
  # the arming half: the edit MOVES the held instance's identity. A walked position refuses the warm
  # re-compose (the read throws); a stopped one re-composes warm and equals cold.
  moveRefused =
    ty: v: v':
    let
      base = anchor ++ [
        { options.h = mkOption { type = ty; }; }
        {
          _file = "sb";
          config.h = v;
        }
      ];
      edit = [
        {
          _file = "sm";
          config.h = mkForce v';
        }
      ];
    in
    !(ok (warmOf base edit).config);
in
{
  flake.tests.carries-one-source = {

    # ONE FIELD APART: which spelling states the element decides `carries`, and the payload never does
    test-carries-has-one-source = {
      expr = {
        payloadOnlyRel = read (
          base
          // {
            name = "box";
            functor = rel // {
              payload.elemType = gt.str;
            };
          }
        );
        payloadOnlyNoBinOpKey = read (
          base
          // {
            name = "box";
            functor = {
              name = "box";
              type = _p: null;
              payload.elemType = gt.str;
            };
          }
        );
        nestedOnlyRel = read (
          base
          // sub3
          // {
            name = "box";
            nestedTypes.elemType = gt.str;
            functor = rel // {
              payload = null;
            };
          }
        );
        unionRel = read (
          base
          // sub3
          // {
            name = "box";
            nestedTypes = {
              left = gt.str;
              right = gt.int;
            };
            functor = rel // {
              payload = null;
            };
          }
        );
        nestedNoSub = read (
          base
          // {
            name = "box";
            nestedTypes.elemType = gt.str;
          }
        );
        leaf = read (base // { name = "leaf"; });
      };
      expected = {
        payloadOnlyRel = {
          carries = [ ];
          nestedTypes = [ ];
        };
        payloadOnlyNoBinOpKey = {
          carries = [ ];
          nestedTypes = [ ];
        };
        nestedOnlyRel = {
          carries = [ "element" ];
          nestedTypes = [ "elemType" ];
        };
        unionRel = {
          carries = [ "alternatives" ];
          nestedTypes = [
            "left"
            "right"
          ];
        };
        nestedNoSub = "refused";
        leaf = {
          carries = [ ];
          nestedTypes = [ ];
        };
      };
    };

    # A RELATION READS WHAT ITS PARTNER OFFERS: a refinement offers no element (its payload is `null`),
    # so a bare container never merges with one, whichever vocabulary the refined base is in
    test-a-relation-reads-what-a-type-offers = {
      expr = {
        overGen = merged (gt.listOf gt.str) (refinedLike (gt.listOf gt.str));
        overNixpkgs = merged (gt.listOf gt.str) (refinedLike (t.listOf gt.str));
        ctlGenTwin = merged (gt.listOf gt.str) (gt.listOf gt.str);
        ctlRefinedTwin = merged (refinedLike (gt.listOf gt.str)) (refinedLike (gt.listOf gt.str));
      };
      expected = {
        overGen = "REFUSED";
        overNixpkgs = "REFUSED";
        ctlGenTwin = "listOf";
        ctlRefinedTwin = "listOf";
      };
    };

    # THE READ-WHOLE GUARD HOLDS FOR AN IMPORTED PARTNER AS FOR A RAW ONE: nixpkgs' `attrsOf` and
    # `submodule` payloads state more than the one parameter a gen relation merges on, so neither is
    # offered to one, imported or not, in either declaration order. A `listOf` payload is just its
    # element and still merges.
    test-an-imported-partner-is-read-whole = {
      expr = {
        attrsOfSub = ev [
          (gt.attrsOf (imp (t.submodule { })))
          (gt.attrsOf (gt.submodule { }))
        ] { a = { }; };
        attrsOfSubRev =
          ev
            [
              (gt.attrsOf (gt.submodule { }))
              (gt.attrsOf (imp (t.submodule { })))
            ]
            {
              a = { };
            };
        subTop = ev [
          (gt.submodule { })
          (imp (t.submodule { }))
        ] { };
        ctlListOf = ev [ (gt.attrsOf (gt.listOf gt.str)) (gt.attrsOf (imp (t.listOf gt.str))) ] {
          a = [ "x" ];
        };
        ctlListOfRev = ev [ (gt.attrsOf (imp (t.listOf gt.str))) (gt.attrsOf (gt.listOf gt.str)) ] {
          a = [ "x" ];
        };
      };
      expected = {
        attrsOfSub = "REFUSED";
        attrsOfSubRev = "REFUSED";
        subTop = "REFUSED";
        ctlListOf = "MERGED attrsOf / ACCEPTED";
        ctlListOfRev = "MERGED attrsOf / ACCEPTED";
      };
    };

    # A STATED NESTED ROLE CROSSES: a container stating its element only in `nestedTypes` is legible,
    # and a redeclaration whose join drops an element's check is seen
    test-a-stated-nested-role-crosses = {
      expr = {
        nestedTypes = keysOf (bobbin t.str).nestedTypes;
        carries = keysOf (bobbin t.str).carries;
        drop = ev [ (bobbin t.port) (bobbin t.int) ] { a = 70000; };
        ctlTwin = ev [ (bobbin t.str) (bobbin t.str) ] { a = "sateen"; };
      };
      expected = {
        nestedTypes = [ "elemType" ];
        carries = [ "element" ];
        drop = "REFUSED";
        ctlTwin = "MERGED bobbin / ACCEPTED";
      };
    };

    # THE IDENTITY WALK IS TOTAL WHERE A TYPE CARRIES AN ELEMENT BUT STATES NO POSITION FOR IT. A
    # record that crossed stating its own relation owes no `recarry`, so nothing says whether it adds
    # a path level; the walk stops there rather than guess. Wrappers and containers alike: every row
    # is a warm read that is total and equals cold. The walked controls state their position (a gen
    # wrapper, a refinement over a gen base, which keeps the base's `recarry`); a raw nixpkgs wrapper
    # states none either, and stops (`test-the-walk-reads-no-raw-payload` below).
    #
    # `idSub` is a gen `submodule`, a NESTING type, and each foreign or hand-rolled wrapper over it
    # through `mkOptionType` is refused at construction by the import refusal (den-hoag-n6dh7 OQ11
    # (d)), which `nesting-threaded` tests. So each row states the ruled escape hatch, `optedOut`
    # (`declaresNesting = false`), and is exercised through it in-suite: on the wrapper where the row
    # hands `mkOptionType` a record, on the element where the wrapper is built inside a helper.
    test-the-identity-walk-stops-where-no-position-is-stated =
      let
        optedOut = ty: ty // { declaresNesting = false; };
      in
      {
        expr = {
          # opted out on the wrapper: the refusal fires without it
          refinedNpNullOr = hold (refinedLike (optedOut (t.nullOr idSub))) { spool = "silk"; };
          # opted out on the wrapper: the refusal fires without it
          refinedNpUniq = hold (refinedLike (optedOut (t.uniq idSub))) { spool = "silk"; };
          # opted out on the element: `spindle` declares it by `nestedTypes`
          spindle = hold (spindle (optedOut idSub)) { spool = "silk"; };
          importedNpNullOr = hold (imp (t.nullOr idSub)) { spool = "silk"; };
          # opted out on the wrapper: nixpkgs' `uniq` is outside the six and declares its element
          importedNpUniq = hold (imp (optedOut (t.uniq idSub))) { spool = "silk"; };
          # opted out on the wrapper: the refusal fires without it
          refinedNpAttrsOf = hold (refinedLike (optedOut (t.attrsOf idSub))) { a.spool = "silk"; };
          # opted out on the element: `bobbin` declares it by `nestedTypes` and payload
          bobbin = hold (bobbin (optedOut idSub)) { a.spool = "silk"; };
          ctlGenNullOr = hold (gt.nullOr idSub) { spool = "silk"; };
          ctlNpNullOr = hold (t.nullOr idSub) { spool = "silk"; };
          # opted out on the wrapper: a record copy of gen's `nullOr` declares its element
          ctlRefinedGenNullOr = hold (refinedLike (optedOut (gt.nullOr idSub))) { spool = "silk"; };
          ctlGenAttrsOf = hold (gt.attrsOf idSub) { a.spool = "silk"; };
          # the walk is live: a moved identity under the gen controls is refused warm
          armedGenNullOr = moveRefused (gt.nullOr idSub) { spool = "silk"; } { spool = "satin"; };
          armedGenAttrsOf = moveRefused (gt.attrsOf idSub) { a.spool = "silk"; } { a.spool = "satin"; };
        };
        expected = {
          refinedNpNullOr = true;
          refinedNpUniq = true;
          spindle = true;
          importedNpNullOr = true;
          importedNpUniq = true;
          refinedNpAttrsOf = true;
          bobbin = true;
          ctlGenNullOr = true;
          ctlNpNullOr = true;
          ctlRefinedGenNullOr = true;
          ctlGenAttrsOf = true;
          armedGenNullOr = true;
          armedGenAttrsOf = true;
        };
      };

    # A TAG IS NOT A ROLE: `attrTag`'s `nestedTypes` is its tag set, option records, so a tag NAMED
    # `elemType` (or `left` and `right`) states no element or union, the record reads exactly as its
    # twin with a tag named anything else (its module set), and the identity it holds stays tracked
    test-a-tag-named-for-a-role-states-no-role =
      let
        tagged = tags: imp (t.attrTag (builtins.mapAttrs (_: ty: nixpkgsLib.mkOption { type = ty; }) tags));
      in
      {
        expr = {
          elemTypeTag = keysOf (tagged { elemType = idSub; }).carries;
          leftRightTags =
            keysOf
              (tagged {
                left = idSub;
                right = gt.str;
              }).carries;
          elemTypeTagMoveRefused = moveRefused (tagged { elemType = idSub; }) { elemType.spool = "silk"; } {
            elemType.spool = "satin";
          };
          ctlATag = keysOf (tagged { a = idSub; }).carries;
          ctlATagMoveRefused = moveRefused (tagged { a = idSub; }) { a.spool = "silk"; } {
            a.spool = "satin";
          };
        };
        expected = {
          elemTypeTag = [ "moduleSet" ];
          leftRightTags = [ "moduleSet" ];
          elemTypeTagMoveRefused = true;
          ctlATag = [ "moduleSet" ];
          ctlATagMoveRefused = true;
        };
      };

    # THE WALK READS NO RAW PAYLOAD. A raw nixpkgs record carrying an identity submodule states its
    # element (`statedRoles`) but no position for it: only a gen `recarry` says where an element sits,
    # and the functor payload is what the record offers to MERGE on, not what it carries. So the walk
    # stops at every raw carrying constructor, and a MOVED identity there is SERVED warm,
    # byte-identical to cold, rather than refused. `functionTo`/`attrListOf`/`attrListWith` were
    # walked by a payload rebuild that met the value at the wrong level and aborted uncatchably. The
    # element is nixpkgs' own submodule: gen's is a nesting type, refused by name inside most foreign
    # containers. Live controls: the move IS refused under gen's containers, and under a raw nixpkgs
    # record carrying a MODULE SET (`submodule`, and `addCheck`/`coercedTo` over one), which states
    # it in `getSubModules` and is walked at its own position, with no payload read.
    test-the-walk-reads-no-raw-payload =
      let
        npIdSub = t.submodule idMod;
        a = {
          spool = "silk";
        };
        b = {
          spool = "satin";
        };
        # the edit MOVES the held identity: warm is total and equals cold. `read` applies a
        # `functionTo` value, which has no JSON form.
        moveServed =
          read: ty: v: v':
          let
            base = anchor ++ [
              { options.h = mkOption { type = ty; }; }
              {
                _file = "sb";
                config.h = v;
              }
            ];
            edit = [
              {
                _file = "sm";
                config.h = mkForce v';
              }
            ];
            w = read (warmOf base edit).config;
          in
          ok w && builtins.toJSON w == builtins.toJSON (read (coldOf (base ++ edit)).config);
        served = moveServed (c: c);
        applied = moveServed (c: c // { h = c.h null; });
      in
      {
        expr = {
          listOf = served (t.listOf npIdSub) [ a ] [ b ];
          nonEmptyListOf = served (t.nonEmptyListOf npIdSub) [ a ] [ b ];
          nullOr = served (t.nullOr npIdSub) a b;
          uniq = served (t.uniq npIdSub) a b;
          unique = served (t.unique { message = "u"; } npIdSub) a b;
          addCheckNullOr = served (t.addCheck (t.nullOr npIdSub) (_: true)) a b;
          attrsOf = served (t.attrsOf npIdSub) { p = a; } { p = b; };
          lazyAttrsOf = served (t.lazyAttrsOf npIdSub) { p = a; } { p = b; };
          attrsWith = served (t.attrsWith { elemType = npIdSub; }) { p = a; } { p = b; };
          functionTo = applied (t.functionTo npIdSub) (_: a) (_: b);
          attrListOf = served (t.attrListOf npIdSub) { p = a; } { p = b; };
          attrListWith = served (t.attrListWith { elemType = npIdSub; }) { p = a; } { p = b; };
          # a gen container over a raw wrapper: walked to the wrapper, which stops
          genAttrsOfNullOr = served (gt.attrsOf (t.nullOr npIdSub)) { p = a; } { p = b; };
          # an identity inside an instance (the instance's own gen `listOf` of instances) is not
          # walked: the walk stops at the outer instance's `id_hash` (README, Known boundaries)
          innerInstance =
            served
              (gt.submodule {
                imports = [ idMod ];
                options.inner = mkOption { type = gt.listOf idSub; };
              })
              {
                spool = "o";
                inner = [ a ];
              }
              {
                spool = "o";
                inner = [ b ];
              };
          armedGenNullOr = moveRefused (gt.nullOr npIdSub) a b;
          armedGenListOf = moveRefused (gt.listOf npIdSub) [ a ] [ b ];
          armedNpSubmodule = moveRefused npIdSub a b;
          armedNpAddCheck = moveRefused (t.addCheck npIdSub (_: true)) a b;
          armedNpCoercedTo = moveRefused (t.coercedTo t.str (s: { spool = s; }) npIdSub) "silk" "satin";
        };
        expected = {
          listOf = true;
          nonEmptyListOf = true;
          nullOr = true;
          uniq = true;
          unique = true;
          addCheckNullOr = true;
          attrsOf = true;
          lazyAttrsOf = true;
          attrsWith = true;
          functionTo = true;
          attrListOf = true;
          attrListWith = true;
          genAttrsOfNullOr = true;
          innerInstance = true;
          armedGenNullOr = true;
          armedGenListOf = true;
          armedNpSubmodule = true;
          armedNpAddCheck = true;
          armedNpCoercedTo = true;
        };
      };

    # AN UNROLED KEY THE ROLE'S OWN SPELLING WOULD PUBLISH IS REFUSED BY NAME, catchably: a record
    # stating its element at the top-level `elemType` while `nestedTypes.elemType` holds an option
    # record would lose one of the two at export. Controls: the two spellings agreeing, each alone,
    # and the refusal caught by `tryEval` through the public constructor.
    test-an-unroled-key-the-role-would-publish-is-refused =
      let
        tag = nixpkgsLib.mkOption { type = t.str; };
        box =
          extra:
          base
          // sub3
          // {
            name = "box";
            functor = rel // {
              payload = null;
            };
          }
          // extra;
        clash = box {
          elemType = gt.int;
          nestedTypes.elemType = tag;
        };
      in
      {
        expr = {
          clash = read clash;
          caught = (builtins.tryEval (builtins.seq (imp clash).name null)).success;
          ctlAgree = read (box {
            elemType = gt.int;
            nestedTypes.elemType = gt.int;
          });
          ctlTopOnly = read (box {
            elemType = gt.int;
          });
          ctlTagOnly = read (box {
            nestedTypes.elemType = tag;
          });
          ctlTopBesideOtherKey = read (box {
            elemType = gt.int;
            nestedTypes.weft = tag;
          });
        };
        expected = {
          clash = "refused";
          caught = false;
          ctlAgree = {
            carries = [ "element" ];
            nestedTypes = [ "elemType" ];
          };
          ctlTopOnly = {
            carries = [ "element" ];
            nestedTypes = [ "elemType" ];
          };
          ctlTagOnly = {
            carries = [ ];
            nestedTypes = [ "elemType" ];
          };
          ctlTopBesideOtherKey = {
            carries = [ "element" ];
            nestedTypes = [
              "elemType"
              "weft"
            ];
          };
        };
      };

    # A NESTING RECORD'S `nestedTypes` IS NOT FORCED TO DECIDE ITS IMPORT. Attrset `==` forces the
    # LEFT operand's `type` (its isDerivation test), so the unroled split compares `{ } == …`: a
    # `type` key an author named is not read to answer. Control: the same record over an ordinary
    # unroled key.
    test-a-nesting-records-nestedTypes-type-key-is-not-forced =
      let
        tag = nixpkgsLib.mkOption { type = t.str; };
      in
      {
        expr = {
          typeKeyPlant = nestingDecided {
            type = throw "gen-merge test: a nesting record's nestedTypes.type was forced";
            foo = tag;
          };
          ctlOrdinaryKey = nestingDecided { foo = tag; };
        };
        expected = {
          typeKeyPlant = false;
          ctlOrdinaryKey = false;
        };
      };

    # A FOREIGN RECORD'S `nestedTypes` IS NOT FORCED BY THE PRESENCE TEST EITHER (`statesWrapped`):
    # `{ }` is its left operand, so a `type` key an author named is not read. The record carries the
    # declared opt-out, so no walk reads the key's value either. Control: the same record over an
    # ordinary unroled key.
    test-a-foreign-records-nestedTypes-type-key-is-not-forced-by-the-presence-test =
      let
        tag = nixpkgsLib.mkOption { type = t.str; };
        imports =
          nested:
          let
            e = builtins.tryEval (
              interface.importType (
                base
                // {
                  name = "box";
                  declaresNesting = false;
                  nestedTypes = nested;
                }
              )
              ? imported
            );
          in
          if e.success then e.value else "throws";
      in
      {
        expr = {
          typeKeyPlant = imports {
            type = throw "gen-merge test: a foreign record's nestedTypes.type was forced";
            foo = tag;
          };
          ctlOrdinaryKey = imports { foo = tag; };
        };
        expected = {
          typeKeyPlant = true;
          ctlOrdinaryKey = true;
        };
      };

    # The same guard for a nesting record whose `nestedTypes` is no set at all: its import is decided
    # without comparing it, as it was before the unroled split. Control: an empty `nestedTypes`.
    test-a-nesting-records-non-set-nestedTypes-is-not-compared = {
      expr = {
        notASet = nestingDecided "str";
        ctlEmpty = nestingDecided { };
      };
      expected = {
        notASet = false;
        ctlEmpty = false;
      };
    };

    # THE NESTING PLANE READS WHAT A TYPE CARRIES FROM THE CARRYING SPELLINGS, NEVER FROM ITS PAYLOAD:
    # a stock `listOf` stating its element only at the top-level `elemType` is re-homed as gen's
    # `listOf`, the same container with its `nestedTypes` stripped is not recognised (its payload
    # alone states nothing), and one whose payload offers another element than it states is refused
    # by name (OQ2 arm (b)). Controls: the stock containers, untouched.
    test-the-nesting-plane-reads-no-payload =
      let
        sub = gt.submodule {
          options.x = mkOption {
            type = gt.int;
            default = 0;
          };
        };
        topOnly = (builtins.removeAttrs (t.listOf sub) [ "nestedTypes" ]) // {
          elemType = sub;
        };
        shape = r: if r == null then null else "${r.container}:${r.element.name}";
        value =
          ty: v:
          (evalModuleTree {
            modules = [
              { options.h = mkOption { type = ty; }; }
              { config.h = v; }
            ];
          }).config.h;
      in
      {
        expr = {
          topOnlyRehomed = (interface.importType topOnly) ? rehomed;
          topOnlyHomed = (interface.homedAt "probe" null topOnly).name;
          topOnlyValue = value topOnly [ { x = 1; } ];
          stripped = shape (interface.importedRehome (t.listOf sub // { nestedTypes = { }; }));
          # Shallow: `ok`'s `deepSeq` would throw inside the rehomed element's own record either way.
          disagree =
            (builtins.tryEval (interface.importedRehome (t.listOf t.str // { nestedTypes.elemType = sub; })))
            .success;
          ctlSub = shape (interface.importedRehome (t.listOf sub));
          ctlSubRehomed = (interface.importType (t.listOf sub)) ? rehomed;
          ctlStrRehomed = (interface.importType (t.listOf t.str)) ? rehomed;
        };
        expected = {
          topOnlyRehomed = true;
          topOnlyHomed = "listOf";
          topOnlyValue = [ { x = 1; } ];
          stripped = null;
          disagree = false;
          ctlSub = "listOf:submodule";
          ctlSubRehomed = true;
          ctlStrRehomed = false;
        };
      };

    # A `nestedTypes` KEY NAMING NO GEN ROLE CROSSES VERBATIM, as a nixpkgs type keeps it: an imported
    # record re-publishes every key its roles did not consume, beside the role's own spelling, and
    # its roles are unchanged. The identity walk is blind inside those keys (README, Known
    # boundaries).
    test-a-nestedTypes-key-naming-no-role-crosses-verbatim =
      let
        crossed =
          d:
          let
            e = imp d;
          in
          {
            nestedTypes = keysOf e.nestedTypes;
            verbatim = builtins.all (
              k:
              (e.nestedTypes.${k}.type or e.nestedTypes.${k}).name
              == (d.nestedTypes.${k}.type or d.nestedTypes.${k}).name
            ) (keysOf d.nestedTypes);
            carries = keysOf (e.carries or { });
          };
      in
      {
        expr = {
          coercedTo = crossed (t.coercedTo t.int toString t.str);
          coercedToSub = crossed (t.coercedTo t.str (s: { spool = s; }) (t.submodule idMod));
          freeform = crossed (t.submodule { freeformType = t.attrsOf t.str; });
          attrTag = crossed (t.attrTag { a = nixpkgsLib.mkOption { type = t.str; }; });
          attrTagElemType = crossed (t.attrTag { elemType = nixpkgsLib.mkOption { type = t.str; }; });
          authored = crossed (
            nixpkgsLib.mkOptionType {
              name = "loom";
              check = _: true;
              nestedTypes.weft = t.str;
            }
          );
          ctlListOf = crossed (t.listOf t.str);
          ctlEither = crossed (t.either t.str t.int);
        };
        expected = {
          coercedTo = {
            nestedTypes = [
              "coercedType"
              "finalType"
            ];
            verbatim = true;
            carries = [ ];
          };
          coercedToSub = {
            nestedTypes = [
              "coercedType"
              "finalType"
            ];
            verbatim = true;
            carries = [ "moduleSet" ];
          };
          freeform = {
            nestedTypes = [ "freeformType" ];
            verbatim = true;
            carries = [ "moduleSet" ];
          };
          attrTag = {
            nestedTypes = [ "a" ];
            verbatim = true;
            carries = [ ];
          };
          attrTagElemType = {
            nestedTypes = [ "elemType" ];
            verbatim = true;
            carries = [ ];
          };
          authored = {
            nestedTypes = [ "weft" ];
            verbatim = true;
            carries = [ ];
          };
          ctlListOf = {
            nestedTypes = [ "elemType" ];
            verbatim = true;
            carries = [ "element" ];
          };
          ctlEither = {
            nestedTypes = [
              "left"
              "right"
            ];
            verbatim = true;
            carries = [ "alternatives" ];
          };
        };
      };
  };
}
