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
    # is a warm read that is total and equals cold. The controls state their position (a gen wrapper,
    # a raw nixpkgs wrapper, a refinement over a gen base, which keeps the base's `recarry`) and are
    # walked as before.
    test-the-identity-walk-stops-where-no-position-is-stated = {
      expr = {
        refinedNpNullOr = hold (refinedLike (t.nullOr idSub)) { spool = "silk"; };
        refinedNpUniq = hold (refinedLike (t.uniq idSub)) { spool = "silk"; };
        spindle = hold (spindle idSub) { spool = "silk"; };
        importedNpNullOr = hold (imp (t.nullOr idSub)) { spool = "silk"; };
        importedNpUniq = hold (imp (t.uniq idSub)) { spool = "silk"; };
        refinedNpAttrsOf = hold (refinedLike (t.attrsOf idSub)) { a.spool = "silk"; };
        bobbin = hold (bobbin idSub) { a.spool = "silk"; };
        ctlGenNullOr = hold (gt.nullOr idSub) { spool = "silk"; };
        ctlNpNullOr = hold (t.nullOr idSub) { spool = "silk"; };
        ctlRefinedGenNullOr = hold (refinedLike (gt.nullOr idSub)) { spool = "silk"; };
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
  };
}
