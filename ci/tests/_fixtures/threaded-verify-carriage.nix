# A `verify` read on the settled value through a threaded nixpkgs wrapper and at the meet (den-hoag-x7qe5, owner
# Ruling 8 in ADR-0039: a `verify` is a refinement on the option node's settled value, never on its definition edges).
# Read by the value cells (`../threaded-verify-carriage.nix`) and the refusal cells (`../../tests-error.nix`,
# `threaded-verify-carriage`).
#
# `cells` holds one declaration list per cell; `run engine name` forces the option `x` deeply. `engine` is "gen"
# (gen-merge's `evalModuleTree` over gen's records), "np" (nixpkgs' `evalModules` over the same records) or "twin"
# (nixpkgs' `evalModules` over nixpkgs' own types, every door the identity), the reference a served cell equals.
#
# The shapes: a raw `// { verify }` copy of a gen submodule under nixpkgs' `uniq` (`np.uniq` forwards the thread
# marker to its element, and the copy answered it with its base); the mkOptionType door over a `both` copy
# (`np.addCheck` then `// { verify }`) met with a plain declaration (the meet read the combining fold's verify per
# definition); a wrapper that states its own check over a threaded copy (the check is the wrapper's and is kept);
# door copies declared last in nixpkgs' pairwise fold (each later step re-meets the record the meet returned); and a
# met record below two threaded wrappers (the recursive arm closes it).
{ gm, nl }:
let
  np = nl.types;
  # the verifies: `pSub` rejects a = 2; `verMem` reads a member (b = 5 is rejected); `atLeastTwo` reads a list
  pSub = v: !(builtins.isAttrs v) || !(v ? a) || !(builtins.isInt v.a) || v.a != 2;
  ver = p: v: if p v then null else "the verify rejects a = 2";
  verMem = v: if builtins.isAttrs v && v.b == 5 then "the verify rejects b = 5" else null;
  atLeastTwo =
    v: if !(builtins.isList v) || builtins.length v >= 2 then null else "the verify wants two elements";
  # the wrapper's own check: rejects a = 3
  q = v: !(builtins.isAttrs v) || (v.a or 0) != 3;
  cellsFor =
    twin:
    let
      K = if twin then np else gm.types;
      mkO = if twin then nl.mkOption else gm.mkOption;
      door = d: if twin then (t: t) else d;
      mkOT = door gm.mkOptionType;
      tMkOT = door gm.types.mkOptionType;
      defT = door gm.types.defineType;
      sub = K.submodule {
        key = "threaded-verify-carriage-sub";
        options.a = mkO {
          type = K.int;
          default = 0;
        };
        options.b = mkO {
          type = K.int;
          default = 0;
        };
      };
      copy = sub // {
        verify = ver pSub;
      };
      eith = K.either sub K.str;
      eCopy = eith // {
        verify = ver pSub;
      };
      both = np.addCheck eith pSub // {
        verify = ver pSub;
      };
      au = e: np.addCheck (np.uniq e) q;
      ov =
        e:
        let
          u = np.uniq e;
        in
        u // { check = v: u.check v && q v; };
      opt = t: { options.x.type = t; };
    in
    {
      # np.uniq over a raw verify copy, and twice
      uniqCopy = [
        (opt (np.uniq copy))
        { x.a = 2; }
      ];
      uniqCopyOk = [
        (opt (np.uniq copy))
        { x.a = 1; }
      ];
      uniqUniqCopy = [
        (opt (np.uniq (np.uniq copy)))
        { x.a = 2; }
      ];
      # laziness: reading `.a` forces no other member
      uniqCopyLazy = [
        (opt (np.uniq copy))
        {
          x.a = 1;
          x.b = throw "threaded-verify-carriage: b forced";
        }
      ];
      # the mkOptionType door over a both-copy, declared before a plain np.attrsOf, one module-function definition
      doorBoth = [
        (opt (np.attrsOf (mkOT both)))
        (opt (np.attrsOf eith))
        { x.k = { ... }: { a = 2; }; }
      ];
      doorBothOk = [
        (opt (np.attrsOf (mkOT both)))
        (opt (np.attrsOf eith))
        { x.k = { ... }: { a = 1; }; }
      ];
      typesDoorBoth = [
        (opt (np.attrsOf (tMkOT both)))
        (opt (np.attrsOf eith))
        { x.k = { ... }: { a = 2; }; }
      ];
      # the both-copy declared last: its own check refuses per definition
      doorBothLast = [
        (opt (np.attrsOf eith))
        (opt (np.attrsOf (mkOT both)))
        { x.k = { ... }: { a = 2; }; }
      ];
      # gen attrsOf, a raw copy third of three
      rawThird = [
        (opt (K.attrsOf eith))
        (opt (K.attrsOf eith))
        (opt (K.attrsOf eCopy))
        { x.k = { ... }: { a = 2; }; }
      ];
      # the mirror: a verify that reads the merged list admits what one definition alone would not
      listMirror = [
        (opt (K.attrsOf (K.listOf K.int)))
        (opt (K.attrsOf (K.listOf K.int)))
        (opt (K.attrsOf (K.listOf K.int // { verify = atLeastTwo; })))
        { x.k = [ 1 ]; }
        { x.k = [ 2 ]; }
      ];
      # a member-reading verify: through defineType under np.uniq, and raw third of three
      uniqDefineMember = [
        (opt (np.uniq (defT (sub // { verify = verMem; }))))
        { x.a = 1; }
      ];
      rawThirdMember = [
        (opt (K.attrsOf eith))
        (opt (K.attrsOf eith))
        (opt (K.attrsOf (eith // { verify = verMem; })))
        { x.k.a = 1; }
      ];
      rawThirdMemberBad = [
        (opt (K.attrsOf eith))
        (opt (K.attrsOf eith))
        (opt (K.attrsOf (eith // { verify = verMem; })))
        { x.k.b = 5; }
      ];
      # the wrapper's own check over a threaded copy (q rejects a = 3), and over a plain element
      checkOverUniqCopy = [
        (opt (au copy))
        { x.a = 3; }
      ];
      checkOverUniqCopyOk = [
        (opt (au copy))
        { x.a = 1; }
      ];
      overlayOverUniqCopy = [
        (opt (ov copy))
        { x.a = 3; }
      ];
      checkOverUniqCopyInAttrs = [
        (opt (np.attrsOf (au copy)))
        { x.k.a = 3; }
      ];
      checkOverUniqDoorCopy = [
        (opt (au (mkOT copy)))
        { x.a = 3; }
      ];
      checkOverUniqPlain = [
        (opt (au sub))
        { x.a = 3; }
      ];
      overlayOverUniqPlain = [
        (opt (ov sub))
        { x.a = 3; }
      ];
      checkOverUniqPlainInAttrs = [
        (opt (np.attrsOf (au sub)))
        { x.k.a = 3; }
      ];
      # the wrapper's own check on the wrapper the in-place close rebuilds: np.uniq over it
      uniqCheckOverUniqCopy = [
        (opt (np.uniq (au copy)))
        { x.a = 3; }
      ];
      uniqCheckOverUniqDoorCopy = [
        (opt (np.uniq (au (mkOT copy))))
        { x.a = 3; }
      ];
      uniqCheckOverUniqCopyVerify = [
        (opt (np.uniq (au copy)))
        { x.a = 2; }
      ];
      uniqCheckOverUniqCopyOk = [
        (opt (np.uniq (au copy)))
        { x.a = 1; }
      ];
      # door copies declared last of four (nixpkgs' pairwise fold re-meets the met record), and one last
      twoDoorCopiesLast = [
        (opt eith)
        (opt eith)
        (opt (mkOT eCopy))
        (opt (mkOT eCopy))
        { x.a = 2; }
      ];
      twoDoorCopiesLastOk = [
        (opt eith)
        (opt eith)
        (opt (mkOT eCopy))
        (opt (mkOT eCopy))
        { x.a = 1; }
      ];
      oneDoorCopyLast = [
        (opt eith)
        (opt eith)
        (opt eith)
        (opt (mkOT eCopy))
        { x.a = 2; }
      ];
      # a met record carrying a door copy's member-reading verify, through np.uniq, under np.attrsOf
      attrsUniqDoorMember = [
        (opt (np.attrsOf (np.uniq eith)))
        (opt (np.attrsOf (np.uniq eith)))
        (opt (np.attrsOf (np.uniq (mkOT (eith // { verify = verMem; })))))
        { x.k.b = 5; }
      ];
      # a met record through two threaded np.uniq, the door copy third of three and first of three
      uniqUniqDoorCopyThird = [
        (opt (np.uniq (np.uniq eith)))
        (opt (np.uniq (np.uniq eith)))
        (opt (np.uniq (np.uniq (mkOT eCopy))))
        { x.a = 2; }
      ];
      uniqUniqDoorCopyFirst = [
        (opt (np.uniq (np.uniq (mkOT eCopy))))
        (opt (np.uniq (np.uniq eith)))
        (opt (np.uniq (np.uniq eith)))
        { x.a = 2; }
      ];
      uniqUniqDoorCopyThirdOk = [
        (opt (np.uniq (np.uniq eith)))
        (opt (np.uniq (np.uniq eith)))
        (opt (np.uniq (np.uniq (mkOT eCopy))))
        { x.a = 1; }
      ];
    };
  # the option `x` of a cell, on one engine (`opt` states the type only; the engine's own mkOption is added here)
  config =
    engine: name:
    let
      ms = (cellsFor (engine == "twin")).${name};
      withOpt = map (
        m:
        if m ? options then
          { options.x = (if engine == "gen" then gm.mkOption else nl.mkOption) { type = m.options.x.type; }; }
        else
          m
      ) ms;
    in
    if engine == "gen" then
      (gm.evalModuleTree { } withOpt).config
    else
      (nl.evalModules { modules = withOpt; }).config;
  san =
    v:
    if builtins.isFunction v then
      "<function>"
    else if builtins.isAttrs v then
      builtins.mapAttrs (_: san) v
    else if builtins.isList v then
      map san v
    else
      v;
in
{
  inherit config;
  # forced deeply: the value as served, or the throw
  run =
    engine: name:
    let
      x = (config engine name).x;
    in
    builtins.deepSeq x (san x);
}
