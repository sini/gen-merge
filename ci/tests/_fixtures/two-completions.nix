# The forms of `ci/tests/two-completions.nix` and its error-plane half (`ci/tests-error-two-completions.nix`):
# one `mkType` leaf record, completed by `defineType` once and declared N times, completed twice, copied after its
# completion, re-completed, derived, mixed with its raw self, nested, and the import arm's records stating the
# foreign `check` (den-hoag-oqqa5). `gen` declares on gen's engine, `npe` on nixpkgs' over the same types.
{ genMerge, nixpkgsLib }:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  np = nl.types;
  inherit (builtins) isInt head;
  force = v: builtins.deepSeq v v;
in
rec {
  inherit gt np force;
  gen =
    ts: v:
    force
      (gm.evalModuleTree { } (map (t: { options.x = gm.mkOption { type = t; }; }) ts ++ [ { x = v; } ]))
      .config.x;
  npe =
    ts: v:
    force
      (nl.evalModules {
        modules = map (t: { options.x = nl.mkOption { type = t; }; }) ts ++ [ { x = v; } ];
      }).config.x;
  # the served value, or REFUSED for a catchable refusal (an abort is never caught: those are error-plane cells)
  verdict =
    v:
    let
      r = builtins.tryEval (force v);
    in
    if r.success then r.value else "REFUSED";
  vf = v: if isInt v then null else "not an int";
  no4 = v: if v == 4 then "no" else null;
  m = gt.mkType {
    name = "nm";
    verify = vf;
  };
  md = m // {
    description = "d";
  };
  T = gt.defineType m;
  T' = gt.defineType m;
  T'' = gt.defineType m;
  Tc = gt.defineType md;
  Tc2 = gt.defineType (m // { description = "d"; });
  C = T // {
    description = "d";
  };
  V = T // {
    verify = no4;
  };
  Rd = gt.defineType C;
  Dx = gt.deriveType { } "x" T;
  Dx' = gt.deriveType { } "x" T;
  mi = gt.mkType {
    name = "int";
    verify = vf;
  };
  Ti = gt.defineType mi;
  Ti' = gt.defineType mi;
  Hz = gt.defineType (m // { verify = no4; });
  nv = gt.mkType { name = "nv"; };
  mD = gt.mkType {
    name = "nm";
    mergeDefs = _loc: defs: (head defs).value;
  };
  # the import arm's records: a stated `check` (and fold) is re-read by the import, never leaf-sealed
  mCM = gt.mkType {
    name = "nm";
    check = isInt;
    merge = _loc: defs: (head defs).value;
  };
  mV2 = gt.mkType {
    name = "nm";
    check = builtins.isList;
    merge = (np.listOf np.int).merge;
  };
  r = {
    name = "nm";
    verify = vf;
  };
  # the forms
  twob = [
    T
    T'
  ];
  twobR = [
    T'
    T
  ];
  two2 = [
    Tc
    Tc2
  ];
  twob3 = [
    T
    T'
    T''
  ];
  hz = [
    T
    Hz
  ];
  TiTi = [
    Ti
    Ti'
  ];
  aoTT2 = [
    (gt.attrsOf T)
    (gt.attrsOf T')
  ];
  loTT2 = [
    (gt.listOf T)
    (gt.listOf T')
  ];
  nvTwob = [
    (gt.defineType nv)
    (gt.defineType nv)
  ];
  mDTwob = [
    (gt.defineType mD)
    (gt.defineType mD)
  ];
  mCMTwob = [
    (gt.defineType mCM)
    (gt.defineType mCM)
  ];
  mV2Twob = [
    (gt.defineType mV2)
    (gt.defineType mV2)
  ];
}
