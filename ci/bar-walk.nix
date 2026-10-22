# THE DOCS WALK of the replacement bar, one file for every stage that reads an option tree (stage 2's
# `nixos-bar-eval.nix`, stage 3's `hm-bar-eval.nix`). Each node is exactly the entry nixpkgs'
# `optionAttrSetToDocList` emits for that option: nixpkgs' own `optionAttrSetToDocList'`, called one option
# at a time with its sub-option recursion cut, so the walk recurses itself, under `tryEval`, and one refusing
# node cannot hide the rest.
#
# A line is `<name>\tok:<sha256 of the entry's JSON>`, or `<name>\terr:<step>\t<route>` where forcing it
# refused; `route` is the JSON path back to it (a key, or null for a `getSubOptions` step), for the `node`
# read. A group whose keys refuse is `<path>.<keys>`, a sub-option set that refuses `<name>.<sub>`.
#
# Two parameters:
#   published  false: every entry the manual's `rawOpts` holds, internal and invisible ones too (stage 2).
#              true: only the entries the manual publishes, `make-options-doc`'s own filter `visible &&
#              !internal` (stage 3: home-manager's docs evaluation makes every config read an `abort`, and
#              an unpublished option's config-reading default is one, which `tryEval` cannot catch).
#   a getSubOptions answering a non-set is no sub-options, as `optionAttrSetToDocList` reads it (two
#   published home-manager options answer a list); a set-answering tree walks exactly as before.
#
# `docsLen` is the conservation read: the length of nixpkgs' own list over the same options, filtered as the
# walk is.
{
  nplib,
  options,
  published,
  route,
}:
let
  one =
    opt:
    builtins.head (
      nplib.optionAttrSetToDocList' [ ] {
        x = opt // {
          type = opt.type // {
            getSubOptions = _: { };
          };
        };
      }
    );
  isOpt = t: nplib.isOption t;
  nameOf = t: nplib.showOption t.loc;
  subsOf =
    t:
    let
      v = t.visible or true;
      shown = if builtins.isBool v then v else v == "transparent";
    in
    if shown then t.type.getSubOptions t.loc else { };
  forced = v: builtins.seq v v;
  walk =
    let
      dot = nplib.concatStringsSep ".";
      err = nm: step: rt: [ "${nm}\terr:${step}\t${builtins.toJSON rt}" ];
      node =
        pre: rt: t:
        let
          o = builtins.tryEval (isOpt t);
        in
        if !o.success then
          err (dot pre) "isopt" rt
        else if o.value then
          let
            e = builtins.tryEval (forced (builtins.toJSON (one t)));
            n = builtins.tryEval (nameOf t);
            nm = if n.success then n.value else dot pre;
            ss = builtins.tryEval (
              let
                x = subsOf t;
              in
              if builtins.isAttrs x then builtins.seq (builtins.attrNames x) x else { }
            );
          in
          (
            if published then
              let
                p = builtins.tryEval ((one t).visible && !(one t).internal);
              in
              if !p.success then
                err nm "pub" rt
              else if !p.value then
                [ ]
              else if e.success then
                [ "${nm}\tok:${builtins.hashString "sha256" e.value}" ]
              else
                err nm "opt" rt
            else if e.success then
              [ "${nm}\tok:${builtins.hashString "sha256" e.value}" ]
            else
              err nm "opt" rt
          )
          ++ (if !ss.success then err "${nm}.<sub>" "sub" rt else node pre (rt ++ [ null ]) ss.value)
        else if !(builtins.isAttrs t) then
          [ ]
        else
          let
            ks = builtins.tryEval (builtins.attrNames t);
          in
          if !ks.success then
            err "${dot pre}.<keys>" "keys" rt
          else
            builtins.concatMap (k: node (pre ++ [ k ]) (rt ++ [ k ]) t.${k}) ks.value;
    in
    builtins.concatStringsSep "\n" (node [ ] [ ] options);
  # The node `route` names, reached by the steps the walk took, and the step that refused there forced.
  node =
    let
      rt = builtins.fromJSON route;
      step = builtins.head rt;
      at = builtins.foldl' (t: k: if k == null then subsOf t else t.${k}) options (builtins.tail rt);
    in
    if step == "isopt" then
      isOpt at
    else if step == "opt" then
      forced (builtins.toJSON (one at))
    else if step == "pub" then
      (one at).visible && !(one at).internal
    else if step == "sub" then
      builtins.attrNames (subsOf at)
    else if step == "keys" then
      builtins.attrNames at
    else
      throw "bar-walk: unknown node step ${builtins.toJSON step}";
in
{
  inherit walk node;
  docsLen = builtins.length (
    builtins.filter (o: !published || (o.visible && !o.internal)) (nplib.optionAttrSetToDocList options)
  );
}
