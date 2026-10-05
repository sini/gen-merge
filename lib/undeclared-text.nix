# The undeclared-option refusal's text beyond its head: nixpkgs' `Did you mean` suggestion and the
# pretty-printed definition value (`checkUnmatched` in nixpkgs `lib/modules.nix`, `showDefs` in
# `lib/options.nix`). Every binding here is read only inside the refusal's `throw`, so none is forced
# on a success path.
#
# The bindings marked "nixpkgs, verbatim" are ported from nixpkgs `lib/` (a7868a7), with `lib.*`
# helpers spelled as builtins:
#
#   Copyright (c) 2003-2026 Eelco Dolstra and the Nixpkgs/NixOS contributors
#
#   Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
#   associated documentation files (the "Software"), to deal in the Software without restriction,
#   including without limitation the rights to use, copy, modify, merge, publish, distribute,
#   sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
#   furnished to do so, subject to the following conditions:
#
#   The above copyright notice and this permission notice shall be included in all copies or
#   substantial portions of the Software.
#
#   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
#   NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
#   NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES
#   OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
#   CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
{
  prelude,
  showDefLine,
  escapeIdentifier,
}:
let
  inherit (builtins)
    addErrorContext
    attrNames
    concatStringsSep
    elem
    elemAt
    filter
    genList
    isAttrs
    isFloat
    isInt
    isList
    isPath
    isString
    length
    map
    mapAttrs
    replaceStrings
    sort
    split
    stringLength
    substring
    tryEval
    ;
  inherit (prelude) isFunction functionArgs;

  min = x: y: if x < y then x else y;
  take = n: l: genList (elemAt l) (min n (length l));

  # nixpkgs `lib.strings.levenshtein`, verbatim.
  levenshtein =
    a: b:
    let
      arr = genList (i: genList (j: dist i j) (stringLength b + 1)) (stringLength a + 1);
      d = x: y: elemAt (elemAt arr x) y;
      dist =
        i: j:
        let
          c = if substring (i - 1) 1 a == substring (j - 1) 1 b then 0 else 1;
        in
        if j == 0 then
          i
        else if i == 0 then
          j
        else
          min (min (d (i - 1) j + 1) (d i (j - 1) + 1)) (d (i - 1) (j - 1) + c);
    in
    d (stringLength a) (stringLength b);

  # nixpkgs `lib.strings.commonPrefixLength`, verbatim.
  commonPrefixLength =
    a: b:
    let
      m = min (stringLength a) (stringLength b);
      go =
        i:
        if i >= m then
          m
        else if substring i 1 a == substring i 1 b then
          go (i + 1)
        else
          i;
    in
    go 0;

  # nixpkgs `lib.strings.commonSuffixLength`, verbatim.
  commonSuffixLength =
    a: b:
    let
      m = min (stringLength a) (stringLength b);
      go =
        i:
        if i >= m then
          m
        else if substring (stringLength a - i - 1) 1 a == substring (stringLength b - i - 1) 1 b then
          go (i + 1)
        else
          i;
    in
    go 0;

  # nixpkgs `lib.strings.levenshteinAtMost`, verbatim. It is NOT `levenshtein a b <= k`: when the
  # common prefix and suffix overlap (`"abaa"`, `"aabaa"`) the infix strip goes negative and it answers
  # false at distance 1. nixpkgs filters the 100-or-more candidate case with it, so parity ports it.
  levenshteinAtMost =
    let
      infixDifferAtMost1 = x: y: stringLength x <= 1 && stringLength y <= 1;

      # The two strings stripped by their common prefix and suffix differ by at most two edits only if
      # those edits sit at the start or the end, the middle unchanged.
      infixDifferAtMost2 =
        x: y:
        let
          xlen = stringLength x;
          ylen = stringLength y;
          # called only with |x| >= |y| and |x| - |y| <= 2
          diff = xlen - ylen;

          xinfix = substring 1 (xlen - 2) x;
          yinfix = substring 1 (ylen - 2) y;

          xdelr = substring 0 (xlen - 1) x;
          xdell = substring 1 (xlen - 1) x;
          ydelr = substring 0 (ylen - 1) y;
          ydell = substring 1 (ylen - 1) y;
        in
        if diff == 2 then
          xinfix == y
        else if diff == 1 then
          xinfix == ydelr || xinfix == ydell
        else
          xinfix == yinfix || xdelr == ydell || xdell == ydelr;

    in
    k:
    if k <= 0 then
      a: b: a == b
    else
      let
        f =
          a: b:
          let
            alen = stringLength a;
            blen = stringLength b;
            prelen = commonPrefixLength a b;
            suflen = commonSuffixLength a b;
            presuflen = prelen + suflen;
            ainfix = substring prelen (alen - presuflen) a;
            binfix = substring prelen (blen - presuflen) b;
          in
          if alen < blen then
            f b a
          else if alen - blen > k then
            false
          else if k == 1 then
            infixDifferAtMost1 ainfix binfix
          else if k == 2 then
            infixDifferAtMost2 ainfix binfix
          else
            levenshtein ainfix binfix <= k;
      in
      f;

  # nixpkgs `lib.lists.sortOn`, verbatim: stable on the key.
  sortOn =
    f: list:
    map (x: elemAt x 1) (
      sort (a: b: elemAt a 0 < elemAt b 0) (
        map (x: [
          (f x)
          x
        ]) list
      )
    );

  # The `Did you mean` paragraph of nixpkgs' `checkUnmatched`. `candidates` are the sibling option
  # names (the caller has taken `_module` out at a root); `shown` renders one as the option path
  # nixpkgs prints. Below 100 candidates every one is ranked and the 3 nearest kept, however far;
  # from 100, only those `levenshteinAtMost 2`.
  suggestion =
    shown: name: candidates:
    let
      near = if length candidates < 100 then candidates else filter (levenshteinAtMost 2 name) candidates;
      top = take 3 (sortOn (levenshtein name) near);
      n = length top;
      q = s: "`${shown s}'";
    in
    if n == 0 then
      ""
    else if n == 1 then
      "\n\nDid you mean ${q (elemAt top 0)}?"
    else
      "\n\nDid you mean ${
        concatStringsSep ", " (genList (i: q (elemAt top i)) (n - 1))
      } or ${q (elemAt top (n - 1))}?";

  # nixpkgs `lib.generators.withRecursion { depthLimit = 10; throwOnDepthLimit = false; }`, verbatim:
  # a value nested deeper than 10 reads as the string "<unevaluated>".
  limitDepth =
    let
      specialAttrs = [
        "__functor"
        "__functionArgs"
        "__toString"
        "__pretty"
      ];
      transform = depth: if depth > 10 then (_: "<unevaluated>") else (x: x);
      mapAny =
        depth: v:
        let
          evalNext = x: mapAny (depth + 1) (transform (depth + 1) x);
        in
        if isAttrs v then
          mapAttrs (name: if elem name specialAttrs then (x: x) else evalNext) v
        else if isList v then
          map evalNext v
        else
          transform (depth + 1) v;
    in
    mapAny 0;

  # nixpkgs `lib.generators.toPretty { }`, verbatim (multiline, no `__pretty`).
  toPretty =
    let
      go =
        indent: v:
        let
          introSpace = "\n${indent}  ";
          outroSpace = "\n${indent}";
        in
        if isInt v then
          toString v
        else if isFloat v then
          builtins.toJSON v
        else if isString v then
          let
            lines = filter (v: !isList v) (split "\n" v);
            escapeSingleline = replaceStrings [ "\\" "\"" "\${" ] [ "\\\\" "\\\"" "\\\${" ];
            escapeMultiline = replaceStrings [ "\${" "''" ] [ "''\${" "'''" ];
            escapedLines = map escapeMultiline lines;
            lastLine = elemAt escapedLines (length escapedLines - 1);
          in
          if length lines > 1 then
            "''"
            + introSpace
            + concatStringsSep introSpace (take (length escapedLines - 1) escapedLines)
            + (if lastLine == "" then outroSpace else introSpace + lastLine)
            + "''"
          else
            "\"" + concatStringsSep "\\n" (map escapeSingleline lines) + "\""
        else if true == v then
          "true"
        else if false == v then
          "false"
        else if null == v then
          "null"
        else if isPath v then
          toString v
        else if isList v then
          if v == [ ] then
            "[ ]"
          else
            "[" + introSpace + concatStringsSep introSpace (map (go (indent + "  ")) v) + outroSpace + "]"
        else if isFunction v then
          let
            fna = functionArgs v;
            showFnas = concatStringsSep ", " (
              map (name: if fna.${name} then name + "?" else name) (attrNames fna)
            );
          in
          if fna == { } then "<function>" else "<function, args: {${showFnas}}>"
        else if isAttrs v then
          if v == { } then
            "{ }"
          else if v ? type && v.type == "derivation" then
            "<derivation ${v.name or "???"}>"
          else
            "{"
            + introSpace
            + concatStringsSep introSpace (
              map (
                name:
                "${escapeIdentifier name} = ${
                  addErrorContext "while evaluating an attribute `${name}`" (go (indent + "  ") v.${name})
                };"
              ) (attrNames v)
            )
            + outroSpace
            + "}"
        else
          abort "undeclared-text.toPretty: should never happen (v = ${v})";
    in
    go "";

  # nixpkgs `showDefs [ def ]`, verbatim: the value is pretty-printed under `tryEval` and omitted when
  # that fails; a multi-line print goes on its own lines, the first 5 of them, then `...`. `tryEval`
  # catches a `throw` or a failed `assert` in the value, not an `abort`, a missing attribute, a type
  # error, infinite recursion or a missing import: those abort the refusal, as in nixpkgs.
  showDef =
    def:
    let
      prettyEval = tryEval (toPretty (limitDepth def.value));
      lines = filter (v: !isList v) (split "\n" prettyEval.value);
      value = concatStringsSep "\n    " (take 5 lines ++ (if length lines > 5 then [ "..." ] else [ ]));
      result =
        if !prettyEval.success then
          ""
        else if length lines > 1 then
          ":\n    " + value
        else
          ": " + value;
    in
    showDefLine def result;
in
{
  inherit suggestion showDef;
}
