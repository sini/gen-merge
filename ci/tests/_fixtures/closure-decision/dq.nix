{ options, ... }: {
  imports =
    let
      r = builtins.tryEval (options ? a);
    in
    if r.success && r.value then [ ] else [ ];
}
