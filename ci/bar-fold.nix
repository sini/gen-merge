# The gating oracle of every replacement bar's `--fold` (den-hoag-5ea43): the four shipped bars, run with no
# evaluator, which is the fold's own regime, so a sandboxed check, the same in every CI column. The cells are
# `bar-fold-cells.bash`; this derivation holds their COUNT, with equality, because a run that silently
# collects fewer cells reads exactly like a green.
{ inputs, ... }:
{
  perSystem =
    { pkgs, ... }:
    let
      bars = [
        {
          name = "modules-sh";
          bin = "${import ./modules-sh.nix { inherit pkgs inputs; }}/bin/modules-sh";
          register = ./modules-sh-baseline.jsonl;
        }
        {
          name = "nixos-bar";
          bin = "${import ./nixos-bar.nix { inherit pkgs inputs; }}/bin/nixos-bar";
          register = ./nixos-bar-baseline.jsonl;
        }
        {
          name = "hm-bar";
          bin = "${import ./hm-bar.nix { inherit pkgs inputs; }}/bin/hm-bar";
          register = ./hm-bar-baseline.jsonl;
        }
        {
          name = "fp-bar";
          bin = "${import ./fp-bar.nix { inherit pkgs inputs; }}/bin/fp-bar";
          register = ./fp-bar-baseline.jsonl;
        }
      ];
      cells = 7 * builtins.length bars;
    in
    {
      checks.bar-fold = pkgs.runCommand "gen-merge-bar-fold-cells" { nativeBuildInputs = [ pkgs.jq ]; } ''
        rc=0
        ${pkgs.lib.concatMapStrings (b: ''
          bash ${./bar-fold-cells.bash} ${b.name} ${b.bin} ${b.register} >> cells.out 2>&1 || rc=$?
        '') bars}
        cat cells.out
        n=$(grep -c '^PASS ' cells.out || true)
        ! grep -q '^FAIL ' cells.out || rc=1
        [ "$rc" = 0 ] || { echo "bar-fold: a cell failed"; exit 1; }
        [ "$n" = ${toString cells} ] || { echo "bar-fold: collected $n cells, want exactly ${toString cells}"; exit 1; }
        echo "bar-fold: ${toString cells} cells" > $out
      '';
    };
}
