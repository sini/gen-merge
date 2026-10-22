# Stage 2's cells (den-hoag-fwkzx, `nixos-bar.nix`), run by the shared body `nixos-bar.bash`. Every
# evaluation runs `--readonly-mode`, with the arguments `nixos-bar-eval.nix` takes, in this order.
BAR_FLAGS=(--readonly-mode)
# wargs <read> <route>: one argument per line, a walk read's arguments.
wargs() { printf '%s\n' --argstr cfg docs --argstr read "$1" --argstr route "$2"; }
cells() {
  docsWalk '{"kind":"docs-walk"}' "" wargs
  cell '{"kind":"options"}' options identity --argstr cfg docs --argstr read options --argstr route '[]'
  for c in smallContainer tinyContainer ec2 kde xfce gnome pantheon lapp; do
    cell "{\"kind\":\"toplevel\",\"cfg\":\"$c\"}" toplevel identity --argstr cfg "$c" --argstr read toplevel --argstr route '[]'
  done
}
