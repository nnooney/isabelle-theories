# Isabelle Theories

This repository contains various theories written with the Isabelle proof
assistant.

- `concrete-semantics`: Proofs from the exercises in the book
  [Concrete Semantics](http://concrete-semantics.org/concrete-semantics.pdf)

## Usage with NixOS

Use the Nix flake-based ecosystem for working with this repository.
`nix develop` enters a shell environment with the necessary dependencies
available. It's also possible to automatically enter the development environment
using a tool like `nix-direnv`.

`isabelle jedit` launches the IDE from the command line.
