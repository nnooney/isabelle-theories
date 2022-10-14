{
  description = "Theories written with the Isabelle Proof Assistant";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }: 
    flake-utils.lib.eachDefaultSystem (system:
      let 
        pkgs = import nixpkgs { inherit system; };
      in {
        devShells = pkgs.mkShell {
          buildInputs = with pkgs; [
            isabelle
          ];
        };
      }
    );
}
