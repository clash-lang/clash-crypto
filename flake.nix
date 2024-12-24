{
  description = "A flake enabling tooling for clash-crypto";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    clash-compiler.url = "github:clash-lang/clash-compiler/dd/nix-update";
  };
  outputs = { self, nixpkgs, flake-utils, clash-compiler, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = clash-compiler.inputs.nixpkgs.legacyPackages.${system};
          inherit (pkgs.haskell.lib) dontCheck doJailbreak markUnbroken;
          overlay = final: prev: {
            clash-cores = clash-compiler.packages.${system}.clash-cores;
            clash-prelude = clash-compiler.packages.${system}.clash-prelude;
            clash-prelude-hedgehog = clash-compiler.packages.${system}.clash-prelude-hedgehog;
            clash-lib = clash-compiler.packages.${system}.clash-lib;
            clash-ghc = clash-compiler.packages.${system}.clash-ghc;
            cabal-install = nixpkgs.legacyPackages.${system}.cabal-install;
            serialport = doJailbreak (prev.callHackage "serialport" "0.5.6" { });
          };
          # TODO: refer dynamically to the right ghc version (using clash-compiler's default).
          # Might require some changes on clash-compiler's flake.
          myHsPkgs = (pkgs.haskell.packages.ghc910.extend overlay).extend
            (pkgs.haskell.lib.compose.packageSourceOverrides {
              clash-crypto = ./.;
            });
      in
      {
        devShells.default = myHsPkgs.shellFor {
          packages = p: [ p.clash-crypto ];
          inputsFrom = [
            clash-compiler.packages.${system}.clash-lib.env
            clash-compiler.packages.${system}.clash-ghc.env
          ];
          nativeBuildInputs =
            with pkgs; [
              gnumake yosys nextpnr
            ] ++
            (with myHsPkgs; [ cabal-install ])
          ;
        };
      });
}
