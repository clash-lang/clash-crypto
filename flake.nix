{
  description = "A flake enabling tooling for clash-crypto";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    ecpprog.url = "github:diegodiv/ecpprog";
    ghc-typelits-proof-assist.url = "git+ssh://git@github.com/QBayLogic/ghc-typelits-proof-assist?ref=main";
  };
  outputs = { self, nixpkgs, flake-utils, ecpprog, ghc-typelits-proof-assist, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system};
          serialportSrc = pkgs.fetchFromGitHub {
            owner = "standardsemiconductor";
            repo = "serialport";
            rev = "ce42a5afebb55d2e2e84be7f5386d69c343e3942";
            sha256 = "sha256-oBG8DylFwzUu212AiNOg2x+D1jmI2hAvMJQT0F8wWlE=";
          };
          clashCompilerSrc = pkgs.fetchFromGitHub {
            owner = "clash-lang";
            repo = "clash-compiler";
            rev = "7bf85bfbdb6561c068f99ec5f346d1b5092a011b";
            sha256 = "sha256-uiXDG8S5eJrQvwetU0YlAKu1C5RDFoW/3/j77nM0lYw=";
          };

          inherit (pkgs.haskell.lib) dontCheck doJailbreak markUnbroken;
          overlay = final: prev: {
            clash-prelude = prev.callCabal2nix "clash-prelude"
              (clashCompilerSrc + "/clash-prelude") { };
            clash-prelude-hedgehog = prev.callCabal2nix "clash-prelude-hedgehog"
              (clashCompilerSrc + "/clash-prelude-hedgehog") { };
            clash-lib = prev.callCabal2nix "clash-lib"
              (clashCompilerSrc + "/clash-lib") { };
            clash-ghc = prev.callCabal2nix "clash-ghc"
              (clashCompilerSrc + "/clash-ghc") { };
            serialport = dontCheck (prev.callCabal2nix "serialport" serialportSrc { });
            clash-crypto = final.callCabal2nix "clash-crypto" ./. { };
            ghc-typelits-proof-assist = doJailbreak (dontCheck (prev.callCabal2nix "ghc-typelits-proof-assist" ghc-typelits-proof-assist.outPath { }));
          };
          myHsPkgs = pkgs.haskell.packages.ghc9101.extend overlay;
      in
      {
        devShells.default = myHsPkgs.shellFor {
          name = "GHC 9.10.1";
          packages = p: [ p.clash-crypto ];
          inputsFrom = [];
          shellHook = ''
            SHAKEPATH=`cabal list-bin clash-crypto:shake`
            export PATH="$(dirname $SHAKEPATH):$PATH:$(dirname $SHAKEPATH)"

            export OCAML_VERSION=${pkgs.ocaml-ng.ocamlPackages_4_09.ocaml.version}
            export OPAMROOT=$(pwd)/.opam-local
            mkdir -p $OPAMROOT
            export OPAMYES=true # Auto-answer yes to prompts

            if [ ! -d "$OPAMROOT/default" ]; then
              opam init --bare --disable-sandboxing --auto-setup
              # Create a switch for the current OCaml version
              opam switch create default $OCAML_VERSION
            fi

            eval $(opam env)
          '';          nativeBuildInputs =
            with pkgs; [
              gnumake yosys nextpnr trellis ocaml-ng.ocamlPackages_4_09.ocaml opam gmp pkg-config
              coq_8_13
            ] ++
            (with myHsPkgs; [ cabal-install haskell-language-server ])
            ++ [ecpprog.defaultPackage.${system}]
          ;
        };
        packages.default = dontCheck myHsPkgs.clash-crypto;
      });
}
