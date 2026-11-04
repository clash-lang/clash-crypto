{
  description = "A flake enabling tooling for clash-crypto";
  nixConfig = {
    extra-substituters = [ "https://clash-lang.cachix.org" ];
    extra-trusted-substituters = [ "https://clash-lang.cachix.org" ];
    extra-trusted-public-keys = [ "clash-lang.cachix.org-1:/2N1uka38B/heaOAC+Ztd/EWLmF0RLfizWgC5tamCBg=" ];
  };
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs?ref=nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    nix-filter.url = "github:numtide/nix-filter";
    ecpprog.url = "github:diegodiv/ecpprog";
    clash-compiler = {
      url = "github:clash-lang/clash-compiler";
      flake = false;
    };
    ghc-typelits-proof-assist.url = "github:clash-lang/ghc-typelits-proof-assist";
    ghc-tcplugin-api = { url = "github:sheaf/ghc-tcplugin-api"; flake = false; };
    ghc-typelits-natnormalise = { url = "github:clash-lang/ghc-typelits-natnormalise"; flake = false; };
    ghc-typelits-knownnat = { url = "github:clash-lang/ghc-typelits-knownnat"; flake = false; };
    ghc-typelits-extra = { url = "github:clash-lang/ghc-typelits-extra"; flake = false; };
    checked-literals = { url = "github:clash-lang/checked-literals"; flake = false; };
  };
  outputs =
  { self
  , nixpkgs
  , flake-utils
  , nix-filter
  , ecpprog
  , clash-compiler
  , ghc-typelits-proof-assist
  , ghc-tcplugin-api
  , ghc-typelits-natnormalise
  , ghc-typelits-knownnat
  , ghc-typelits-extra
  , checked-literals
  , ...
  }:
    flake-utils.lib.eachDefaultSystem (system:
      let ghc-version = "ghc9141";
          config = import ./build-config.nix;
          src = nix-filter.lib {
            root = self;
            exclude = [
              (nix-filter.lib.matchExt "nix")
              "flake.lock"
            ];
          };
          ecpprogOverlay = _: _: {
            ecpprog = ecpprog.defaultPackage.${system};
          };
          extensions = [ ecpprogOverlay ];
          pkgs0 = nixpkgs.legacyPackages.${system};
          pkgs = pkgs0.extend (pkgs0.lib.composeManyExtensions extensions);

          inherit (pkgs) lib;
          clashLib = import ./nix/clash.nix { inherit pkgs lib; };
          inherit (pkgs.haskell.lib) dontCheck doJailbreak overrideCabal markUnbroken;

          hsPkgs0 = pkgs.haskell.packages.${ghc-version};
          overlay914 = import ./nix/overlay-ghc914.nix { inherit pkgs; };
          overlay = final: prev: {
            clash-prelude = dontCheck (prev.callCabal2nix "clash-prelude"
              (clash-compiler + "/clash-prelude") { });
            clash-prelude-hedgehog = dontCheck (prev.callCabal2nix "clash-prelude-hedgehog"
              (clash-compiler + "/clash-prelude-hedgehog") { });
            clash-lib = dontCheck (prev.callCabal2nix "clash-lib"
              (clash-compiler + "/clash-lib") { });
            clash-ghc = dontCheck (prev.callCabal2nix "clash-ghc"
              (clash-compiler + "/clash-ghc") { });
            network  = dontCheck (prev.callHackage "network" "3.2.7.0" {});
            checked-literals = dontCheck (prev.callCabal2nix "checked-literals" checked-literals {});
            th-desugar = doJailbreak (prev.callHackage "th-desugar" "1.19" { });
            singletons-th = doJailbreak (prev.callHackage "singletons-th" "3.5.1" { });
            singletons-base = dontCheck (doJailbreak (prev.callHackage "singletons-base" "3.5" { }));
            singletons-base-code-generator = markUnbroken prev.singletons-base-code-generator;
            cabal-add = dontCheck prev.cabal-add;
            statistics = dontCheck prev.statistics;
            fourmolu = dontCheck prev.fourmolu;
            ghc-tcplugin-api = dontCheck (prev.callCabal2nix "ghc-tcplugin-api" ghc-tcplugin-api { });
            ghc-typelits-natnormalise = dontCheck (prev.callCabal2nix "ghc-typelits-natnormalise" ghc-typelits-natnormalise { });
            ghc-typelits-knownnat = dontCheck (prev.callCabal2nix "ghc-typelits-knownnat" ghc-typelits-knownnat { });
            ghc-typelits-extra = doJailbreak (dontCheck (prev.callCabal2nix "ghc-typelits-extra" ghc-typelits-extra { }));
            ghc-typelits-proof-assist = dontCheck (prev.callCabal2nix "ghc-typelits-proof-assist" ghc-typelits-proof-assist.outPath { });
            clash-crypto = (overrideCabal (final.callCabal2nix "clash-crypto" src {}) {
              configureFlags = [
                "--ghc-option=-DHITLT_BAUD=${config.serial-speed}"
              ];
            }).overrideAttrs (_: _: {
              checkFlags = [ "simulation" ];
            });
          };
          hsPkgs1 = hsPkgs0.extend overlay;
          hsPkgs = hsPkgs1.extend overlay914;

          envTools =
            (with pkgs; [ gnumake yosys nextpnr trellis ]) ++
            [ pkgs.ecpprog ] ++
            (with hsPkgs; [ cabal-install ])
            ;
          # Environment that is burned in to the CI runner image. The goal is to
          # alleviate cache.nixos.org a bit, but not over-specify the
          # environment such that the image needs to be updated often.
          ciEnv = pkgs.buildEnv {
            name = "ci-env";
            paths = envTools ++ (with hsPkgs; [
              clash-prelude
              clash-prelude-hedgehog
              clash-lib
              clash-ghc
            ]);
          };
          defaultDevShell = hsPkgs.shellFor {
            name = "GHC 9.14.1";
            packages = p: [ p.clash-crypto ];
            shellHook = ''
              SHAKEPATH=`cabal list-bin clash-crypto:shake`
              export PATH="$(dirname $SHAKEPATH):$PATH:$(dirname $SHAKEPATH)"
            '';
            nativeBuildInputs = envTools;
          };
          opamOverlay = _: prevA: {
            name = prevA.name + " with opam";
            shellHook = prevA.shellHook + ''
              export OCAML_VERSION=${pkgs.ocaml-ng.ocamlPackages_4_09.ocaml.version}
              export OPAMROOT=$(pwd)/.opam-local
              mkdir -p $OPAMROOT

              if [ ! -d "$OPAMROOT/default" ]; then
                opam init --bare --disable-sandboxing --auto-setup
                # Create a switch for the current OCaml version
                opam switch create default $OCAML_VERSION
              fi

              eval $(opam env)
            '';
            nativeBuildInputs = prevA.nativeBuildInputs ++
                    (with pkgs; [ opam gmp pkg-config ]);
          };
          hlsOverlay = _: prevA : {
            name = prevA.name + " with HLS";
            nativeBuildInputs =
              prevA.nativeBuildInputs ++
              (with hsPkgs; [ haskell-language-server ])
              ;
          };

          hitltHsPkgs = hsPkgs.extend (_: prev: { clash-crypto = dontCheck prev.clash-crypto; });
          inherit (import ./nix/hitlt.nix hitltHsPkgs config) hitltBaseArgs hitltTopEntities;
          clashHitlt = k: v:
            clashLib.ecp5.clash (lib.recursiveUpdate hitltBaseArgs v // { name = k; });
          hitlt = builtins.mapAttrs clashHitlt hitltTopEntities;
          hitltUpload = builtins.mapAttrs (n: _:
            { upload = { type = "app"; program = "${hitlt.${n}}/bin/upload"; }; }
          ) hitltTopEntities;
      in
      {
        devShells.default = defaultDevShell;
        devShells.withOpam = defaultDevShell.overrideAttrs opamOverlay;
        devShells.withHLS = defaultDevShell.overrideAttrs hlsOverlay;
        devShells.allFeatures =
          (defaultDevShell.overrideAttrs hlsOverlay).overrideAttrs opamOverlay;
        apps.hitlt = hitltUpload;
        apps.realize = {
          type = "app";
          program = "${./nix/realize.sh}";
        };
        packages.default = hsPkgs.clash-crypto;
        packages.hitlt = hitlt;
        packages.hitltHsPkgs = hitltHsPkgs;
        packages.ciEnv = ciEnv;
      });
}
