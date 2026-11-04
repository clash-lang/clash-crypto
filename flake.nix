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
    ecpprog.url = "github:gregdavill/ecpprog";
    ghc-tcplugin-api = { url = "github:sheaf/ghc-tcplugin-api"; flake = false; };
    ghc-typelits-natnormalise = { url = "github:clash-lang/ghc-typelits-natnormalise"; flake = false; };
    ghc-typelits-knownnat = { url = "github:clash-lang/ghc-typelits-knownnat"; flake = false; };
    ghc-typelits-extra = { url = "github:clash-lang/ghc-typelits-extra"; flake = false; };
    clash-compiler = { url = "github:clash-lang/clash-compiler"; flake = false; };
    ghc-typelits-proof-assist.url = "github:clash-lang/ghc-typelits-proof-assist";
  };
  outputs =
  { self
  , nixpkgs
  , flake-utils
  , nix-filter
  , ecpprog
  , ghc-tcplugin-api
  , ghc-typelits-natnormalise
  , ghc-typelits-knownnat
  , ghc-typelits-extra
  , clash-compiler
  , ghc-typelits-proof-assist
  , ...
  }:
    flake-utils.lib.eachDefaultSystem (system:
      let config = import ./build-config.nix;

          inherit (pkgs.haskell.lib) dontCheck doJailbreak overrideCabal markUnbroken;

          ecpprogOverlay = _: _: {
            ecpprog = ecpprog.defaultPackage.${system};
          };

          haskellOverlay = final: prev:
            let
              ghcOverlayFile = ./. + "/nix/ghc10/overlay-ghc101.nix";
              ghcOverlay =
                if builtins.pathExists ghcOverlayFile then
                  import ghcOverlayFile { pkgs = prev; }
                else
                  _: _: {};

              pkgSrcOverlay = final: prev: {
                clash-prelude = dontCheck (prev.callCabal2nix "clash-prelude"
                  (clash-compiler + "/clash-prelude") { });
                clash-prelude-hedgehog = dontCheck (prev.callCabal2nix "clash-prelude-hedgehog"
                  (clash-compiler + "/clash-prelude-hedgehog") { });
                clash-lib =
                  let package = prev.callCabal2nix "clash-lib" (clash-compiler + "/clash-lib") {};
                   in dontCheck ( package.overrideAttrs (_: _: {
                        patches = [ ./nix/ghc10/patches/clash-lib.patch ];
                      }));
                clash-ghc =
                  let package = prev.callCabal2nix "clash-ghc" (clash-compiler + "/clash-ghc") {};
                  in dontCheck ( package.overrideAttrs (_: _: {
                        patches = [ ./nix/ghc10/patches/clash-ghc.patch ];
                      }));
                ghc-tcplugin-api =
                  let package = prev.callCabal2nix "ghc-tcplugin-api" ghc-tcplugin-api {};
                   in dontCheck ( package.overrideAttrs (_: _: {
                        patches = [ ./nix/ghc10/patches/ghc-tcplugin-api.patch ];
                      }));
                ghc-typelits-natnormalise = dontCheck (
                  prev.callCabal2nix "ghc-typelits-natnormalise"
                    ghc-typelits-natnormalise {}
                );
                ghc-typelits-knownnat = dontCheck (
                  prev.callCabal2nix "ghc-typelits-knownnat"
                    ghc-typelits-knownnat {}
                );
                ghc-typelits-extra =
                  let package = prev.callCabal2nix "ghc-typelits-extra" ghc-typelits-extra {};
                   in doJailbreak ( dontCheck ( package.overrideAttrs (_: _: {
                        patches = [ ./nix/ghc10/patches/ghc-typelits-extra.patch ];
                      })));
                ghc-typelits-proof-assist =
                  let package = prev.callCabal2nix "ghc-typelits-proof-assist"
                        ghc-typelits-proof-assist.outPath {};
                   in dontCheck ( package.overrideAttrs (_: _: {
                        patches = [ ./nix/ghc10/patches/ghc-typelits-proof-assist.patch ];
                      }));
                clash-crypto =
                  let src = nix-filter.lib {
                        root = self;
                        exclude = [
                          (nix-filter.lib.matchExt "nix")
                          "flake.lock"
                        ];
                      };
                   in (overrideCabal (final.callCabal2nix "clash-crypto" src {}) {
                        # Works around a potential cabal bug preventing the main
                        # library to be found when building a sub-library requiring
                        # template haskell support.
                        preBuild = (prev.clash-crypto.preBuild or "") + ''
                          export LD_LIBRARY_PATH="$PWD/dist/build''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
                        '';
                        configureFlags = [
                          "--ghc-option=-DHITLT_BAUD=${config.serial-speed}"
                        ];
                      }).overrideAttrs (_: _: {
                        checkFlags = [ "simulation" ];
                      });
              };

              overlays =
                prev.lib.composeManyExtensions [
                    pkgSrcOverlay
                    ghcOverlay
                  ];
            in {
              hsPkgs-ghc101 =
                let
                  ghc101Packages = (prev.haskell.packages.ghc9141.override {
                    ghc = import ./nix/ghc10/ghc-10.1.nix { pkgs = prev; };
                    buildHaskellPackages = ghc101Packages;
                  }).extend overlays;
                in
                  ghc101Packages;
            };

          extensions = [ ecpprogOverlay haskellOverlay ];
          pkgs0 = nixpkgs.legacyPackages.${system};
          pkgs = pkgs0.extend (pkgs0.lib.composeManyExtensions extensions);
          hsPkgs = pkgs.hsPkgs-ghc101;

          inherit (pkgs) lib;
          clashLib = import ./nix/clash.nix { inherit pkgs lib; };

          envTools =
            (with pkgs; [ gnumake yosys nextpnr trellis ]) ++
            [ pkgs.ecpprog ] ++
            (with hsPkgs; [ cabal-install clash-ghc ])
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
            name = "GHC-10.1-70dc4e6";
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
