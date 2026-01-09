{ lib, pkgs }: rec {
  cabal = rec {
    splitTarget = target:
      let parts = builtins.match "([^:]+)(:([^:]+))?" target;
          package = builtins.elemAt parts 0;
          component = builtins.elemAt parts 2;
      in { inherit package component; };

    munge = component:
      if component.component == null
      then component.package
      else "z-${component.package}-z-${component.component}";

    expose = component:
      "-package-id $(ghc-pkg --simple-output field ${munge component} id)";
  };

  onlyClash =
    { hsPkgs
    , package
    , module ? "Main"
    , binding ? "topEntity"
    , envPackages ? [ "clash-ghc" (cabal.splitTarget package).package ] ++ extraEnvPackages
    , extraEnvPackages ? []
    , exposedComponents ? (builtins.map cabal.splitTarget [
        package
        "ghc-typelits-natnormalise"
        "ghc-typelits-extra"
        "ghc-typelits-knownnat"
      ]) ++ extraExposedComponents
    , extraExposedComponents ? []
    , env ?
      (hsPkgs.ghcWithPackages
        (p: builtins.map (n: builtins.getAttr n p) envPackages)
      ).overrideAttrs (_: prev: {
        buildCommand = ''
          ${prev.buildCommand}
          ${lib.strings.concatStringsSep "\n" (
            builtins.map (c: "$out/bin/ghc-pkg expose ${cabal.munge c}") exposedComponents
          )}
        '';
      })
    , flags ? [ "--verilog" ] ++ extraFlags
    , extraFlags ? []
    , ...
    }@args:
      pkgs.stdenv.mkDerivation ((builtins.removeAttrs args [ "hsPkgs" "exposedComponents" "extraExposedComponents" ]) // {
        __contentAddressed = true;
        dontUnpack = true;
        buildPhase = ''
          export PATH=${env}/bin:$PATH
          clash \
            -package-db ${env}/lib/ghc-*/lib/package.conf.d \
            -outputdir . \
            ${lib.strings.escapeShellArgs flags} \
            ${module} -main-is ${binding}
        '';
        installPhase = ''
          mkdir -p $out
          mv ${lib.strings.escapeShellArg "${module}.${binding}"}/* $out
          rm $out/clash-manifest.json
        '';
      });

  ecp5.clash =
    { hsPkgs
    , package
    , module ? "Main"
    , binding ? "topEntity"
    , name ? "${package}-${module}-${binding}"
    , clashArgs ? {}
    , ...
    }@args0:
      let args = builtins.removeAttrs args0 [ "hsPkgs" "clashArgs" ];
          clashArgs0 = {
            inherit hsPkgs package module binding;
            name = "${name}-hdl";
          };
          clashSrc = onlyClash (clashArgs0 // clashArgs);
          synthArgs = args // {
            inherit name;
            src = clashSrc;
          };
      in ecp5.synthesize synthArgs;

  ecp5.synthesize =
    # Synthesis options
    { yosysFlags ? []
    , preRead    ? ""
    , read       ? "read_verilog ${readFlags} *.v"
    , readFlags  ? ""
    , postRead   ? ""
    , preSynth   ? ""
    , synthFlags ? ""
    , synth      ? "synth_ecp5 ${synthFlags}"
    , postSynth  ? ""
    , preWrite   ? ""
    , write      ? "write_json ${writeFlags} 01-synthesized/top.json"
    , writeFlags ? ""
    , postWrite  ? ""

    # Place & route options
    , nextpnrFlags ? []

    # Bitstream packing options
    , ecppackFlags ? []
    , doCompress ? true

    # Expect at least name, src(s) to be passed along to mkDerivation
    , ...
    }@args:
      let programArg = arg: if arg == "" then ""  else lib.escapeShellArgs [ "-p" arg ];
      in pkgs.stdenv.mkDerivation (args // {
        nativeBuildInputs = [ pkgs.yosys pkgs.nextpnr pkgs.trellis ];
        configurePhase = ''
          mkdir -p 01-synthesized
          mkdir -p 02-routed
          mkdir -p 03-bitstream
        '';
        buildPhase = ''
          runPhase synthesizePhase
          runPhase placeAndRoutePhase
          runPhase packPhase
        '';
        synthesizePhase = ''
          yosys \
            ${lib.escapeShellArgs yosysFlags} \
            ${programArg preRead} \
            ${programArg read} \
            ${programArg postRead} \
            ${programArg preSynth} \
            ${programArg synth} \
            ${programArg postSynth} \
            ${programArg preWrite} \
            ${programArg write} \
            ${programArg postWrite}
        '';
        placeAndRoutePhase = ''
          nextpnr-ecp5 --version
          nextpnr-ecp5 \
            ${lib.escapeShellArgs nextpnrFlags} \
            --json 01-synthesized/top.json \
            --textcfg 02-routed/top.config
        '';
        packPhase = ''
          ecppack \
            ${lib.escapeShellArgs ecppackFlags} \
            ${lib.optionalString doCompress "--compress"} \
            --input 02-routed/top.config \
            --bit 03-bitstream/top.bit
        '';
        installPhase = ''
          mkdir -p $out
          cp 03-bitstream/top.bit $out/top.bit
          ${lib.optionalString (pkgs ? ecpprog) ''
            mkdir -p $out/bin
            cat <<EOF > $out/bin/upload
            #!/bin/bash
            ${pkgs.ecpprog}/bin/ecpprog "\$@" -S $out/top.bit
            EOF
            chmod +x $out/bin/upload
          ''}
        '';
      });
}
