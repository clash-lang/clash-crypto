hsPkgs: config: rec {
  hitltBaseArgs = {
    hsPkgs = hsPkgs;
    clashArgs = {
      extraExposedComponents = [
        { package = "clash-crypto"; component = "hitl"; }
      ];
      extraFlags = [
        "-fclash-clear"
        "-fclash-spec-limit=400"
        "-fclash-inline-limit=100"
        "-fconstraint-solver-iterations=20"
      ];
    };
    nextpnrFlags = [
      "--85k"
      "--package" "CSFBGA285"
      "--lpf" "${./../orangecrab.pcf}"
    ];
  };
  hitltTopEntities =
    let byModule = module: {
          target = {
            package = "clash-crypto:hitlt-instances";
            inherit module;
          };
        };
        bySource = source: sha: {
          target = {
            source = "${./..}/tests/hitl/top/${source}";
          };
          clashArgs = {
            extraEnvPackages = [ "clash-crypto" ];
            extraFlags = hitltBaseArgs.clashArgs.extraFlags ++ [
              "-DHITLT_SHA=${sha}"
              "-DHITLT_BAUD=${config.serial-speed}"
            ];
          };
        };
    in {
      BEA = byModule "BEA";
      Calculator = byModule "Calculator";
      CLU = byModule "CLU";
      DeterministicNonce = byModule "DeterministicNonce";
      ECDSADerivePublicKey = byModule "ECDSADerivePublicKey";
      ECDSASign = byModule "ECDSASign";
      FastGCD = byModule "FastGCD";
      FltCtmi = byModule "FltCtmi";
      Karatsuba = byModule "Karatsuba";
      KaratsubaModulo = byModule  "KaratsubaModulo";
      Modulo = byModule "Modulo";
      SictMi = byModule "SictMi";
      Stack = byModule "Stack";
      SHA1 = bySource "SHA.hs" "SHA1";
      SHA224 = bySource "SHA.hs" "SHA224";
      SHA256 = bySource "SHA.hs" "SHA256";
      SHA384 = bySource "SHA.hs" "SHA384";
      SHA512 = bySource "SHA.hs" "SHA512";
      SHA512224 = bySource "SHA.hs" "SHA512224";
      SHA512256 = bySource "SHA.hs" "SHA512256";
      HMACSHA1 = bySource "HMAC.hs" "SHA1";
      HMACSHA224 = bySource "HMAC.hs" "SHA224";
      HMACSHA256 = bySource "HMAC.hs" "SHA256";
      HMACSHA384 = bySource "HMAC.hs" "SHA384";
      HMACSHA512 = bySource "HMAC.hs" "SHA512";
      HMACSHA512224 = bySource "HMAC.hs" "SHA512224";
      HMACSHA512256 = bySource "HMAC.hs" "SHA512256";
    };
}
