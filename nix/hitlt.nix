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
        bySource = source: value: {
          target = {
            source = "${./..}/tests/hitl/top/${source}.hs";
          };
          clashArgs = {
            extraEnvPackages = [ "clash-crypto" ];
            extraFlags = hitltBaseArgs.clashArgs.extraFlags ++ [
              "-DHITLT_${source}=${value}"
              "-DHITLT_BAUD=${config.serial-speed}"
            ];
          };
        };
    in {
      AES128               = bySource "AES" "AES128";
      AES192               = bySource "AES" "AES192";
      AES256               = bySource "AES" "AES256";
      BEA                  = byModule "BEA";
      Calculator           = byModule "Calculator";
      CLU                  = byModule "CLU";
      DeterministicNonce   = byModule "DeterministicNonce";
      ECDSADerivePublicKey = byModule "ECDSADerivePublicKey";
      ECDSASign            = byModule "ECDSASign";
      FastGCD              = byModule "FastGCD";
      FltCtmi              = byModule "FltCtmi";
      Karatsuba            = byModule "Karatsuba";
      KaratsubaModulo      = byModule "KaratsubaModulo";
      Modulo               = byModule "Modulo";
      SictMi               = byModule "SictMi";
      Stack                = byModule "Stack";
      SHA1                 = bySource "SHA" "SHA1";
      SHA224               = bySource "SHA" "SHA224";
      SHA256               = bySource "SHA" "SHA256";
      SHA384               = bySource "SHA" "SHA384";
      SHA512               = bySource "SHA" "SHA512";
      SHA512224            = bySource "SHA" "SHA512224";
      SHA512256            = bySource "SHA" "SHA512256";
      HMACSHA1             = bySource "HMAC" "SHA1";
      HMACSHA224           = bySource "HMAC" "SHA224";
      HMACSHA256           = bySource "HMAC" "SHA256";
      HMACSHA384           = bySource "HMAC" "SHA384";
      HMACSHA512           = bySource "HMAC" "SHA512";
      HMACSHA512224        = bySource "HMAC" "SHA512224";
      HMACSHA512256        = bySource "HMAC" "SHA512256";
    };
}
