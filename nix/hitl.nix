hsPkgs: {
  hitltBaseArgs = {
    hsPkgs = hsPkgs;
    clashArgs = {
      extraExposedComponents = [
        { package = "clash-crypto"; component = "hitlt-shared"; }
      ];
      extraFlags = [
        "-fclash-clear"
        "-fclash-spec-limit=200"
        "-fclash-inline-limit=200"
        "-fconstraint-solver-iterations=20"
      ];
    };
    package = "clash-crypto:hitlt-instances";
    nextpnrFlags = [
      "--85k"
      "--package" "CSFBGA285"
      "--lpf" "${./../orangecrab.pcf}"
    ];
  };
  hitltTopEntities = {
    BEA = { module = "BEA"; };
    FastGCD = { module = "FastGCD"; };
    FltCtmi = { module = "FltCtmi"; };
    Karatsuba = { module = "Karatsuba"; };
    Modulo = { module = "Modulo"; };
    SictMi = { module = "SictMi"; };
    SHA1 = { module = "SHA"; binding = "topEntitySHA1"; };
    SHA224 = { module = "SHA"; binding = "topEntitySHA224"; };
    SHA256 = { module = "SHA"; binding = "topEntitySHA256"; };
    SHA384 = { module = "SHA"; binding = "topEntitySHA384"; };
    SHA512 = { module = "SHA"; binding = "topEntitySHA512"; };
    SHA512224 = { module = "SHA"; binding = "topEntitySHA512224"; };
    SHA512256 = { module = "SHA"; binding = "topEntitySHA512256"; };
    HMACSHA1 = { module = "HMAC"; binding = "topEntitySHA1"; };
    HMACSHA224 = { module = "HMAC"; binding = "topEntitySHA224"; };
    HMACSHA256 = { module = "HMAC"; binding = "topEntitySHA256"; };
    HMACSHA384 = { module = "HMAC"; binding = "topEntitySHA384"; };
    HMACSHA512 = { module = "HMAC"; binding = "topEntitySHA512"; };
    HMACSHA512224 = { module = "HMAC"; binding = "topEntitySHA512224"; };
    HMACSHA512256 = { module = "HMAC"; binding = "topEntitySHA512256"; };
  };
}
