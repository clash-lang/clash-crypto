hsPkgs: {
  hitltBaseArgs = {
    hsPkgs = hsPkgs;
    clashArgs = {
      extraExposedComponents = [
        { package = "clash-crypto"; component = "hitl"; }
      ];
      extraFlags = [
        "-fclash-clear"
        "-fclash-spec-limit=200"
        "-fclash-inline-limit=200"
        "-fconstraint-solver-iterations=20"
      ];
    };
    target.package = "clash-crypto:hitlt-instances";
    nextpnrFlags = [
      "--85k"
      "--package" "CSFBGA285"
      "--lpf" "${./../orangecrab.pcf}"
    ];
  };
  hitltTopEntities = {
    BEA = { target = { module = "BEA"; }; };
    Calculator = { target = { module = "Calculator"; }; };
    CLU = { target = { module = "CLU"; }; };
    FastGCD = { target = { module = "FastGCD"; }; };
    FltCtmi = { target = { module = "FltCtmi"; }; };
    Karatsuba = { target = { module = "Karatsuba"; }; };
    KaratsubaModulo = { target = {  module = "KaratsubaModulo"; }; };
    Modulo = { target = { module = "Modulo"; }; };
    SictMi = { target = { module = "SictMi"; }; };
    Stack = { target = { module = "Stack"; }; };
    SHA1 = { target = { module = "SHA"; }; binding = "topEntitySHA1"; };
    SHA224 = { target = { module = "SHA"; }; binding = "topEntitySHA224"; };
    SHA256 = { target = { module = "SHA"; }; binding = "topEntitySHA256"; };
    SHA384 = { target = { module = "SHA"; }; binding = "topEntitySHA384"; };
    SHA512 = { target = { module = "SHA"; }; binding = "topEntitySHA512"; };
    SHA512224 = { target = { module = "SHA"; }; binding = "topEntitySHA512224"; };
    SHA512256 = { target = { module = "SHA"; }; binding = "topEntitySHA512256"; };
    HMACSHA1 = { target = { module = "HMAC"; }; binding = "topEntitySHA1"; };
    HMACSHA224 = { target = { module = "HMAC"; }; binding = "topEntitySHA224"; };
    HMACSHA256 = { target = { module = "HMAC"; }; binding = "topEntitySHA256"; };
    HMACSHA384 = { target = { module = "HMAC"; }; binding = "topEntitySHA384"; };
    HMACSHA512 = { target = { module = "HMAC"; }; binding = "topEntitySHA512"; };
    HMACSHA512224 = { target = { module = "HMAC"; }; binding = "topEntitySHA512224"; };
    HMACSHA512256 = { target = { module = "HMAC"; }; binding = "topEntitySHA512256"; };
  };
}
