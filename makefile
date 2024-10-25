hitlt:
	time cabal run -- clash-crypto:clash \
    -package-env .ghc.environment.* \
    -fclash-spec-limit=100 \
    -outputdir _build \
    --verilog \
    tests/hitl/Top.hs
