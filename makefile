hitlt:
	time cabal run -- clash-crypto:clash \
    -package-env .ghc.environment.* \
    -fclash-spec-limit=10000 \
    -outputdir _build \
    --verilog \
    tests/hitl/Top.hs

#    -fclash-debug DebugApplied \