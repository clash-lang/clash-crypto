hitlt:
	time cabal run -- clash-crypto:clash \
    -package-env .ghc.environment.* \
    -fclash-spec-limit=100 \
    -fclash-inline-limit=100 \
    -outputdir _build \
    --verilog \
    tests/hitl/Top.hs
	wc -l _build/Top.topEntity/topEntity.v

yosys:
	time yosys -p "read_verilog _build/Top.topEntity/topEntity.v; synth_ecp5 -top topEntity -json _build/topEntity.json"

nextpnr:
	time nextpnr-ecp5 \
    --85k \
    --package CSFBGA285 \
    --json _build/topEntity.json \
    --out-of-context \
    --threads "1"
