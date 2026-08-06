import PrimeCert.Meta.PolyaCert

/-! Runs each prototype certification loop at a small bound and reports its self-check. -/

set_option maxRecDepth 4000000
set_option Elab.async false

run_cert_gap 10000
run_cert_count 10000
run_cert_lamsieve 10000
run_cert_self 10000
run_cert_spread 10000
