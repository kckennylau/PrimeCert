import PrimeCert.Meta.PolyaCert

/-! Times the table stage as it stands: one stride per packed prime power. -/

set_option maxRecDepth 4000000
set_option Elab.async false

run_cert_base 100000
