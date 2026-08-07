import PrimeCert.Meta.PolyaCert

/-! Times building the parity table by walking every integer and testing its prime-power bit. -/

set_option maxRecDepth 4000000
set_option Elab.async false

run_cert_lambits 936411
