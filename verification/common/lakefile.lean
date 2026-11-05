import Lake
open Lake DSL
package e5rVerification
@[default_target]
lean_lib E5rVerification
lean_exe proofcheck where
  root := `E5rVerification.Main
