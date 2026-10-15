import Lake
open Lake DSL

package edsl where
  moreLeanArgs := #["-DwarningAsError=true"]

@[default_target]
lean_lib EDSL

lean_exe «edsl-certify» where
  root := `Main
