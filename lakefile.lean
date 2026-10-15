import Lake
open Lake DSL

package edsl where
  moreLeanArgs := #["-DwarningAsError=true"]

@[default_target]
lean_lib EDSL

lean_exe «edsl-certify» where
  root := `Main

lean_exe «edsl-certify-process» where
  root := `ProcessMain

lean_exe «edsl-certify-counter» where
  root := `CounterMain

lean_exe «edsl-certify-mutex-worker» where
  root := `MutexWorkerMain
