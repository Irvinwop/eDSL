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

lean_exe «edsl-certify-futex» where
  root := `FutexMain

lean_exe «edsl-certify-futex-client» where
  root := `FutexClientMain

lean_exe «edsl-certify-sum32» where
  root := `Sum32Main
