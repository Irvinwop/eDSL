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

lean_exe «edsl-cfg-import» where
  root := `CFGMain

lean_exe «edsl-grade» where
  root := `GradeMain

lean_exe «edsl-proof-export» where
  root := `ExportMain

lean_lib GradingFixtures where
  roots := #[`tests.fixtures.GradingClient, `tests.fixtures.StrideMov,
    `tests.fixtures.WriteIntermediate]
