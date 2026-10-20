import Lake
open Lake DSL

package edsl where
  moreLeanArgs := #["-DwarningAsError=true"]

@[default_target]
lean_lib EDSL

lean_exe «edsl-certify» where
  root := `Tools.Certify.Function

lean_exe «edsl-certify-process» where
  root := `Tools.Certify.Process

lean_exe «edsl-certify-counter» where
  root := `Tools.Certify.Counter

lean_exe «edsl-certify-mutex-worker» where
  root := `Tools.Certify.MutexWorker

lean_exe «edsl-certify-futex» where
  root := `Tools.Certify.Futex

lean_exe «edsl-certify-futex-client» where
  root := `Tools.Certify.FutexClient

lean_exe «edsl-certify-futex-predicate» where
  root := `Tools.Certify.FutexPredicate

lean_exe «edsl-certify-sum32» where
  root := `Tools.Certify.Sum32

lean_exe «edsl-cfg-import» where
  root := `Tools.CFG

lean_exe «edsl-grade» where
  root := `Tools.Grade.Function

lean_exe «edsl-grade-call-stack» where
  root := `Tools.Grade.CallStack

lean_exe «edsl-grade-call-memory64» where
  root := `Tools.Grade.CallMemory64

lean_exe «edsl-grade-call-memory-loop64» where
  root := `Tools.Grade.CallMemoryLoop64

lean_exe «edsl-grade-atomic-logical64» where
  root := `Tools.Grade.AtomicLogical64

lean_exe «edsl-grade-atomic-set64» where
  root := `Tools.Grade.AtomicSet64

lean_exe «edsl-proof-export» where
  root := `Tools.ProofExport

lean_exe «edsl-certify-store-return32» where
  root := `Tools.Certify.StoreReturn32

lean_exe «edsl-certify-store-load64» where
  root := `Tools.Certify.StoreLoad64

lean_exe «edsl-certify-atomic-logical64» where
  root := `Tools.Certify.AtomicLogical64

lean_exe «edsl-certify-atomic-set64» where
  root := `Tools.Certify.AtomicSet64

lean_exe «edsl-certify-counted-store64» where
  root := `Tools.Certify.CountedStore64

lean_exe «edsl-certify-counted-store64-clang» where
  root := `Tools.Certify.CountedStore64Clang

-- Client proof modules compile separately from the grader's trusted imports.
lean_lib GradingFixtures where
  roots := #[`tests.fixtures]
  globs := #[.submodules `tests.fixtures]

-- Build shared fixtures and their clients once through Lake's input traces.
-- The explicit audit entry point remains runnable after restoring these proofs.
lean_lib ManagedFetchAdd64Tests where
  roots := #[`tests.AtomicFetchAddHistory64, `tests.TSO64Fixtures,
    `tests.TSO64Interleaving, `tests.TSO64Forwarding, `tests.TSO64CurrentRAM,
    `tests.TSO64Denials, `tests.TSO64Audit, `tests.ManagedOverlay64,
    `tests.FetchAddCalls64, `tests.FetchAddABI64, `tests.AtomicMethods,
    `tests.CorpusFetchAdd64, `tests.ManagedFetchAdd64Audit]

-- Checked shared-cell accesses, separate from scheduler and source ordering.
lean_lib AtomicAccess64Tests where
  roots := #[`tests.AtomicAccess64]

-- Whole-word sources in the production mixed-width memory projection.
lean_lib WholeQWordTests where
  roots := #[`tests.WholeQWordProvenance]
  moreLeanArgs := #["-DautoImplicit=false"]

-- Current-authority publication and persistent per-worker store occurrences.
lean_lib ManagedQueue64Tests where
  roots := #[`tests.ManagedQueue64, `tests.TSO64SharedCells, `tests.TSO64ReadSource, `tests.TSO64PublishedWriters, `tests.TSOWordProjection, `tests.TSO64StoreIdentities, `tests.TSO64StoreTrace, `tests.TSO64AtomicTrace]
  moreLeanArgs := #["-DautoImplicit=false"]

-- Source atomic event graphs remain separate from machine scheduling.
lean_lib C23AtomicTests where
  roots := #[`tests.C23AtomicEvents, `tests.C23MessagePassing, `tests.C23AtomicCheck]
  moreLeanArgs := #["-DautoImplicit=false"]

-- Cache input-traced byte-scan regressions alongside production proofs.
lean_lib BoundedScanTests where
  roots := #[`tests.SequentialByteComparison, `tests.BufferCallResources,
    `tests.BufferCallVCGen, `tests.ByteScanBodies, `tests.CorpusByteScanResources]

-- Build released search contract and ISA regressions through Lake input traces.
lean_lib IndexSearchTests where
  roots := #[`tests.IndexSearch, `tests.SequentialSearchISA,
    `tests.CorpusIndexSearchResources, `tests.IndexSearchBodies]
  moreLeanArgs := #["-DautoImplicit=false"]

-- Paired unsigned-byte contracts, decoded operand widths and current loans.
lean_lib ByteComparisonTests where
  roots := #[`tests.ByteComparison, `tests.SequentialByteOrderISA,
    `tests.CorpusByteComparisonResources, `tests.ByteComparisonBodies]
  moreLeanArgs := #["-DautoImplicit=false"]

-- New-program raw/final-ELF clients and the reusable API import boundary.
lean_lib VerificationTests where
  roots := #[`tests.VerificationImports, `tests.VerifyFunction, `tests.ELFCertificate,
    `tests.ELFFunctionSymbol, `tests.ELFFunctionCandidate, `tests.ELFStackCaller,
    `tests.ELFFunctionWindow, `tests.ELFFunctionBounds, `tests.ELFCallerBounds,
    `tests.ReadOnlyCallTransport,
    `tests.VCGenScratchFrame]
  moreLeanArgs := #["-DautoImplicit=false"]

-- Shared unary ISA rules, generated scalar clients and exact loaded resources.
lean_lib UnaryTests where
  roots := #[`tests.native.UnaryReplay, `tests.native.RegisterCapture, `tests.SequentialUnary,
    `tests.UnaryBodies, `tests.CorpusUnaryResources,
    `tests.GradingUnary]
  moreLeanArgs := #["-DautoImplicit=false"]

-- Sparse scalar loops, exact popcount artifacts and their caller-resource bridge.
lean_lib PopcountTests where
  roots := #[`tests.SequentialCounter32, `tests.SequentialDisplacement,
    `tests.VCGenCompactLoop, `tests.PopcountBodies,
    `tests.CorpusPopcountResources, `tests.GradingPopcount]
  moreLeanArgs := #["-DautoImplicit=false"]

-- Shared shift semantics, generated average proofs and exact caller resources.
lean_lib AverageTests where
  roots := #[`tests.WordMathAverage, `tests.native.ShiftOneReplay, `tests.SequentialShiftOne,
    `tests.ShiftOneAudit, `tests.AverageBodies,
    `tests.AverageResources, `tests.GradingAverage]
  moreLeanArgs := #["-DautoImplicit=false"]

-- Shared parity ISA, exact generated bodies and registered scalar certificates.
lean_lib ParityTests where
  roots := #[`tests.SequentialParityISA, `tests.SequentialPadding, `tests.ParityISAAudit,
    `tests.ParityBodies, `tests.ParityResources, `tests.GradingParity]
  moreLeanArgs := #["-DautoImplicit=false"]

-- Shared neutral flag choices, generated rotation and registered resources.
lean_lib RotationTests where
  roots := #[`tests.SequentialRotate, `tests.RotateAudit, `tests.RotationBodies,
    `tests.RotationResources, `tests.GradingRotation]
  moreLeanArgs := #["-DautoImplicit=false"]

-- Partial-byte results through the shared machine, VCG and current resources.
lean_lib Low8Tests where
  roots := #[`tests.SequentialLow8, `tests.Low8Audit]
  moreLeanArgs := #["-DautoImplicit=false"]

-- Paired-buffer Boolean contracts and real DATA1 comparison/padding rules.
lean_lib ByteEqualityTests where
  roots := #[`tests.ByteEquality, `tests.SequentialByteComparePadding,
    `tests.ByteComparePaddingAudit, `tests.ByteEqualityBodies,
    `tests.GradingByteEquality, `tests.ByteEqualityCertificates]
  moreLeanArgs := #["-DautoImplicit=false"]

-- Explicit larger bounds and preservation of the original default profile.
lean_lib CFGProfileTests where
  roots := #[`tests.CFGProfiles, `tests.CFG, `tests.VCGen, `tests.VCGenCutpoints,
    `tests.VCGenCompactLoop, `tests.VCGenPolicy, `tests.VCGenReflection,
    `tests.BufferCallVCGen]
  moreLeanArgs := #["-DautoImplicit=false"]
