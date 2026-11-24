import Lake
open Lake DSL

require leanCrypto from "packages/lean-crypto"

package tornadoLeanCli where
  version := v!"0.1.0"
  -- Lean's bundled linker uses its own sysroot; macOS SDK stubs must be
  -- named explicitly. Linux ignores these search paths and uses libcurl.
  moreLinkArgs := #[
    "-L/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib",
    "-L/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk/usr/lib",
    "-lcurl"]

extern_lib tornadoPrivateIO (pkg : NPackage __name__) := do
  let source ← inputFile (pkg.dir / "native" / "tornado_private_io.c") false
  let lean ← getLeanInstall
  let privateHeader := pkg.dir / "native" / "tornado_private_io.h"
  let object ← buildO (pkg.buildDir / "native" / "tornado_private_io.o") source
    #[] #["-I", lean.includeDir.toString, "-std=c11", "-Wall", "-Wextra", "-Werror"]
    (compiler := "/usr/bin/cc") (extraDepTrace := computeTrace privateHeader)
  let httpsSource ← inputFile (pkg.dir / "native" / "tornado_https.c") false
  let httpsObject ← buildO (pkg.buildDir / "native" / "tornado_https.o") httpsSource
    #[] #["-I", lean.includeDir.toString, "-std=c11", "-Wall", "-Wextra", "-Werror"]
    (compiler := "/usr/bin/cc")
  -- Protected owner-key signing uses the pinned libsecp256k1 recovery module.
  -- The bridge reads the key inside C and returns only public bytes to Lean.
  -- The isolated note-derived signer uses separate Lean arithmetic.
  let vendor := pkg.dir / "native" / "vendor" / "libsecp256k1"
  -- Lake does not infer C #include dependencies from buildO. Hash every
  -- vendored header so a header-only edit cannot reuse stale secp objects.
  let vendorHeaderTrace : JobM BuildTrace := do
    let includeFiles ← (vendor / "include").walkDir
    let sourceFiles ← (vendor / "src").walkDir
    let headers := (includeFiles ++ sourceFiles).filter
      (fun file => file.toString.endsWith ".h")
    computeTrace (headers.qsort (fun a b => a.toString < b.toString))
  let secpFlags := #["-I", (vendor / "include").toString,
    "-I", (vendor / "src").toString,
    "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror",
    "-Wno-unused-function",
    "-DENABLE_MODULE_RECOVERY=1", "-DCOMB_BLOCKS=43", "-DCOMB_TEETH=6",
    "-DECMULT_WINDOW_SIZE=15"]
  let secpSource ← inputFile (vendor / "src" / "secp256k1.c") false
  let secpObject ← buildO (pkg.buildDir / "native" / "secp256k1.o") secpSource
    #[] secpFlags (compiler := "/usr/bin/cc")
    (extraDepTrace := vendorHeaderTrace)
  let precomputedSource ← inputFile (vendor / "src" / "precomputed_ecmult.c") false
  let precomputedObject ← buildO (pkg.buildDir / "native" / "precomputed_ecmult.o")
    precomputedSource #[] secpFlags (compiler := "/usr/bin/cc")
    (extraDepTrace := vendorHeaderTrace)
  let precomputedGenSource ← inputFile (vendor / "src" / "precomputed_ecmult_gen.c") false
  let precomputedGenObject ← buildO (pkg.buildDir / "native" / "precomputed_ecmult_gen.o")
    precomputedGenSource #[] secpFlags (compiler := "/usr/bin/cc")
    (extraDepTrace := vendorHeaderTrace)
  let signerSource ← inputFile (pkg.dir / "native" / "tornado_secret_sign.c") false
  let signerObject ← buildO (pkg.buildDir / "native" / "tornado_secret_sign.o") signerSource
    #[] (#["-I", lean.includeDir.toString] ++ secpFlags)
    (compiler := "/usr/bin/cc")
    (extraDepTrace := do
      return mixTrace (← vendorHeaderTrace) (← computeTrace privateHeader))
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "tornadoPrivateIO")
    #[object, httpsObject, signerObject, secpObject,
      precomputedObject, precomputedGenObject]

lean_lib Tornado where
  roots := #[`Tornado]

lean_lib WithdrawalJournalChecks where
  roots := #[`tests.WithdrawalJournal]

@[default_target]
lean_exe tornado where
  root := `Main

lean_exe protected_io_test where
  root := `tests.ProtectedIO

lean_exe https_transport_test where
  root := `tests.HttpsTransport

lean_exe https_get_test where
  root := `tests.HttpsGet

lean_exe attempt_journal_test where
  root := `tests.AttemptJournal

lean_exe note_claims_test where
  root := `tests.NoteClaims

lean_exe gzip_test where
  root := `tests.Gzip

lean_exe groth16_full_public_test where
  root := `tests.Groth16MSMFull

lean_exe classic_proof_pipeline_full_test where
  root := `tests.ClassicProofPipelineFull

lean_exe journal_refinement_test where
  root := `tests.JournalIORefinement

lean_exe selected_pool_bootstrap_test where
  root := `tests.SelectedPoolBootstrap

lean_exe deposit_send_test where
  root := `tests.DepositSend

lean_exe native_signer_test where
  root := `tests.NativeSigner

lean_exe deposit_multi_test where
  root := `tests.DepositMulti

lean_exe withdraw_proof_test where
  root := `tests.WithdrawProof

lean_exe tornado_prover_worker where
  root := `Tornado.Cli.ProverWorkerMain

lean_exe prover_worker_test where
  root := `tests.ProverWorker

lean_exe history_snapshot_test where
  root := `tests.HistorySnapshot

lean_exe prover_worker_metadata_test where
  root := `tests.ProverWorkerMetadata

lean_exe protected_replace_test where
  root := `tests.ProtectedReplace

lean_exe relayer_submit_test where
  root := `tests.RelayerSubmit

lean_exe worker_disclosure_test where
  root := `tests.WorkerDisclosure

lean_exe witness_certificate_test where
  root := `tests.WitnessCertificate

-- The fault object is linked only into this process regression executable.
-- Its translation unit includes the real protected-I/O implementation, with
-- test-only syscall cuts; it must never become a package extern_lib.
target reservationFaultIO pkg : System.FilePath := do
  let source ← inputFile (pkg.dir / "tests" / "native" / "reservation_fault_io.c") false
  let lean ← getLeanInstall
  buildO (pkg.buildDir / "native" / "reservation_fault_io.o") source
    #[] #["-I", lean.includeDir.toString, "-std=c11", "-Wall", "-Wextra", "-Werror"]
    (compiler := "/usr/bin/cc")
    (extraDepTrace := computeTrace #[pkg.dir / "native" / "tornado_private_io.c",
      pkg.dir / "native" / "tornado_private_io.h"])

lean_exe reservation_admission_process_test where
  root := `tests.ReservationAdmissionProcess
  moreLinkObjs := #[{ key := .packageTarget .anonymous `reservationFaultIO }]
