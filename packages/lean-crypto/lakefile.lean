import Lake
open Lake DSL

package leanCrypto where
  version := v!"0.1.0"

@[default_target]
lean_lib LeanCrypto where
  roots := #[`LeanCrypto]

lean_exe standalone_consumer where
  root := `tests.StandaloneConsumer
