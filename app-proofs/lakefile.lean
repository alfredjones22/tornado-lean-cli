import Lake
open Lake DSL

package tornadoApplicationProofs where
  version := v!"0.1.0"

require tornadoLeanCli from ".."
require leanCryptoProofs from "../proofs"

@[default_target]
lean_lib TornadoProofs where
  roots := #[`TornadoProofs]
