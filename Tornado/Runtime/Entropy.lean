import Lean

/-!
Native Lean access to the Unix kernel CSPRNG device. This relies on the host
OS to implement `/dev/urandom` correctly and on Lean's file-read primitive to
return its bytes unchanged. It does not use Lean's `IO.getRandomBytes`, whose
documented contract does not guarantee cryptographic strength.
-/

namespace Tornado.Runtime.Entropy

/-- Read exactly `count` bytes from the Unix kernel CSPRNG. A short read is
    retried; EOF or an oversized request fails closed. The handle is scoped to
    this operation and is released by Lean's runtime afterwards. -/
def readKernelRandom (count : Nat) : IO ByteArray := do
  if count == 0 || count > 4096 then
    throw <| IO.userError "CSPRNG request must contain 1..4096 bytes."
  let handle ← IO.FS.Handle.mk "/dev/urandom" .read
  let mut output := ByteArray.empty
  for _ in [0:count] do
    if output.size == count then return output
    let chunk ← handle.read (count - output.size).toUSize
    if chunk.isEmpty || chunk.size > count - output.size then
      throw <| IO.userError "Kernel CSPRNG returned an invalid or empty read."
    output := output ++ chunk
  if output.size != count then
    throw <| IO.userError "Kernel CSPRNG returned too few bytes."
  return output

end Tornado.Runtime.Entropy
