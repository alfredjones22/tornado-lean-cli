import Tornado.Runtime.Entropy

open Tornado.Runtime.Entropy

def main : IO UInt32 := do
  let first ← readKernelRandom 32
  let second ← readKernelRandom 16
  if first.size != 32 || second.size != 16 then
    IO.eprintln "Kernel CSPRNG did not return the requested number of bytes."
    return 1
  let rejectedZero ← try
    let _ ← readKernelRandom 0
    pure false
  catch _ => pure true
  let rejectedHuge ← try
    let _ ← readKernelRandom 4097
    pure false
  catch _ => pure true
  if !rejectedZero || !rejectedHuge then
    IO.eprintln "Kernel CSPRNG accepted an invalid request."
    return 1
  IO.println "PASS: native Lean Unix kernel CSPRNG exact-length reads and fail-closed bounds"
  return 0
