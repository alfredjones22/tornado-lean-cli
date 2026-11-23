import Tornado.Crypto.Pedersen

/-! BabyJubJub Pedersen vectors from the pinned `micro-zk-proofs/pedersen.js`.
    The 31-byte cases model nullifier hashes; 62-byte cases model commitments. -/

namespace Tornado.Crypto.PedersenTests

private def repeated (count : Nat) (byte : UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for _ in [0:count] do out := out.push byte
  return out

private def sequence (count : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:count] do out := out.push (UInt8.ofNat (i % 256))
  return out

private def hex (bytes : ByteArray) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut out := ""
  for byte in bytes.data do
    let n := byte.toNat
    out := out.push digits[n / 16]!
    out := out.push digits[n % 16]!
  return out

private def check (label : String) (input : ByteArray)
    (expectedBytes expectedX : String) : IO Unit := do
  let hash ← match pedersenHash input with
    | .ok value => pure value
    | .error error => throw <| IO.userError s!"{label}: {error}"
  let actualBytes := hex hash
  if actualBytes != expectedBytes then
    throw <| IO.userError s!"{label} bytes: got {actualBytes}, expected {expectedBytes}"
  let x ← match pedersenX input with
    | .ok value => pure value
    | .error error => throw <| IO.userError s!"{label} x: {error}"
  if toString x != expectedX then
    throw <| IO.userError s!"{label} x: got {x}, expected {expectedX}"

def main : IO Unit := do
  check "empty" (repeated 0 0)
    "0100000000000000000000000000000000000000000000000000000000000000" "0"
  check "one zero" (repeated 1 0)
    "4342ded81a9c9adc4472f5732febf9b1018ed754ccaf8f0ce9c5d09e6400e30d"
    "2713984616998054873485125083403724179682140658671583177610038376665425019990"
  check "one ff" (repeated 1 0xff)
    "86ce5e50636d62ba5f1ceb78fd04d5193ac450276cb83d8e9239bfdd8491f116"
    "1873070862965687252761882076166765944314336865899891116413426710085435693186"
  check "25 sequential" (sequence 25)
    "1329a7ebe58a025ffddde4f9e3018caa4af839b0304579feb2355cb871590715"
    "8740134997096674099124989223533824428301970684215901254672147028059070282494"
  check "26 sequential" (sequence 26)
    "21ec02d20b056813a0bc784f0ced2a1a60104fb109425b5ab632235ce40edaa1"
    "16149645834192032477094204586047270807983314866742043969303927055315111181481"
  check "50 sequential" (sequence 50)
    "b29770d41103c7f410628bd33287629ce321c0f1ae99852d7134340033e7b62f"
    "9817195640812386370217499949445215192162354332403172832743836118357619319160"
  check "51 sequential" (sequence 51)
    "d25f127f66dac0ad55a84ce38e92146cb26f26330ff0fb00178426b712e09517"
    "5932082649986980504800594748099768951294172177578919319294852001476588179118"
  check "31 zero" (repeated 31 0)
    "7a43ff92977df874316582192d43bc13f286fb02d39cd26a77ed074d799d3c0f"
    "5452775741701204091286931084132339051844063526919666957744016314099542105679"
  check "31 sequential" (sequence 31)
    "71f54bb375c31bff222c15137f1ec312190f10f9bcf780b963750fe33848fda9"
    "18738152560730810883409740444671742160439923181827017630915693874141782944352"
  check "31 ff" (repeated 31 0xff)
    "520bdb680a9a0ef18f0ec1b28933b6ecc68184431477c01f7e59381dfc41319c"
    "11958727323653992140393347419347735936852777297016280498319205036343819833236"
  check "62 zero" (repeated 62 0)
    "79cf702804aeae08c7d181d467372bcb84e5fdfec11926a65e8437909b2a112a"
    "10606596081724992687836412044438397210272029250652246605286526701104132431192"
  check "62 sequential" (sequence 62)
    "a4e59877416ed78ad99691660b749c47c9e9d062b291d1475b45833fc3c62c11"
    "3145092461348658948514230258287571821492383302559722824466238201392794160359"
  check "62 ab" (repeated 62 0xab)
    "d03a9c9bc0bfc1d27e023911039751e7a47d724fc408a1e5fb736a43cb705e06"
    "321510174157933478059751906220227217604756403925110169244765922583439536205"
  check "75 sequential" (sequence 75)
    "4e703b8c13e2861724f24f7c56dd6e06fdc87d161bdd0a9abcbf38511283188c"
    "13639831652642287281306308238384577995655561359840553019068982563800456856967"
  check "76 sequential" (sequence 76)
    "4b368664c56b0f6ec88a50cdc1a4d4f8e5643410cb48ca85a42fde215eba3e29"
    "8244751635112984143118329588173574561758443659190789037645202978307906153174"
  check "125 sequential" (sequence 125)
    "78298856caeadd0498077109ec97c63be1c995333d60f934ab2b7c0be07c8009"
    "7292370809811359281360537888524580762835971639505223756279919003590325648241"
  IO.println "Pedersen/BabyJubJub: 16 compatibility vectors passed"

end Tornado.Crypto.PedersenTests

def main : IO Unit := Tornado.Crypto.PedersenTests.main
