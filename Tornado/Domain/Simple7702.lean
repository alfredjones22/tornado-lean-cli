import Std

/-! Shared public Simple7702 identity and exact EIP-7702 code classification.
No ABI encoder, RPC adapter, or transaction sender participates in routing. -/

namespace Tornado.Domain.Simple7702

def implementation : Nat := 0xe6cae83bde06e4c305530e199d7217f42808555b

def implementationHash : String :=
  "0xcc7b633aef4b2543cb8f37522adf1a401f910f0f6b2430c1eecc11f401ccfcf3"

/-- The implementation occupies exactly 20 big-endian address bytes. -/
def implementationBytes : ByteArray :=
  ByteArray.mk (Array.ofFn fun index : Fin 20 =>
    UInt8.ofNat (implementation / 256 ^ (19 - index.val) % 256))

def delegationPrefix : ByteArray := ByteArray.mk #[0xef, 0x01, 0x00]

def designator : ByteArray := delegationPrefix ++ implementationBytes

/-- Only the exact 23-byte EIP-7702 designator format can be replaced by a
forced delegation. A bytecode prefix without the exact length is insufficient. -/
def isDelegation (code : ByteArray) : Bool :=
  code.size == 23 && (code.extract 0 3).data == delegationPrefix.data

/-- Reuse requires the exact pinned target, not just any delegation prefix. -/
def isCompatible (code : ByteArray) : Bool := code.data == designator.data

def mayForceDelegated (code : ByteArray) : Bool := code.isEmpty || isDelegation code

theorem implementationBytes_size : implementationBytes.size = 20 := by
  decide +kernel

theorem designator_size : designator.size = 23 := by
  decide +kernel

theorem designator_isDelegation : isDelegation designator = true := by
  decide +kernel

theorem isDelegation_iff (code : ByteArray) :
    isDelegation code = true ↔ code.size = 23 ∧ (code.extract 0 3).data = delegationPrefix.data := by
  simp [isDelegation]

theorem isCompatible_iff (code : ByteArray) :
    isCompatible code = true ↔ code.data = designator.data := by
  simp [isCompatible]

theorem mayForceDelegated_iff (code : ByteArray) :
    mayForceDelegated code = true ↔ code.isEmpty = true ∨ isDelegation code = true := by
  simp [mayForceDelegated]

end Tornado.Domain.Simple7702

#print axioms Tornado.Domain.Simple7702.implementationBytes_size
#print axioms Tornado.Domain.Simple7702.designator_size
#print axioms Tornado.Domain.Simple7702.designator_isDelegation
#print axioms Tornado.Domain.Simple7702.isDelegation_iff
#print axioms Tornado.Domain.Simple7702.isCompatible_iff
#print axioms Tornado.Domain.Simple7702.mayForceDelegated_iff
