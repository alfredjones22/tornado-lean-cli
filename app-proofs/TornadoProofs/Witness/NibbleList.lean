import TornadoProofs.Witness.NibbleObservation

set_option autoImplicit false
namespace TornadoProofs.Witness.Source
open LeanCrypto.Proofs.BabyJubjubWindows

theorem byteDigits_get (bytes : List UInt8) (index : Nat) (bound : index<2*bytes.length) :
    (byteDigits bytes)[index]! = nativeNibble (if index%2=0 then (bytes[index/2]!).toNat%16 else (bytes[index/2]!).toNat/16) := by
  induction bytes generalizing index with
  | nil => simp at bound
  | cons byte rest ih =>
    cases index with
    | zero => rfl
    | succ index =>
      cases index with
      | zero => rfl
      | succ index =>
        have tailBound : index<2*rest.length := by simp only [List.length_cons] at bound; omega
        have quotient : (index+2)/2=index/2+1 := by omega
        have remainder : (index+2)%2=index%2 := by omega
        change (byteDigits rest)[index]! = nativeNibble (if (index+2)%2=0 then
          ((byte::rest)[(index+2)/2]!).toNat%16 else ((byte::rest)[(index+2)/2]!).toNat/16)
        rw [quotient,remainder,List.getElem!_cons_succ]
        exact ih index tailBound

theorem extract_bytes_length (bytes : ByteArray) (start count : Nat) (within : start+count≤bytes.size) :
    (bytes.extract start (start+count)).data.toList.length=count := by
  change (bytes.extract start (start+count)).size=count
  rw [ByteArray.size_extract,Nat.min_eq_left within,Nat.add_sub_cancel_left]

theorem extract_bytes_get (bytes : ByteArray) (start count index : Nat)
    (within : start+count≤bytes.size) (bound : index<count) :
    ((bytes.extract start (start+count)).data.toList)[index]! = bytes.get! (start+index) := by
  have extractedBound : index<(bytes.extract start (start+count)).data.toList.length := by
    rw [extract_bytes_length bytes start count within]
    exact bound
  have dataBound : start+index<bytes.data.size := by change start+index<bytes.size; omega
  rw [getElem!_pos _ index extractedBound,Array.getElem_toList]
  simp only [ByteArray.data_extract,Array.getElem_extract,byteGet_data,
    getElem!_pos bytes.data (start+index) dataBound]

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.byteDigits_get
#print axioms TornadoProofs.Witness.Source.extract_bytes_length
#print axioms TornadoProofs.Witness.Source.extract_bytes_get
