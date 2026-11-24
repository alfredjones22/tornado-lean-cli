import LeanCrypto.MiMCTree

/-! Tree roots and paths from pinned `@kohaku-eth/mimc-tree` for both a small
    3-level example and the real 20-level Tornado configuration. -/

namespace LeanCrypto.MiMCTreeTests

private def unwrap (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw <| IO.userError s!"{label}: {error}"

private def check (label actual expected : String) : IO Unit :=
  if actual == expected then pure ()
  else throw <| IO.userError s!"{label}: got {actual}, expected {expected}"

private def checkRoot (constants : Array Nat) (levels : Nat)
    (leaves : Array Nat) (expected : String) : IO MimcTree := do
  let tree ← unwrap "build tree" (buildMimcTreeWith constants leaves levels)
  check "tree root" (toString tree.root) expected
  return tree

def main : IO Unit := do
  let constants := mimcConstants
  let _ ← checkRoot constants 3 #[]
    "14506027710748750947258687001455876266559341618222612722926156490737302846427"
  let one ← checkRoot constants 3 #[1]
    "14817887234532324632578486942317778767513333548116388705259454362287888156301"
  let onePath ← unwrap "one path" (mimcProofAt one 0)
  check "one siblings" (toString onePath.siblings.toList)
    (toString ([21663839004416932945382355908790599225266501822907911457504978515578255421292,
      16923532097304556005972200564242292693309333953544141029519619077135960040221,
      7833458610320835472520144237082236871909694928684820466656733259024982655488] : List Nat))
  check "one directions" (toString onePath.pathIndices.toList) "[0, 0, 0]"
  check "one proof verifies" (toString (← unwrap "verify" (verifyMimcProofWith constants 1 onePath))) "true"
  let _ ← checkRoot constants 3 #[1, 2]
    "90705101527017413862904869340323827962397807757635781575579909868816800839"
  let three ← checkRoot constants 3 #[1, 2, 3]
    "17596747305458218445642002786820180646864609195847486855118685712873099810962"
  let path ← unwrap "three path" (mimcProofForLeaf three 3)
  check "three index" (toString path.index) "2"
  check "three directions" (toString path.pathIndices.toList) "[0, 1, 0]"
  check "three sibling 0" (toString path.siblings[0]!)
    "21663839004416932945382355908790599225266501822907911457504978515578255421292"
  check "three sibling 1" (toString path.siblings[1]!)
    "19814528709687996974327303300007262407299502847885145507292406548098437687919"
  check "three proof verifies" (toString (← unwrap "verify" (verifyMimcProofWith constants 3 path))) "true"
  check "wrong leaf fails" (toString (← unwrap "verify" (verifyMimcProofWith constants 4 path))) "false"
  let forgedIndex := { path with index := 1 }
  let indexRejected := match verifyMimcProofWith constants 3 forgedIndex with
    | .error _ => true
    | .ok _ => false
  check "forged index rejected" (toString indexRejected) "true"
  let _ ← checkRoot constants 20 #[]
    "18926336163373752588529320804722226672465218465546337267825102089394393880276"
  let _ ← checkRoot constants 20 #[1]
    "4768177824216143055519640784977157311673229774898220393681621414098673579769"
  let _ ← checkRoot constants 20 #[1, 2]
    "19250388085485041587583085418097442146754159803884683357829010263306957939672"
  let real ← checkRoot constants 20 #[1, 2, 3]
    "9689626096216832334627417845654134122170488617637736288368858062365673557464"
  let realPath ← unwrap "20-level path" (mimcProofAt real 2)
  check "20-level depth" (toString realPath.siblings.size) "20"
  check "20-level directions" (toString realPath.pathIndices.toList)
    "[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]"
  check "20-level proof verifies"
    (toString (← unwrap "verify" (verifyMimcProofWith constants 3 realPath))) "true"
  IO.println "MiMC Merkle: 14 root, path, and rejection checks passed"

end LeanCrypto.MiMCTreeTests

def main : IO Unit := LeanCrypto.MiMCTreeTests.main
