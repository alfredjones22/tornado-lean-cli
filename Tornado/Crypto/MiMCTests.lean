import Tornado.Crypto.MiMC

/-! MiMC constants, permutation, and tree-parent vectors from the pinned
    micro-zk-proofs and Kohaku MiMC-tree packages. -/

namespace Tornado.Crypto.MiMCTests

private def check (label actual expected : String) : IO Unit :=
  if actual == expected then pure ()
  else throw <| IO.userError s!"{label}: got {actual}, expected {expected}"

private def unwrap (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw <| IO.userError s!"{label}: {error}"

def main : IO Unit := do
  let constants := mimcConstants
  check "constants size" (toString constants.size) "220"
  check "iv" (toString mimcIV)
    "20726889000739135966540349393715347422209337226408207985583375257700203118924"
  for (index, expected) in (#[(0, "0"),
    (1, "7120861356467848435263064379192047478074060781135320967663101236819528304084"),
    (2, "5024705281721889198577876690145313457398658950011302225525409148828000436681"),
    (3, "17980351014018068290387269214713820287804403312720763401943303895585469787384"),
    (4, "19886576439381707240399940949310933992335779767309383709787331470398675714258"),
    (5, "1213715278223786725806155661738676903520350859678319590331207960381534602599"),
    (10, "4798196928559910300796064665904583125427459076060519468052008159779219347957"),
    (100, "2821730726367472966906149684046356272806484545281639696873240305052362149654"),
    (218, "2119542016932434047340813757208803962484943912710204325088879681995922344971"),
    (219, "0")] : Array (Nat × String)) do
    check s!"constant {index}" (toString constants[index]!) expected
  let (left, right) ← unwrap "permutation" (mimcPermutationWith constants 1 2 0)
  check "permutation left" (toString left)
    "18635233944808208882966072806738683940518399005033812161015824420796221493526"
  check "permutation right" (toString right)
    "19140941253229475753487820384337024263930106104819057875453076717944303574361"
  for (label, inputs, expected) in (#[("empty", #[], "0"),
    ("one zero", #[0], "14543742788565021628577424853847564376151732847602780516906950225481254681152"),
    ("one one", #[1], "8792246410719720074073794355580855662772292438409936688983564419486782556587"),
    ("pair zero", #[0, 0], "20636625426020718969131298365984859231982649550971729229988535915544421356929"),
    ("pair 1 2", #[1, 2], "19814528709687996974327303300007262407299502847885145507292406548098437687919"),
    ("pair 123 456", #[123, 456], "15359284944440322468559095640462360728117765773581058256703006539091417328113"),
    ("triple", #[1, 2, 3], "13347232259103605288126215296295968657023270572136673486116911774162409637522")]
      : Array (String × Array Nat × String)) do
    let value ← unwrap label (mimcMultiHashWith constants inputs)
    check label (toString value) expected
  let invalidRejected := match mimcHashPairWith #[] 1 2 with
    | .ok _ => false
    | .error _ => true
  check "bad constants rejected" (toString invalidRejected) "true"
  IO.println "MiMC sponge: 21 compatibility checks passed"

end Tornado.Crypto.MiMCTests

def main : IO Unit := Tornado.Crypto.MiMCTests.main
