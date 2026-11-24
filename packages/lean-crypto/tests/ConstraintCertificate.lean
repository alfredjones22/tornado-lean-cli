import LeanCrypto.Groth16.ConstraintCertificate

open LeanCrypto.Groth16.ConstraintCertificate

private def require (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

/-- Synthetic public equations only; no witness or note is read. -/
def main : IO Unit := do
  let identity : Equation := ⟨[(0, 1)], [(0, 1)], [(0, 1)]⟩
  let identityTrace : Certificate := ⟨#[], #[], #[⟨[], [], []⟩], #[⟨0, 1⟩]⟩
  require ((prepareCertificate 1 1 #[] #[identity] #[identity] identityTrace).isOk)
    "Identity certificate rejected."
  require (!(checkCertificate 1 1 #[] #[identity] #[identity]
    {identityTrace with «matches» := #[⟨0, 0⟩]}).isOk) "Zero scale accepted."
  require (!(checkCertificate 1 1 #[] #[identity] #[identity]
    {identityTrace with «matches» := #[⟨1, 1⟩]}).isOk) "Invalid target source accepted."
  require (!(checkCertificate 1 1 #[] #[identity] #[identity]
    {identityTrace with steps := #[.scale 10 1]}).isOk) "Forward derivation reference accepted."
  require (!(checkCertificate 1 1 #[] #[identity] #[identity]
    {identityTrace with rules := #[⟨0, 0⟩]}).isOk) "Constant pivot accepted."
  require (!(checkCertificate 1 1 #[] #[identity] #[identity]
    {identityTrace with substitutions := #[⟨[1], [], []⟩]}).isOk) "Invalid substitution accepted."
  let source : Equation := ⟨[(1, 1)], [(1, 1)], [(1, 1)]⟩
  let rule : Linear := [(0, modulus - 1), (1, 1)]
  let elimination : Certificate := ⟨#[], #[⟨1, 0⟩], #[⟨[0], [0], [0]⟩], #[⟨0, 1⟩]⟩
  require ((prepareCertificate 1 2 #[rule] #[source] #[identity] elimination).isOk)
    "Valid auxiliary elimination rejected."
  let changed := {identity with c := [(0, 2)]}
  require (!(checkCertificate 1 2 #[rule] #[source] #[changed] elimination).isOk)
    "Changed target constant accepted."
  require (!(checkCertificate 1 2 #[rule] #[source] #[identity]
    {elimination with rules := #[⟨1, 1⟩]}).isOk) "Nonexistent basis row accepted."
  require (!(checkCertificate 1 2 #[rule] #[source] #[identity]
    {elimination with «matches» := #[⟨0, modulus⟩]}).isOk) "Noncanonical scale accepted."
  require (!(checkCertificate 1 2 #[[(0, modulus), (1, 1)]] #[source] #[identity] elimination).isOk)
    "Noncanonical input coefficient accepted."
  require (!(checkCertificate 0 2 #[rule] #[source] #[identity] elimination).isOk)
    "Empty original assignment dimension accepted."
  require (!(checkCertificate 2 1 #[rule] #[source] #[identity] elimination).isOk)
    "Reversed dimensions accepted."
  let scaled : Equation := ⟨[(0, 2)], [(0, 1)], [(0, 2)]⟩
  require ((checkCertificate 1 1 #[] #[identity] #[scaled]
    {identityTrace with «matches» := #[⟨0, 2⟩]}).isOk)
    "Nonzero rescaling of the zero polynomial rejected."
  IO.println "PASS: public constraint certificates, auxiliary elimination, target tamper and 14 boundary cases"
