import Lean
import Tornado.Protocol.Groth16R1CS
import Tornado.Protocol.ProvingKey

/-!
BN254 Fr radix-two FFT for the pinned Tornado Groth16 prover. The root of
unity is derived from NQR 7, matching the legacy websnark key and the pinned
micro-zk-proofs configuration. The polynomial high-half computation uses the
stored sparse A/B records; C cannot affect coefficients of degree >= m.

This module is variable-time bigint code and does not produce a Groth16 proof.
-/

namespace Tornado.Protocol.FrFFT

open Tornado.Protocol.Groth16R1CS
open Tornado.Protocol.ProvingKey

def modulus : Nat := scalarPrime
def nqr : Nat := 7
def maximumSize : Nat := 65536
def provingDomainSize : Nat := 32768

def add (a b : Nat) : Nat := (a + b) % modulus
def sub (a b : Nat) : Nat := (a + modulus - b % modulus) % modulus
def mul (a b : Nat) : Nat := a * b % modulus

def powMod (base exponent : Nat) : Nat := Id.run do
  let mut result := 1
  let mut value := base % modulus
  let mut n := exponent
  while n > 0 do
    if n % 2 == 1 then result := mul result value
    value := mul value value
    n := n / 2
  return result

/-- Inversion verifies the multiplicative equation rather than trusting a
    primality claim about the modulus. -/
def inverse (value : Nat) : Except String Nat :=
  if value % modulus == 0 then .error "Fr zero has no inverse."
  else
    let candidate := powMod value (modulus - 2)
    if mul value candidate == 1 then .ok candidate
    else .error "Fr inverse check failed."

theorem inverse_sound (value candidate : Nat)
    (h : inverse value = .ok candidate) : mul value candidate == 1 := by
  cases hz : value % modulus == 0 with
  | true => simp [inverse, hz] at h
  | false =>
    cases hc : mul value (powMod value (modulus - 2)) == 1 with
    | false => simp [inverse, hz, hc] at h
    | true =>
      simp [inverse, hz, hc] at h
      cases h
      exact hc

/-- Only power-of-two arrays up to the two-domain convolution size are
    accepted. The complete Tornado proving domain is 32768. -/
def validSize (n : Nat) : Bool :=
  n > 0 && n <= maximumSize && 2 ^ Nat.log2 n == n

def validRoot (n root : Nat) : Bool :=
  validSize n && (modulus - 1) % n == 0 && powMod root n == 1 &&
  !(n > 1 && powMod root (n / 2) == 1)

/-- Calculate and validate the exact root used by the pinned SDK. -/
def rootOfUnity (n : Nat) : Except String Nat :=
  if validRoot n (powMod nqr ((modulus - 1) / n)) then
    .ok (powMod nqr ((modulus - 1) / n))
  else .error "NQR 7 did not yield a valid root for this FFT length."

/-- An accepted root has passed every executable domain and exact-order
    guard. This theorem does not establish the general field group law. -/
theorem rootOfUnity_sound (n root : Nat)
    (h : rootOfUnity n = .ok root) : validRoot n root = true := by
  unfold rootOfUnity at h
  split at h
  · rename_i valid
    cases h
    exact valid
  · simp at h

def reverseBits (index bits : Nat) : Nat := Id.run do
  let mut value := index
  let mut result := 0
  for _ in [0:bits] do
    result := result * 2 + value % 2
    value := value / 2
  return result

/-- Natural-order radix-two DIT transform, with its output also in natural
    order. The inverse uses the inverse root and multiplies every result by
    the checked inverse of the transform size. -/
private def transform (input : Array Nat) (inverseDirection : Bool) :
    Except String (Array Nat) := do
  let n := input.size
  let root ← rootOfUnity n
  if !input.all (· < modulus) then throw "FFT input is outside BN254 Fr."
  let selectedRoot := if inverseDirection then powMod root (n - 1) else root
  let bits := Nat.log2 n
  let mut values := input
  for i in [0:n] do
    let j := reverseBits i bits
    if i < j then
      let left := values[i]!
      values := values.set! i values[j]!
      values := values.set! j left
  let mut width := 2
  while width <= n do
    let half := width / 2
    let step := powMod selectedRoot (n / width)
    for group in [0:n / width] do
      let start := group * width
      let mut twiddle := 1
      for j in [0:half] do
        let left := values[start + j]!
        let right := mul values[start + j + half]! twiddle
        values := values.set! (start + j) (add left right)
        values := values.set! (start + j + half) (sub left right)
        twiddle := mul twiddle step
    width := width * 2
  if inverseDirection then
    let nInverse ← inverse n
    values := values.map (fun value => mul value nInverse)
  return values

def fft (input : Array Nat) : Except String (Array Nat) :=
  transform input false

def ifft (input : Array Nat) : Except String (Array Nat) :=
  transform input true

def convolve (left right : Array Nat) : Except String (Array Nat) := do
  if left.isEmpty || right.isEmpty then
    throw "Convolution polynomials must be nonempty."
  let n := (left.size + right.size - 1).nextPowerOfTwo
  if !validSize n then throw "Convolution exceeds the supported FFT size."
  let a ← fft (left ++ Array.replicate (n - left.size) 0)
  let b ← fft (right ++ Array.replicate (n - right.size) 0)
  if a.size != b.size then throw "FFT convolution lengths differ."
  ifft ((a.zip b).map fun (x, y) => mul x y)

private def trimZeros (values : Array Nat) : Array Nat := Id.run do
  let mut result := values
  while !result.isEmpty && result[result.size - 1]! == 0 do
    result := result.pop
  return result

/-- Sum the authenticated key's signal-indexed sparse A or B polynomials
    into the domain evaluation vector. A caller can pass any parsed value, so
    indices and field bounds are checked again here. -/
def sumEvaluations (domainSize : Nat) (witness : Array Nat)
    (polynomials : Array Polynomial) : Except String (Array Nat) := do
  if !validSize domainSize || domainSize > provingDomainSize then
    throw "Invalid proving domain size."
  if witness.size != polynomials.size || witness.isEmpty ||
      !witness.all (· < modulus) then
    throw "Witness and sparse polynomial dimensions do not match."
  let mut evaluations := Array.replicate domainSize 0
  for signal in [0:witness.size] do
    let weight := witness[signal]!
    for entry in polynomials[signal]!.entries do
      if entry.constraint >= domainSize || entry.coefficient >= modulus then
        throw "Sparse polynomial entry is outside the proving domain."
      let index := entry.constraint
      evaluations := evaluations.set! index
        (add evaluations[index]! (mul weight entry.coefficient))
  return evaluations

/-- The pinned key stores A/B but omits C. Since deg(C) < m, C cannot alter
    the high half of the product A(x)B(x). This returns exactly that high half
    after trimming trailing zero coefficients, as micro-zk-proofs does. -/
def calculateH (domainSize : Nat) (witness : Array Nat)
    (polsA polsB : Array Polynomial) : Except String (Array Nat) := do
  if domainSize < 2 then throw "H polynomial domain must have at least two rows."
  let pA ← sumEvaluations domainSize witness polsA
  let pB ← sumEvaluations domainSize witness polsB
  let a ← ifft pA
  let b ← ifft pB
  let product ← convolve a b
  if product.size != 2 * domainSize then
    throw "Unexpected H polynomial convolution size."
  return trimZeros (product.extract domainSize product.size)

end Tornado.Protocol.FrFFT

#print axioms Tornado.Protocol.FrFFT.inverse_sound
#print axioms Tornado.Protocol.FrFFT.rootOfUnity_sound
