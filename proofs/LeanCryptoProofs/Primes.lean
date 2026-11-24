import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

/-! Kernel-checkable Lucas/Pratt certificates for the two BN254 primes.
The factor search is untrusted: products, recursive primality and every modular
power condition are checked by the proof terms below. No native evaluation axiom.
-/
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace LeanCrypto.Proofs.Primes

theorem prime_factor_of_prod (q : Nat) (prime : q.Prime) :
    ∀ factors : List Nat, q ∣ factors.prod → ∃ p ∈ factors, q ∣ p := by
  intro factors
  induction factors with
  | nil =>
    intro divides
    have equal : q = 1 := Nat.dvd_one.mp (by simpa using divides)
    exact False.elim (prime.ne_one equal)
  | cons first rest ih =>
    intro divides
    have parts : q ∣ first ∨ q ∣ rest.prod := prime.dvd_mul.mp (by simpa using divides)
    rcases parts with firstDivides | restDivides
    · exact ⟨first, by simp, firstDivides⟩
    · obtain ⟨p, member, divides⟩ := ih restDivides
      exact ⟨p, by simp [member], divides⟩

theorem prime_from_factors (p generator : Nat) (factors : List Nat)
    (product : factors.prod = p - 1)
    (primes : ∀ q ∈ factors, q.Prime)
    (full : (generator : ZMod p) ^ (p - 1) = 1)
    (proper : ∀ q ∈ factors, (generator : ZMod p) ^ ((p - 1) / q) ≠ 1) : p.Prime := by
  apply lucas_primality p (generator : ZMod p) full
  intro q prime divides
  obtain ⟨factor, member, factorDivides⟩ := prime_factor_of_prod q prime factors (by rwa [product])
  have equal : q = factor := (Nat.prime_dvd_prime_iff_eq prime (primes factor member)).mp factorDivides
  subst q
  exact proper factor member

theorem prime_2 : Nat.Prime 2 := by norm_num

theorem prime_3 : Nat.Prime 3 := by norm_num

theorem prime_13 : Nat.Prime 13 := by norm_num

theorem prime_29 : Nat.Prime 29 := by norm_num

theorem prime_67 : Nat.Prime 67 := by norm_num

theorem prime_229 : Nat.Prime 229 := by norm_num

theorem prime_311 : Nat.Prime 311 := by norm_num

theorem prime_983 : Nat.Prime 983 := by norm_num

theorem prime_5 : Nat.Prime 5 := by norm_num

theorem prime_11 : Nat.Prime 11 := by norm_num

theorem prime_5501 : Nat.Prime 5501 := by
  apply prime_from_factors 5501 2 [2, 2, 5, 5, 5, 11] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_5
    · exact prime_5
    · exact prime_11
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_11003 : Nat.Prime 11003 := by
  apply prime_from_factors 11003 2 [2, 5501] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact prime_2
    · exact prime_5501
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_7 : Nat.Prime 7 := by norm_num

theorem prime_17 : Nat.Prime 17 := by norm_num

theorem prime_4999 : Nat.Prime 4999 := by
  apply prime_from_factors 4999 3 [2, 3, 7, 7, 17] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_7
    · exact prime_17
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_41 : Nat.Prime 41 := by norm_num

theorem prime_3691 : Nat.Prime 3691 := by
  apply prime_from_factors 3691 2 [2, 3, 3, 5, 41] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_5
    · exact prime_41
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_405928799 : Nat.Prime 405928799 := by
  apply prime_from_factors 405928799 22 [2, 11, 3691, 4999] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_3691
    · exact prime_4999
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_19 : Nat.Prime 19 := by norm_num

theorem prime_37 : Nat.Prime 37 := by norm_num

theorem prime_233 : Nat.Prime 233 := by norm_num

theorem prime_327599 : Nat.Prime 327599 := by
  apply prime_from_factors 327599 19 [2, 19, 37, 233] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_37
    · exact prime_233
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_11465965001 : Nat.Prime 11465965001 := by
  apply prime_from_factors 11465965001 3 [2, 2, 2, 5, 5, 5, 5, 7, 327599] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_5
    · exact prime_5
    · exact prime_5
    · exact prime_7
    · exact prime_327599
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_271 : Nat.Prime 271 := by norm_num

theorem prime_1853641 : Nat.Prime 1853641 := by
  apply prime_from_factors 1853641 17 [2, 2, 2, 3, 3, 5, 19, 271] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_271
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_109 : Nat.Prime 109 := by norm_num

theorem prime_1231 : Nat.Prime 1231 := by
  apply prime_from_factors 1231 3 [2, 3, 5, 41] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_4562087 : Nat.Prime 4562087 := by
  apply prime_from_factors 4562087 5 [2, 17, 109, 1231] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_109
    · exact prime_1231
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_73 : Nat.Prime 73 := by norm_num

theorem prime_89 : Nat.Prime 89 := by norm_num

theorem prime_2221 : Nat.Prime 2221 := by
  apply prime_from_factors 2221 2 [2, 2, 3, 5, 37] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_13327 : Nat.Prime 13327 := by
  apply prime_from_factors 13327 3 [2, 3, 2221] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_2221
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_173171039 : Nat.Prime 173171039 := by
  apply prime_from_factors 173171039 13 [2, 73, 89, 13327] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_73
    · exact prime_89
    · exact prime_13327
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_911 : Nat.Prime 911 := by norm_num

theorem prime_127 : Nat.Prime 127 := by norm_num

theorem prime_3557 : Nat.Prime 3557 := by
  apply prime_from_factors 3557 2 [2, 2, 7, 127] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_7
    · exact prime_127
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_1263766531 : Nat.Prime 1263766531 := by
  apply prime_from_factors 1263766531 10 [2, 3, 5, 13, 911, 3557] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_13
    · exact prime_911
    · exact prime_3557
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_35385462869 : Nat.Prime 35385462869 := by
  apply prime_from_factors 35385462869 2 [2, 2, 7, 1263766531] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_7
    · exact prime_1263766531
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_2480874801745591 : Nat.Prime 2480874801745591 := by
  apply prime_from_factors 2480874801745591 6 [2, 3, 3, 5, 19, 41, 35385462869] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_5
    · exact prime_19
    · exact prime_41
    · exact prime_35385462869
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_13427688667394608761327070753331941386769 : Nat.Prime 13427688667394608761327070753331941386769 := by
  apply prime_from_factors 13427688667394608761327070753331941386769 17 [2, 2, 2, 2, 3, 7, 11, 1853641, 4562087, 173171039, 2480874801745591] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_1853641
    · exact prime_4562087
    · exact prime_173171039
    · exact prime_2480874801745591
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_21888242871839275222246405745257275088696311157297823662689037894645226208583 : Nat.Prime 21888242871839275222246405745257275088696311157297823662689037894645226208583 := by
  apply prime_from_factors 21888242871839275222246405745257275088696311157297823662689037894645226208583 3 [2, 3, 3, 13, 29, 67, 229, 311, 983, 11003, 405928799, 11465965001, 13427688667394608761327070753331941386769] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_67
    · exact prime_229
    · exact prime_311
    · exact prime_983
    · exact prime_11003
    · exact prime_405928799
    · exact prime_11465965001
    · exact prime_13427688667394608761327070753331941386769
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_449 : Nat.Prime 449 := by norm_num

theorem prime_237073 : Nat.Prime 237073 := by
  apply prime_from_factors 237073 15 [2, 2, 2, 2, 3, 11, 449] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_449
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_107 : Nat.Prime 107 := by norm_num

theorem prime_661 : Nat.Prime 661 := by norm_num

theorem prime_31 : Nat.Prime 31 := by norm_num

theorem prime_93001 : Nat.Prime 93001 := by
  apply prime_from_factors 93001 14 [2, 2, 2, 3, 5, 5, 5, 31] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5
    · exact prime_5
    · exact prime_31
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_12048837557 : Nat.Prime 12048837557 := by
  apply prime_from_factors 12048837557 2 [2, 2, 7, 7, 661, 93001] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_7
    · exact prime_7
    · exact prime_661
    · exact prime_93001
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_5156902474397 : Nat.Prime 5156902474397 := by
  apply prime_from_factors 5156902474397 2 [2, 2, 107, 12048837557] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_107
    · exact prime_12048837557
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_1670836401704629 : Nat.Prime 1670836401704629 := by
  apply prime_from_factors 1670836401704629 2 [2, 2, 3, 3, 3, 3, 5156902474397] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_5156902474397
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_823 : Nat.Prime 823 := by norm_num

theorem prime_47 : Nat.Prime 47 := by norm_num

theorem prime_223 : Nat.Prime 223 := by norm_num

theorem prime_20963 : Nat.Prime 20963 := by
  apply prime_from_factors 20963 2 [2, 47, 223] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact prime_2
    · exact prime_47
    · exact prime_223
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_41927 : Nat.Prime 41927 := by
  apply prime_from_factors 41927 5 [2, 20963] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact prime_2
    · exact prime_20963
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_1593227 : Nat.Prime 1593227 := by
  apply prime_from_factors 1593227 2 [2, 19, 41927] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact prime_2
    · exact prime_19
    · exact prime_41927
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_83 : Nat.Prime 83 := by norm_num

theorem prime_379 : Nat.Prime 379 := by norm_num

theorem prime_409 : Nat.Prime 409 := by norm_num

theorem prime_1637 : Nat.Prime 1637 := by
  apply prime_from_factors 1637 2 [2, 2, 409] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_409
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_853 : Nat.Prime 853 := by norm_num

theorem prime_639533339 : Nat.Prime 639533339 := by
  apply prime_from_factors 639533339 2 [2, 229, 853, 1637] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_229
    · exact prime_853
    · exact prime_1637
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_65865678001877903 : Nat.Prime 65865678001877903 := by
  apply prime_from_factors 65865678001877903 5 [2, 83, 379, 1637, 639533339] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_83
    · exact prime_379
    · exact prime_1637
    · exact prime_639533339
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_13818364434197438864469338081 : Nat.Prime 13818364434197438864469338081 := by
  apply prime_from_factors 13818364434197438864469338081 3 [2, 2, 2, 2, 2, 5, 823, 1593227, 65865678001877903] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_823
    · exact prime_1593227
    · exact prime_65865678001877903
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem prime_21888242871839275222246405745257275088548364400416034343698204186575808495617 : Nat.Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617 := by
  apply prime_from_factors 21888242871839275222246405745257275088548364400416034343698204186575808495617 5 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 13, 29, 983, 11003, 237073, 405928799, 1670836401704629, 13818364434197438864469338081] (by decide)
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_13
    · exact prime_29
    · exact prime_983
    · exact prime_11003
    · exact prime_237073
    · exact prime_405928799
    · exact prime_1670836401704629
    · exact prime_13818364434197438864469338081
  · reduce_mod_char
  · intro q member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide

theorem bn254_base_prime : Nat.Prime 21888242871839275222246405745257275088696311157297823662689037894645226208583 := prime_21888242871839275222246405745257275088696311157297823662689037894645226208583
theorem bn254_scalar_prime : Nat.Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617 := prime_21888242871839275222246405745257275088548364400416034343698204186575808495617

end LeanCrypto.Proofs.Primes

#print axioms LeanCrypto.Proofs.Primes.prime_factor_of_prod
#print axioms LeanCrypto.Proofs.Primes.prime_from_factors
#print axioms LeanCrypto.Proofs.Primes.prime_2
#print axioms LeanCrypto.Proofs.Primes.prime_3
#print axioms LeanCrypto.Proofs.Primes.prime_13
#print axioms LeanCrypto.Proofs.Primes.prime_29
#print axioms LeanCrypto.Proofs.Primes.prime_67
#print axioms LeanCrypto.Proofs.Primes.prime_229
#print axioms LeanCrypto.Proofs.Primes.prime_311
#print axioms LeanCrypto.Proofs.Primes.prime_983
#print axioms LeanCrypto.Proofs.Primes.prime_5
#print axioms LeanCrypto.Proofs.Primes.prime_11
#print axioms LeanCrypto.Proofs.Primes.prime_5501
#print axioms LeanCrypto.Proofs.Primes.prime_11003
#print axioms LeanCrypto.Proofs.Primes.prime_7
#print axioms LeanCrypto.Proofs.Primes.prime_17
#print axioms LeanCrypto.Proofs.Primes.prime_4999
#print axioms LeanCrypto.Proofs.Primes.prime_41
#print axioms LeanCrypto.Proofs.Primes.prime_3691
#print axioms LeanCrypto.Proofs.Primes.prime_405928799
#print axioms LeanCrypto.Proofs.Primes.prime_19
#print axioms LeanCrypto.Proofs.Primes.prime_37
#print axioms LeanCrypto.Proofs.Primes.prime_233
#print axioms LeanCrypto.Proofs.Primes.prime_327599
#print axioms LeanCrypto.Proofs.Primes.prime_11465965001
#print axioms LeanCrypto.Proofs.Primes.prime_271
#print axioms LeanCrypto.Proofs.Primes.prime_1853641
#print axioms LeanCrypto.Proofs.Primes.prime_109
#print axioms LeanCrypto.Proofs.Primes.prime_1231
#print axioms LeanCrypto.Proofs.Primes.prime_4562087
#print axioms LeanCrypto.Proofs.Primes.prime_73
#print axioms LeanCrypto.Proofs.Primes.prime_89
#print axioms LeanCrypto.Proofs.Primes.prime_2221
#print axioms LeanCrypto.Proofs.Primes.prime_13327
#print axioms LeanCrypto.Proofs.Primes.prime_173171039
#print axioms LeanCrypto.Proofs.Primes.prime_911
#print axioms LeanCrypto.Proofs.Primes.prime_127
#print axioms LeanCrypto.Proofs.Primes.prime_3557
#print axioms LeanCrypto.Proofs.Primes.prime_1263766531
#print axioms LeanCrypto.Proofs.Primes.prime_35385462869
#print axioms LeanCrypto.Proofs.Primes.prime_2480874801745591
#print axioms LeanCrypto.Proofs.Primes.prime_13427688667394608761327070753331941386769
#print axioms LeanCrypto.Proofs.Primes.prime_21888242871839275222246405745257275088696311157297823662689037894645226208583
#print axioms LeanCrypto.Proofs.Primes.prime_449
#print axioms LeanCrypto.Proofs.Primes.prime_237073
#print axioms LeanCrypto.Proofs.Primes.prime_107
#print axioms LeanCrypto.Proofs.Primes.prime_661
#print axioms LeanCrypto.Proofs.Primes.prime_31
#print axioms LeanCrypto.Proofs.Primes.prime_93001
#print axioms LeanCrypto.Proofs.Primes.prime_12048837557
#print axioms LeanCrypto.Proofs.Primes.prime_5156902474397
#print axioms LeanCrypto.Proofs.Primes.prime_1670836401704629
#print axioms LeanCrypto.Proofs.Primes.prime_823
#print axioms LeanCrypto.Proofs.Primes.prime_47
#print axioms LeanCrypto.Proofs.Primes.prime_223
#print axioms LeanCrypto.Proofs.Primes.prime_20963
#print axioms LeanCrypto.Proofs.Primes.prime_41927
#print axioms LeanCrypto.Proofs.Primes.prime_1593227
#print axioms LeanCrypto.Proofs.Primes.prime_83
#print axioms LeanCrypto.Proofs.Primes.prime_379
#print axioms LeanCrypto.Proofs.Primes.prime_409
#print axioms LeanCrypto.Proofs.Primes.prime_1637
#print axioms LeanCrypto.Proofs.Primes.prime_853
#print axioms LeanCrypto.Proofs.Primes.prime_639533339
#print axioms LeanCrypto.Proofs.Primes.prime_65865678001877903
#print axioms LeanCrypto.Proofs.Primes.prime_13818364434197438864469338081
#print axioms LeanCrypto.Proofs.Primes.prime_21888242871839275222246405745257275088548364400416034343698204186575808495617
#print axioms LeanCrypto.Proofs.Primes.bn254_base_prime
#print axioms LeanCrypto.Proofs.Primes.bn254_scalar_prime
