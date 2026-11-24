import LeanCrypto.Pedersen
import LeanCryptoProofs.Primes

/-! Numerical factor candidates are untrusted search data. Every factor product,
recursive prime certificate and modular-power condition is checked by Lean.
The public ACL2 Baby-Jubjub subgroup certificate provided independent factor
candidates: https://github.com/acl2/acl2/blob/master/books/kestrel/crypto/primes/baby-jubjub-subgroup-prime.lisp -/

open Lean Elab Term Meta
elab "actualPedersenSubgroupOrder" : term =>
  mkConstWithFreshMVarLevels (mkPrivateNameCore `LeanCrypto.Pedersen `LeanCrypto.subgroupOrder)

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace LeanCrypto.Proofs.BabyJubjubPrimes

abbrev subgroupOrder : Nat := actualPedersenSubgroupOrder

theorem prime_967 : Nat.Prime 967 := by
  norm_num

theorem prime_4139 : Nat.Prime 4139 := by
  norm_num

theorem prime_349 : Nat.Prime 349 := by
  norm_num

theorem prime_43189 : Nat.Prime 43189 := by
  norm_num

theorem prime_295049 : Nat.Prime 295049 := by
  norm_num

theorem prime_25485742523 : Nat.Prime 25485742523 := by
  apply Primes.prime_from_factors 25485742523 2 [2, 43189, 295049] (by decide +kernel)
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Primes.prime_2
    · exact prime_43189
    · exact prime_295049
  · reduce_mod_char
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals reduce_mod_char; decide +kernel

theorem prime_202795150404015601 : Nat.Prime 202795150404015601 := by
  apply Primes.prime_from_factors 202795150404015601 7 [2, 2, 2, 2, 3, 5, 5, 19, 349, 25485742523] (by decide +kernel)
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Primes.prime_2
    · exact Primes.prime_2
    · exact Primes.prime_2
    · exact Primes.prime_2
    · exact Primes.prime_3
    · exact Primes.prime_5
    · exact Primes.prime_5
    · exact Primes.prime_19
    · exact prime_349
    · exact prime_25485742523
  · reduce_mod_char
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide +kernel

theorem prime_431548080059745198929 : Nat.Prime 431548080059745198929 := by
  apply Primes.prime_from_factors 431548080059745198929 3 [2, 2, 2, 2, 7, 19, 202795150404015601] (by decide +kernel)
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Primes.prime_2
    · exact Primes.prime_2
    · exact Primes.prime_2
    · exact Primes.prime_2
    · exact Primes.prime_7
    · exact Primes.prime_19
    · exact prime_202795150404015601
  · reduce_mod_char
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide +kernel

theorem prime_32151195060611136810608359 : Nat.Prime 32151195060611136810608359 := by
  apply Primes.prime_from_factors 32151195060611136810608359 3 [2, 3, 3, 4139, 431548080059745198929] (by decide +kernel)
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact Primes.prime_2
    · exact Primes.prime_3
    · exact Primes.prime_3
    · exact prime_4139
    · exact prime_431548080059745198929
  · reduce_mod_char
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide +kernel

theorem prime_6323 : Nat.Prime 6323 := by
  norm_num

theorem prime_336157 : Nat.Prime 336157 := by
  norm_num

theorem prime_33409 : Nat.Prime 33409 := by
  norm_num

theorem prime_23 : Nat.Prime 23 := by
  norm_num

theorem prime_521 : Nat.Prime 521 := by
  norm_num

theorem prime_27743 : Nat.Prime 27743 := by
  norm_num

theorem prime_513749 : Nat.Prime 513749 := by
  norm_num

theorem prime_1061 : Nat.Prime 1061 := by
  norm_num

theorem prime_10206821 : Nat.Prime 10206821 := by
  apply Primes.prime_from_factors 10206821 2 [2, 2, 5, 13, 37, 1061] (by decide +kernel)
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Primes.prime_2
    · exact Primes.prime_2
    · exact Primes.prime_5
    · exact Primes.prime_13
    · exact Primes.prime_37
    · exact prime_1061
  · reduce_mod_char
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide +kernel

theorem prime_81654569 : Nat.Prime 81654569 := by
  apply Primes.prime_from_factors 81654569 3 [2, 2, 2, 10206821] (by decide +kernel)
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact Primes.prime_2
    · exact Primes.prime_2
    · exact Primes.prime_2
    · exact prime_10206821
  · reduce_mod_char
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide +kernel

theorem prime_27892051421815855583579 : Nat.Prime 27892051421815855583579 := by
  apply Primes.prime_from_factors 27892051421815855583579 2 [2, 23, 521, 27743, 513749, 81654569] (by decide +kernel)
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Primes.prime_2
    · exact prime_23
    · exact prime_521
    · exact prime_27743
    · exact prime_513749
    · exact prime_81654569
  · reduce_mod_char
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide +kernel

theorem prime_1863691091902891838383581623 : Nat.Prime 1863691091902891838383581623 := by
  apply Primes.prime_from_factors 1863691091902891838383581623 5 [2, 33409, 27892051421815855583579] (by decide +kernel)
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Primes.prime_2
    · exact prime_33409
    · exact prime_27892051421815855583579
  · reduce_mod_char
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals reduce_mod_char; decide +kernel

theorem prime_178259130663561045147472537592047227885001 : Nat.Prime 178259130663561045147472537592047227885001 := by
  apply Primes.prime_from_factors 178259130663561045147472537592047227885001 14 [2, 2, 2, 3, 3, 5, 5, 5, 5, 6323, 336157, 1863691091902891838383581623] (by decide +kernel)
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Primes.prime_2
    · exact Primes.prime_2
    · exact Primes.prime_2
    · exact Primes.prime_3
    · exact Primes.prime_3
    · exact Primes.prime_5
    · exact Primes.prime_5
    · exact Primes.prime_5
    · exact Primes.prime_5
    · exact prime_6323
    · exact prime_336157
    · exact prime_1863691091902891838383581623
  · reduce_mod_char
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide +kernel

theorem prime_2736030358979909402780800718157159386076813972158567259200215660948447373041 : Nat.Prime 2736030358979909402780800718157159386076813972158567259200215660948447373041 := by
  apply Primes.prime_from_factors 2736030358979909402780800718157159386076813972158567259200215660948447373041 31 [2, 2, 2, 2, 3, 5, 11, 11, 17, 967, 32151195060611136810608359, 178259130663561045147472537592047227885001] (by decide +kernel)
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Primes.prime_2
    · exact Primes.prime_2
    · exact Primes.prime_2
    · exact Primes.prime_2
    · exact Primes.prime_3
    · exact Primes.prime_5
    · exact Primes.prime_11
    · exact Primes.prime_11
    · exact Primes.prime_17
    · exact prime_967
    · exact prime_32151195060611136810608359
    · exact prime_178259130663561045147472537592047227885001
  · reduce_mod_char
  · intro factor member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals reduce_mod_char; decide +kernel

theorem native_subgroup_order_prime : Nat.Prime subgroupOrder := prime_2736030358979909402780800718157159386076813972158567259200215660948447373041

end LeanCrypto.Proofs.BabyJubjubPrimes

#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_967
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_4139
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_349
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_43189
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_295049
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_25485742523
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_202795150404015601
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_431548080059745198929
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_32151195060611136810608359
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_6323
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_336157
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_33409
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_23
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_521
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_27743
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_513749
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_1061
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_10206821
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_81654569
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_27892051421815855583579
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_1863691091902891838383581623
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_178259130663561045147472537592047227885001
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.prime_2736030358979909402780800718157159386076813972158567259200215660948447373041
#print axioms LeanCrypto.Proofs.BabyJubjubPrimes.native_subgroup_order_prime
