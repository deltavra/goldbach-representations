import Goldbach.PowerResidues
import Mathlib.Data.List.Prime
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

namespace Goldbach

/-! A Lucas–Pratt certificate for a pair of primes at distance 327075
from the midpoint of `[0, 2^128]`. Each list factors one less than the prime it certifies. -/

private theorem primeOfLucasFactors (n g : ℕ) (factors : List ℕ)
    (hprod : factors.prod = n - 1) (hprimes : ∀ p ∈ factors, p.Prime)
    (hpow : (g : ZMod n) ^ (n - 1) = 1)
    (horders : ∀ p ∈ factors, (g : ZMod n) ^ ((n - 1) / p) ≠ 1) : n.Prime := by
  apply lucas_primality n (g : ZMod n) hpow
  intro p hp hd
  apply horders
  exact mem_list_primes_of_dvd_prod hp.prime (fun r hr => (hprimes r hr).prime) (hprod ▸ hd)

-- The repeated-squaring calculation in `reduce_mod_char` produces a kernel
-- proof of every modular exponentiation. Previously proved nodes discharge
-- the large prime factors. The small leaves use trial division.
scoped macro "lucas_certificate " g:num " with " factors:term : tactic =>
  `(tactic|
    (apply primeOfLucasFactors _ $g $factors rfl
     · simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
       repeat' apply And.intro
       all_goals first | assumption | norm_num
     · reduce_mod_char <;> decide
     · simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
       repeat' apply And.intro
       all_goals reduce_mod_char <;> decide))

private theorem prime222741979 : Nat.Prime 222741979 := by
  lucas_certificate 2 with [2, 3, 19, 43, 45439]

private theorem prime742608173 : Nat.Prime 742608173 := by
  lucas_certificate 2 with [2, 2, 30271, 6133]

private theorem prime1485216347 : Nat.Prime 1485216347 := by
  have := prime742608173
  lucas_certificate 2 with [2, 742608173]

private theorem prime19458471412664793119309 : Nat.Prime 19458471412664793119309 := by
  have := prime1485216347
  lucas_certificate 2 with [2, 2, 467, 33589, 208807, 1485216347]

private theorem primeBelowMidpoint : Nat.Prime 170141183460469231731687303715883778653 := by
  have := prime222741979
  have := prime19458471412664793119309
  lucas_certificate 2 with [2, 2, 71, 277, 499, 222741979, 19458471412664793119309]

private theorem prime840726697 : Nat.Prime 840726697 := by
  lucas_certificate 5 with [2, 2, 2, 3, 31, 571, 1979]

private theorem prime80461514321 : Nat.Prime 80461514321 := by
  lucas_certificate 3 with [2, 2, 2, 2, 5, 11, 31, 59, 49991]

private theorem prime9025847891857069968439 : Nat.Prime 9025847891857069968439 := by
  have := prime80461514321
  lucas_certificate 3 with [2, 3, 3, 3, 3, 4993, 138683, 80461514321]

private theorem prime85070591730234615865843651857942216401 : Nat.Prime 85070591730234615865843651857942216401 := by
  have := prime840726697
  have := prime9025847891857069968439
  lucas_certificate 3 with [2, 2, 2, 2, 5, 5, 28027, 840726697, 9025847891857069968439]

private theorem primeAboveMidpoint : Nat.Prime 170141183460469231731687303715884432803 := by
  have := prime85070591730234615865843651857942216401
  lucas_certificate 2 with [2, 85070591730234615865843651857942216401]

/-- Both primes pass the square-and-cube residue filter, lie in the closed
middle third, and sum to the prescribed target. -/
theorem twoPow128_middle_prime_pair :
    let p : ℕ := 2 ^ 127 - 327075
    let q : ℕ := 2 ^ 127 + 327075
    p.Prime ∧ q.Prime ∧ p + q = 2 ^ 128 ∧
      2 ^ 128 ≤ 3 * p ∧ 3 * q ≤ 2 * 2 ^ 128 ∧ powerResidue p ∧ powerResidue q := by
  exact ⟨primeBelowMidpoint, primeAboveMidpoint, by decide, by decide, by decide,
    by decide, by decide⟩

end Goldbach
