import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace Goldbach

/-- The smaller summand in a minimal Goldbach partition of an even integer. -/
def IsLeastPrimeSummand (N u : ℕ) : Prop :=
  Even N ∧ u.Prime ∧ (N - u).Prime ∧ u ≤ N - u ∧
    ∀ p < u, p.Prime → ¬ (N - p).Prime

/-- A proper divisor for each reflected candidate excludes all smaller primes. -/
theorem no_small_prime_summand_of_cover {N F : ℕ}
    (cover : ∀ p ≤ F, p.Prime → ∃ d, 2 ≤ d ∧ d ∣ N - p ∧ d < N - p) :
    ∀ p ≤ F, p.Prime → ¬ (N - p).Prime := by
  intro p hp hprime hother
  obtain ⟨d, hd, hdiv, hlt⟩ := cover p hp hprime
  have := hother.eq_one_or_self_of_dvd d hdiv
  omega

/-- Choose a prime translate whose sum with a given prime contains every smaller factor. -/
theorem exists_prime_gt_with_smaller_factors {u : ℕ} (hu : u.Prime) (B : ℕ) :
    ∃ q > B, q.Prime ∧ ∀ d, 0 < d → d < u → d ∣ u + q := by
  let m := (u - 1).factorial
  have : NeZero m := ⟨Nat.factorial_ne_zero _⟩
  have hunit : IsUnit (u : ZMod m) :=
    (ZMod.isUnit_iff_coprime u m).mpr (hu.coprime_factorial_of_lt (by have := hu.pos; omega))
  obtain ⟨q, hq, hprime, heq⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod hunit.neg B
  have hmult : m ∣ u + q := (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast; rw [heq]; simp)
  exact ⟨q, hq, hprime, fun d hd hlt => (Nat.dvd_factorial hd (by omega : d ≤ u - 1)).trans hmult⟩

/-- Every odd prime is the exact minimum for arbitrarily large even targets. -/
theorem exists_gt_with_least_prime_summand {u : ℕ} (hu : u.Prime) (hodd : 2 < u) (B : ℕ) :
    ∃ q > max B u, q.Prime ∧ IsLeastPrimeSummand (u + q) u := by
  obtain ⟨q, hq, hprime, hfactor⟩ := exists_prime_gt_with_smaller_factors hu (max B u)
  refine ⟨q, hq, hprime, ?_⟩
  refine ⟨even_iff_two_dvd.mpr (hfactor 2 (by decide) hodd), hu, by simpa using hprime, by omega, ?_⟩
  intro p hp hpp
  apply no_small_prime_summand_of_cover (N := u + q) (F := u - 1) ?_ p (by omega) hpp
  intro t ht htprime
  exact ⟨t, htprime.two_le, Nat.dvd_sub (hfactor t htprime.pos (by omega)) (dvd_refl t), by omega⟩

end Goldbach
