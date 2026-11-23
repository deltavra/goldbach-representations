import Goldbach.BoundedPrimality
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring

open Finset

namespace Goldbach.HomometricPrimeSets

/-- Reflecting one factor of a sum preserves all ordered difference statistics.
The sums count each representation separately. For direct sums this counts set points. -/
theorem reflect_factor_preserves_differences {G : Type*} [AddCommMonoid G]
    (u v : Finset ℤ) (c d : ℤ) (f : ℤ → G) :
    (∑ a ∈ u, ∑ b ∈ u, ∑ i ∈ v, ∑ j ∈ v,
      f ((a + d * i) - (b + d * j))) =
    (∑ a ∈ u, ∑ b ∈ u, ∑ i ∈ v, ∑ j ∈ v,
      f ((a + d * (c - i)) - (b + d * (c - j)))) := by
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  congr 1
  ring

private def anchors : List Nat := [1075141, 1271183, 1288607]

private def points (offsets : List Nat) : List Nat :=
  anchors.flatMap fun a => offsets.map fun t => a + 210 * t

def sampleA : List Nat := points [0, 1, 5, 6, 8]
def sampleB : List Nat := points [0, 2, 3, 7, 8]

private def lowerEnds (s : List Nat) : List Nat :=
  s.filter fun p => 2 * p ≤ 2363958 ∧ 2363958 - p ∈ s

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sample_primes : ∀ p ∈ sampleA ++ sampleB,
    Nat.Prime p ∧ 2363958 ≤ 3 * p ∧ 3 * p ≤ 2 * 2363958 := by
  simp_rw [← Goldbach.CentralCoprime.quickPrime_iff]
  decide +kernel

theorem sample_reflection : lowerEnds sampleA = [1075141, 1075351] ∧
    lowerEnds sampleB = [] := by
  decide +kernel

end Goldbach.HomometricPrimeSets
