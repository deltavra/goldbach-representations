import Goldbach.SegmentedPairs
import Mathlib.Tactic.IntervalCases

namespace Goldbach

open SegmentedPairs

private def batch (k : ℕ) : Bool :=
  (List.range 7).all fun i => covered (7*k+i)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
set_option Elab.async false in
private theorem batches {k : ℕ} (hk : k < 36) : batch k = true := by
  interval_cases k <;> as_aux_lemma => decide +kernel

private theorem checked_block {j : ℕ} (hj : j < 252) : covered j = true := by
  have hb := batches (k := j/7) (by omega)
  have hv := List.all_eq_true.mp hb (j%7) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  simpa only [show 7*(j/7)+j%7 = j by omega] using hv

/-- Every even integer from 4 through 2²⁶ has a prime summand at most 1093. -/
theorem goldbach_through_67108864 {n : ℕ} (hn : 4 ≤ n) (hN : n ≤ 67108864)
    (he : Even n) : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ 1093 ∧ p+q=n := by
  by_cases h : n ≤ 1048576
  · obtain ⟨p,q,hp,hq,hs,heq⟩ := goldbach_through_1048576 hn h he
    exact ⟨p,q,hp,hq,by omega,heq⟩
  let j := (n-1048577)/262144
  have hj : j < 252 := by dsimp [j]; omega
  apply covered_sound (checked_block hj) _ _ hN he
  · change 1048576 + 262144*((n-1048577)/262144) < n
    omega
  · change n ≤ 1048576 + 262144*((n-1048577)/262144) + 262144
    omega

/-- The uniform bound 1093 is attained at this target. -/
theorem summand_ge_1093_at_60119912 {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (heq : p+q=60119912) : 1093 ≤ p := by
  have table : (PrimeBits.smallPrimes 1092).all
    (fun a => (60119912-a).minFac != 60119912-a) = true := by decide +kernel
  by_contra! hl
  have ht := List.all_eq_true.mp table p (PrimeBits.mem_smallPrimes.mpr ⟨by omega,hp⟩)
  have hs : 60119912-p=q := by omega
  simp [hs, hq.minFac_eq] at ht

end Goldbach
