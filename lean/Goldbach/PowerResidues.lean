import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Tactic.IntervalCases

namespace Goldbach

/-- Twelve unit classes modulo 56 that contain no integer square or cube. -/
def powerResidue (n : ℕ) : Prop :=
  (n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7) ∧ 2 ≤ n % 7 ∧ n % 7 ≤ 5

instance (n : ℕ) : Decidable (powerResidue n) := by unfold powerResidue; infer_instance

def powerResiduePairCount (N : ℕ) : ℕ :=
  ((Finset.range 56).filter fun a =>
    powerResidue a ∧ powerResidue ((N % 56 + 56 - a) % 56)).card

/-- At least two ordered pairs of the twelve classes serve every even target. -/
theorem two_le_powerResiduePairCount (N : ℕ) (he : Even N) : 2 ≤ powerResiduePairCount N := by
  have table : ∀ t : Fin 28, 2 ≤ powerResiduePairCount (2 * t.val) := by decide +kernel
  obtain ⟨j, rfl⟩ := he
  have h := table ⟨j % 28, Nat.mod_lt _ (by decide)⟩
  dsimp only at h
  unfold powerResiduePairCount at h ⊢
  rwa [show (j + j) % 56 = (2 * (j % 28)) % 56 by omega]

/-- Every even residue modulo 56 has a decomposition into two allowed classes. -/
theorem exists_paired_power_residues (N : ℕ) (he : Even N) :
    ∃ a b : Fin 56, powerResidue a.val ∧ powerResidue b.val ∧
      (a.val + b.val) % 56 = N % 56 := by
  have h := two_le_powerResiduePairCount N he
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) h)
  obtain ⟨hr, hleft, hright⟩ := Finset.mem_filter.mp ha
  have hlt := Finset.mem_range.mp hr
  refine ⟨⟨a, hlt⟩, ⟨_, Nat.mod_lt _ (by decide)⟩, hleft, hright, ?_⟩
  dsimp
  omega

private theorem not_powerResidue_sq (p : ℕ) : ¬powerResidue (p ^ 2) := by
  have sq : ∀ a : Fin 8, (a.val ^ 2) % 8 = 0 ∨ (a.val ^ 2) % 8 = 1 ∨
      (a.val ^ 2) % 8 = 4 := by decide
  have h := sq ⟨p % 8, Nat.mod_lt _ (by decide)⟩
  dsimp at h
  rw [← Nat.pow_mod] at h
  rintro ⟨hp, _⟩
  omega

private theorem not_powerResidue_cube (p : ℕ) : ¬powerResidue (p ^ 3) := by
  have cube : ∀ a : Fin 7, (a.val ^ 3) % 7 = 0 ∨ (a.val ^ 3) % 7 = 1 ∨
      (a.val ^ 3) % 7 = 6 := by decide
  have h := cube ⟨p % 7, Nat.mod_lt _ (by decide)⟩
  dsimp at h
  rw [← Nat.pow_mod] at h
  rintro ⟨_, hlow, hhigh⟩
  omega

/-- Every higher power in one of the twelve classes has exponent at least five. -/
theorem five_le_exponent_of_powerResidue {p j : ℕ} (hj : 2 ≤ j)
    (h : powerResidue (p ^ j)) : 5 ≤ j := by
  by_contra! hlt
  interval_cases j
  · exact not_powerResidue_sq p h
  · exact not_powerResidue_cube p h
  · exact not_powerResidue_sq (p ^ 2) (by simpa only [← pow_mul] using h)

end Goldbach
