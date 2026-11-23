import Goldbach.ExtendedOdd.Window
import Goldbach.OddCertificate

namespace Goldbach.ExtendedOdd

/-- A half-open interval of verified windows. -/
def Covered (lo hi : ℕ) : Prop := ∀ j, lo ≤ j → j < hi → checked j = true

theorem Covered.append {a b c : ℕ} (hab : Covered a b) (hbc : Covered b c) :
    Covered a c := by
  intro j h₁ h₂
  by_cases h : j<b
  · exact hab j h₁ h
  · exact hbc j (by omega) h₂

/-- Reuse the same presieved table while checking four adjacent windows. -/
noncomputable def four (g : ℕ) :=
  (List.range 4).all fun r => checked (4*g+r)

theorem covered_of_four {a b : ℕ} (h : ∀ i < b, four (a+i) = true) :
    Covered (4*a) (4*(a+b)) := by
  intro j hlo hhi
  let i := j/4-a
  have hi : i < b := by dsimp [i]; omega
  have hb := List.all_eq_true.mp (h i hi) (j%4) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  simpa only [show 4*(a+i)+j%4=j by dsimp [i]; omega] using hb

theorem partition_of_covered {j n : ℕ} (hc : Covered 0 j) (hn : 4≤n)
    (hN : n ≤ 1073741824+1048576*j) (h32 : n≤4294967296) (he : Even n) (hne : n≠1847133842) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≤1789 ∧ p+q=n := by
  by_cases h : n ≤ 1073741824
  · obtain ⟨p,q,hp,hq,hb,hs⟩ := goldbach_through_1073741824 hn h he
    exact ⟨p,q,hp,hq,hb,hs⟩
  let k := (n/2-536870913)/524288
  have hev := Nat.even_iff.mp he
  have hk : k<j := by dsimp [k]; omega
  apply checked_sound (j:=k) (hc k (by omega) hk) _ _ h32 he hne
  · change 536870913+524288*k≤n/2
    dsimp [k]; omega
  · change n/2<536870913+524288*k+524288
    dsimp [k]; omega

end Goldbach.ExtendedOdd
