import Goldbach.ExtendedOdd.Certificate31
import Goldbach.ExtendedOdd.Blocks22
import Goldbach.ExtendedOdd.Blocks23

namespace Goldbach

private theorem covered3072 : ExtendedOdd.Covered 0 3072 :=
  ExtendedOdd.covered1024.append <|
  ExtendedOdd.blocks08.append <| ExtendedOdd.blocks09.append <|
  ExtendedOdd.blocks10.append <| ExtendedOdd.blocks11.append <|
  ExtendedOdd.blocks12.append <| ExtendedOdd.blocks13.append <|
  ExtendedOdd.blocks14.append <| ExtendedOdd.blocks15.append <|
  ExtendedOdd.blocks16.append <| ExtendedOdd.blocks17.append <|
  ExtendedOdd.blocks18.append <| ExtendedOdd.blocks19.append <|
  ExtendedOdd.blocks20.append <| ExtendedOdd.blocks21.append <|
  ExtendedOdd.blocks22.append ExtendedOdd.blocks23

/-- The strong Goldbach assertion with an explicit prime summand bound through 2³². -/
theorem goldbach_through_4294967296 {n : ℕ} (hn : 4≤n) (hN : n≤4294967296) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≤1861 ∧ p+q=n := by
  exact ExtendedOdd.partition1861_of_covered covered3072 hn hN hN he

/-- Among all even targets through 2³², exactly one requires a summand above 1789. -/
theorem summand_le_1789_iff_ne_1847133842 {n : ℕ} (hn : 4≤n) (hN : n≤4294967296)
    (he : Even n) : (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≤1789 ∧ p+q=n) ↔ n≠1847133842 := by
  constructor
  · rintro ⟨p,q,hp,hq,hb,hs⟩ rfl
    have := summand_ge_1861_at_1847133842 hp hq hs
    omega
  · exact ExtendedOdd.partition_of_covered covered3072 hn hN hN he

/-- The sharp uniform bound jumps from 1789 to 1861 at 1847133842. -/
theorem uniform_summand_bound_iff {N u : ℕ} (hlo : 721013438≤N) (hhi : N≤4294967296) :
    (∀ n, 4≤n → n≤N → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≤u ∧ p+q=n) ↔
      (if N<1847133842 then 1789 else 1861)≤u := by
  constructor
  · intro h
    split
    · obtain ⟨p,q,hp,hq,hb,hs⟩ := h 721013438 (by decide) hlo (by decide)
      exact (summand_ge_1789_at_721013438 hp hq hs).trans hb
    · obtain ⟨p,q,hp,hq,hb,hs⟩ := h 1847133842 (by decide) (by omega) (by decide)
      exact (summand_ge_1861_at_1847133842 hp hq hs).trans hb
  · intro hu n hn hN he
    split at hu
    · obtain ⟨p,q,hp,hq,hb,hs⟩ :=
        (summand_le_1789_iff_ne_1847133842 hn (hN.trans hhi) he).mpr (by omega)
      exact ⟨p,q,hp,hq,hb.trans hu,hs⟩
    · obtain ⟨p,q,hp,hq,hb,hs⟩ := goldbach_through_4294967296 hn (hN.trans hhi) he
      exact ⟨p,q,hp,hq,hb.trans hu,hs⟩

end Goldbach
