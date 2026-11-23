import Goldbach.ExtendedOdd.Blocks06
import Goldbach.ExtendedOdd.Blocks07
import Goldbach.ExtendedOdd.Sharp

namespace Goldbach

theorem ExtendedOdd.covered1024 : ExtendedOdd.Covered 0 1024 :=
  ExtendedOdd.blocks00.append <| ExtendedOdd.blocks01.append <|
  ExtendedOdd.blocks02.append <| ExtendedOdd.blocks03.append <|
  ExtendedOdd.blocks04.append <| ExtendedOdd.blocks05.append <|
  ExtendedOdd.blocks06.append ExtendedOdd.blocks07

/-- The previous sharp bound, 1789, lasts until just before 1847133842. -/
theorem goldbach_before_1847133842 {n : ℕ} (hn : 4≤n) (hN : n<1847133842) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≤1789 ∧ p+q=n := by
  exact ExtendedOdd.partition_of_covered ExtendedOdd.covered1024 hn (by omega) (by omega)
    he (by omega)

theorem ExtendedOdd.partition1861_of_covered {j n : ℕ} (hc : ExtendedOdd.Covered 0 j)
    (hn : 4≤n) (hN : n≤1073741824+1048576*j) (h32 : n≤4294967296) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≤1861 ∧ p+q=n := by
  by_cases h : n=1847133842
  · subst n
    exact ⟨1861, 1847131981, leastSummand_1847133842.2.1,
      leastSummand_1847133842.2.2.1, le_rfl, rfl⟩
  · obtain ⟨p,q,hp,hq,hb,hs⟩ := ExtendedOdd.partition_of_covered hc hn hN h32 he h
    exact ⟨p,q,hp,hq,by omega,hs⟩

/-- 1861 is a uniform small prime summand bound for all even numbers through 2³¹. -/
theorem goldbach_through_2147483648 {n : ℕ} (hn : 4≤n) (hN : n≤2147483648) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≤1861 ∧ p+q=n := by
  exact ExtendedOdd.partition1861_of_covered ExtendedOdd.covered1024 hn hN (by omega) he

end Goldbach
