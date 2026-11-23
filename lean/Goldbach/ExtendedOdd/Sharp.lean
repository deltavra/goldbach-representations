import Goldbach.DyadicWitness
import Goldbach.LeastSummandCertificate

namespace Goldbach

open scoped Goldbach

private theorem prime1847131981 : Nat.Prime 1847131981 := by
  have : Nat.Prime 145903 := by lucas_certificate 5 with [2, 3, 24317]
  lucas_certificate 6 with [2, 2, 3, 5, 211, 145903]

/-- A proper factor of 1847133842 − p for each prime p below 1861, in order. -/
private def factorsAt1847133842 : Array ℕ := #[
    2, 79, 3, 5, 3, 233, 3, 293, 3, 3, 19, 5, 3, 7, 3, 3, 3, 277, 5, 3,
    13, 41, 3, 3, 5, 3, 11, 3, 337, 3, 5, 3, 3, 23, 3, 13, 5, 89, 3, 3,
    3, 197, 3, 7817, 3, 1063, 7, 61, 3, 13, 3, 3, 6827, 3, 3, 3, 3, 409, 5, 3,
    16603, 3, 5, 3, 34297, 3, 29, 5, 3, 21067, 3, 3, 5, 19, 7, 3, 3, 5, 3, 661,
    3, 7, 3, 11, 107, 3, 3, 5, 3, 7, 3, 3, 5, 3, 11, 3, 3, 3, 1597, 13,
    5, 3, 3, 3, 41, 5, 3, 3, 3, 19, 5, 47, 3, 13, 7, 3, 503, 3, 3, 3,
    17, 7, 3, 3, 23, 3, 1289, 3, 5, 31, 157, 3, 2971, 5, 3, 97, 3, 5, 3, 3,
    7013, 3, 151, 3, 11, 3, 13, 3, 43, 3, 5, 3, 7, 3, 5, 3, 31, 3, 5, 3,
    3, 3, 5, 3, 3, 3, 4691, 5, 7, 3, 3, 431, 3, 977, 11411, 3, 7, 3, 41, 17,
    5, 3, 7, 3, 3, 3, 5, 15149, 83, 3, 317, 3, 17, 3, 3, 3, 29, 12539, 3, 3,
    3, 37, 5, 647, 3, 3, 311, 3, 3, 11, 5, 3, 7, 3, 3, 13, 5, 3, 3, 3,
    23, 13, 3, 11, 3, 7, 3, 3, 5, 3, 37, 47, 7, 3, 73, 3, 11, 3, 3, 3,
    3, 4003, 28403, 29, 3, 3, 5, 3, 17, 3, 5, 3, 3, 757, 3, 3, 11, 5, 3, 5,
    31, 3, 3547, 3823, 3, 10303, 3, 3, 7, 3, 19, 5, 11, 18523, 5, 17, 3, 13, 41, 3,
    3, 9209, 3]

/-- 1847133842 = 1861 + 1847131981, with the smallest possible prime summand. -/
theorem leastSummand_1847133842 : IsLeastPrimeSummand 1847133842 1861 := by
  apply least_summand_of_divisorCover (ds := factorsAt1847133842)
    (by decide) (by norm_num) (by exact prime1847131981) (by decide)
  decide +kernel

theorem summand_ge_1861_at_1847133842 {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hs : p+q=1847133842) : 1861≤p := by
  by_contra! h
  exact leastSummand_1847133842.2.2.2.2 p h hp (by rwa [show 1847133842-p=q by omega])

end Goldbach
