import Goldbach.LeastSummand
import Goldbach.FinitePairs
import Mathlib.Data.List.Enum

namespace Goldbach

/-- One proper divisor for each reflected prime below the proposed least summand. -/
def divisorCover (n cap : ℕ) (ds : Array ℕ) : Bool :=
  ((PrimeBits.smallPrimes cap).zipIdx).all fun pi =>
    let d := ds[pi.2]!
    decide (2≤d ∧ d ∣ n-pi.1 ∧ d<n-pi.1)

theorem least_summand_of_divisorCover {n u : ℕ} {ds : Array ℕ}
    (he : Even n) (hp : u.Prime) (hq : (n-u).Prime) (horder : u≤n-u)
    (h : divisorCover n (u-1) ds=true) : IsLeastPrimeSummand n u := by
  refine ⟨he,hp,hq,horder,?_⟩
  intro p hpu hprime
  apply no_small_prime_summand_of_cover (F:=u-1) _ p (by omega) hprime
  intro r hr hpr
  let ps := PrimeBits.smallPrimes (u-1)
  have hmem : r ∈ ps := PrimeBits.mem_smallPrimes.mpr ⟨hr,hpr⟩
  obtain ⟨i,hi,hei⟩ := List.mem_iff_getElem.mp hmem
  have ha := List.forall_mem_zipIdx'.mp (List.all_eq_true.mp h) i hi
  have val : 2≤ds[i]! ∧ ds[i]! ∣ n-ps[i] ∧ ds[i]!<n-ps[i] := of_decide_eq_true ha
  exact ⟨_,by simpa only [hei] using val⟩

end Goldbach
