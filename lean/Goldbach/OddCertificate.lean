import Goldbach.OddBlocksFirst
import Goldbach.OddBlocksMiddle
import Goldbach.OddBlocksLast
import Goldbach.SegmentedCertificate

namespace Goldbach

private theorem odd_blocks (j : ℕ) (hj : j<960) : OddWindow.checked j=true := by
  by_cases h₁ : j<320
  · exact OddBlocks.first j h₁
  by_cases h₂ : j<640
  · simpa only [show 320+(j-320)=j by omega] using OddBlocks.middle (j-320) (by omega)
  simpa only [show 640+(j-640)=j by omega] using OddBlocks.last (j-640) (by omega)

/-- All even integers through 2³⁰ have a prime summand at most 1789. -/
theorem goldbach_through_1073741824 {n : ℕ} (hn : 4≤n) (hN : n≤1073741824)
    (he : Even n) : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≤1789 ∧ p+q=n := by
  by_cases h : n≤67108864
  · obtain ⟨p,q,hp,hq,hb,hs⟩ := goldbach_through_67108864 hn h he
    exact ⟨p,q,hp,hq,by omega,hs⟩
  let j := (n/2-33554433)/524288
  have hev := Nat.even_iff.mp he
  have hidx : j<960 := by dsimp [j]; omega
  apply OddWindow.checked_sound (j:=j) (odd_blocks _ hidx) _ _ hN he
  · change 33554433+524288*j≤n/2
    dsimp [j]; omega
  · change n/2<33554433+524288*j+524288
    dsimp [j]; omega

set_option maxHeartbeats 0 in
/-- The uniform bound is sharp at 721013438. -/
theorem summand_ge_1789_at_721013438 {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hs : p+q=721013438) : 1789≤p := by
  have h : (PrimeBits.smallPrimes 1788).all
    (fun a => (721013438-a).minFac != 721013438-a)=true := by decide +kernel
  by_contra! hl
  have hmem : p ∈ PrimeBits.smallPrimes 1788 := PrimeBits.mem_smallPrimes.mpr ⟨by omega,hp⟩
  have hm := List.all_eq_true.mp h p hmem
  simp [show 721013438-p=q by omega,hq.minFac_eq] at hm

end Goldbach
