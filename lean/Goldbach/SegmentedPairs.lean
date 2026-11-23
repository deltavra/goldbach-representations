import Goldbach.FinitePairs

namespace Goldbach.SegmentedPairs

open PrimeBits

private abbrev width : ℕ := 262144
private abbrev halo : ℕ := 1094
private abbrev root : ℕ := 8192
private abbrev span : ℕ := width + halo
def start (j : ℕ) : ℕ := 1048576 + width*j

local macro "block_arith" : tactic =>
  `(tactic| (simp only [start, span, width, halo, root] at * <;> omega))

/-- The origin of each periodic strike is translated by the block's residue. -/
private def primeWindow (base : ℕ) : ℕ :=
  ((1 <<< (span+1)) - 1) ^^^
    maskUnion (smallPrimes root) (fun d => stride (span+root) d 19 >>> (base % d))

private theorem primeWindow_sound {base i : ℕ} (hi : i ≤ span) (hl : 2 ≤ base+i)
    (hu : base+i ≤ 67108864) (hit : (primeWindow base).testBit i = true) :
    (base+i).Prime := by
  by_contra hcomp
  let d := (base+i).minFac
  have hp : d.Prime := Nat.minFac_prime (by omega)
  have hroot : d ≤ root := by
    have hs : d^2 ≤ base+i := Nat.minFac_sq_le_self (by omega) hcomp
    by_contra! hbad
    have hq := Nat.pow_le_pow_left (show 8193 ≤ d by block_arith) 2
    block_arith
  have hd : d ∣ base % d+i := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.mod_add_mod]
    exact Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd _)
  obtain ⟨k, hk⟩ := hd
  have hz := Nat.mod_lt base hp.pos
  have hlim : d*k ≤ span+root := by omega
  have hk' : k ≤ d*k := by simpa using Nat.mul_le_mul_right k hp.one_le
  have hbit := stride_bit (span+root) d 19 k (by block_arith) hlim
  have struck : ((stride (span+root) d 19) >>> (base % d)).testBit i = true := by
    simpa [Nat.testBit_shiftRight, ← hk, Nat.add_comm] using hbit
  have hm := (maskUnion_bit (smallPrimes root)
    (fun d => stride (span+root) d 19 >>> (base % d)) i).mpr
    ⟨d, mem_smallPrimes.mpr ⟨hroot, hp⟩, struck⟩
  have hf : ((1 <<< (span+1) : ℕ) - 1).testBit i = true := by
    simp [Nat.one_shiftLeft, show i < span+1 by omega]
  simp [primeWindow, Nat.testBit_xor, hf, hm] at hit

private def evenOffsets : ℕ := stride width 2 17 <<< 2

def covered (j : ℕ) : Bool :=
  let bits := primeWindow (start j - halo)
  (evenOffsets &&& maskUnion (smallPrimes 1093) (fun p => bits >>> (halo-p))) == evenOffsets

theorem covered_sound {j n : ℕ} (hc : covered j = true) (hl : start j < n)
    (hu : n ≤ start j + width) (hN : n ≤ 67108864) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ 1093 ∧ p+q=n := by
  obtain ⟨v, hv⟩ := he
  let k := n-start j
  have heq : k = 2*(v-(524288+131072*j)) := by dsimp [k]; block_arith
  have low : 2 ≤ k := by dsimp [k] at *; block_arith
  have high : k ≤ width := by dsimp [k]; omega
  have hsub : k-2 = 2*(v-(524288+131072*j)-1) := by omega
  have hb := stride_bit width 2 17 (v-(524288+131072*j)-1) (by block_arith) (by block_arith)
  have hev : evenOffsets.testBit k = true := by
    simpa [evenOffsets, Nat.testBit_shiftLeft, low, hsub] using hb
  have hequal := congrArg (fun m : ℕ => m.testBit k) (beq_iff_eq.mp hc)
  simp only [Nat.testBit_and, hev, Bool.true_and] at hequal
  obtain ⟨p, hp, hq⟩ := (maskUnion_bit _ _ k).mp hequal
  obtain ⟨hpmax,hprime⟩ := mem_smallPrimes.mp hp
  rw [Nat.testBit_shiftRight] at hq
  have hbase : halo ≤ start j := by block_arith
  have hpos : 2 ≤ start j-halo+(k+(halo-p)) := by block_arith
  have hsum : start j-halo+(k+(halo-p)) = n-p := by dsimp [k]; block_arith
  have hqprime := primeWindow_sound (by block_arith : k+(halo-p) ≤ span) hpos
    (by rw [hsum]; omega) (by simpa [Nat.add_comm] using hq)
  exact ⟨p,n-p,hprime,hsum ▸ hqprime,hpmax,by block_arith⟩

end Goldbach.SegmentedPairs
