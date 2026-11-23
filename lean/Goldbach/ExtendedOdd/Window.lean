import Goldbach.ExtendedOdd.MaskTable

namespace Goldbach.ExtendedOdd

open PrimeBits

private abbrev width : ℕ := 524288
private abbrev halo : ℕ := 931
private abbrev span : ℕ := width + halo

/-- Half of the first even target in the block; block zero starts after 2³⁰. -/
def start (j : ℕ) := 536870913 + width*j

private def base (j : ℕ) := start j - halo
private def offset (j d : ℕ) := (base j + (d+1)/2) % d

private def shifted (j : ℕ) (e : ℕ × ℕ) :=
  if e.1^2 ≤ 2*(start j+width)+1 then e.2 >>> offset j e.1 else 0

private noncomputable def strikes (j : ℕ) : ℕ :=
  maskUnion (MaskTable.rows.toList.flatten.map (shifted j)) id

private def clear (strike : ℕ) := ((1 <<< (span+1))-1) ^^^ strike
private def smallOdds := (smallPrimes 1789).filter (fun p => p%2=1)
private def full : ℕ := (1 <<< width)-1

-- The exceptional target has half-index start 737 + 295752.
private def exception (j : ℕ) := if j=737 then 1 <<< 295752 else 0

/-- Every even target other than 1847133842 has an unstruck odd complement. -/
noncomputable def checked (j : ℕ) : Bool :=
  let bits := clear (strikes j)
  (full &&& (maskUnion smallOdds (fun p => bits >>> (halo-(p+1)/2)) ||| exception j)) == full

private theorem unstruck_prime {j k : ℕ} (hk : k ≤ span)
    (hlo : 2 ≤ 2*(base j+k)+1) (hhi : 2*(base j+k)+1 ≤ 4294967296)
    (hit : (clear (strikes j)).testBit k = true) : (2*(base j+k)+1).Prime := by
  let n := 2*(base j+k)+1
  change n.Prime
  by_contra hn
  let d := n.minFac
  have hpos : 0 < n := by dsimp [n]; omega
  have hd : d.Prime := Nat.minFac_prime (by dsimp [n]; omega)
  have hdvd : d ∣ n := Nat.minFac_dvd n
  have htwo : d ≠ 2 := by
    rintro h
    obtain ⟨t, ht⟩ := hdvd
    rw [h] at ht
    dsimp [n] at ht
    omega
  have hroot : d ≤ 65536 := by
    have hs := Nat.minFac_sq_le_self hpos hn
    change d^2 ≤ n at hs
    change n ≤ 4294967296 at hhi
    by_contra! h
    have := Nat.pow_le_pow_left (by omega : 65537 ≤ d) 2
    omega
  have hhalf : 2*((d+1)/2) = d+1 := by obtain ⟨t, ht⟩ := hd.odd_of_ne_two htwo; omega
  have hdouble : d ∣ 2*(base j+(d+1)/2+k) := by
    rw [show 2*(base j+(d+1)/2+k) = n+d by dsimp [n]; omega]
    exact Nat.dvd_add hdvd (dvd_refl d)
  have hdiv : d ∣ base j+(d+1)/2+k :=
    (hd.dvd_mul.mp hdouble).resolve_left
      (fun h => htwo ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hd.ne_one))
  have hoff : d ∣ offset j d+k := by
    apply Nat.dvd_of_mod_eq_zero
    rw [offset, Nat.mod_add_mod]
    exact Nat.mod_eq_zero_of_dvd hdiv
  obtain ⟨t, ht⟩ := hoff
  have hlim : d*t ≤ span+65536 := by
    have := Nat.mod_lt (base j+(d+1)/2) hd.pos
    change (base j+(d+1)/2)%d+k = d*t at ht
    omega
  have hcount : t < 2^20 := by
    have h := Nat.mul_le_mul_right t hd.one_le
    simp only [one_mul] at h
    dsimp [span, width, halo] at hlim
    omega
  have hs := stride_bit (span+65536) d 20 t hcount hlim
  have hsq : d^2 ≤ 2*(start j+width)+1 := by
    have hs : d^2 ≤ n := Nat.minFac_sq_le_self hpos hn
    have hstart : halo ≤ start j := by dsimp [start, halo]; omega
    dsimp [n, base, span] at *
    omega
  have hstrike : (strikes j).testBit k = true := by
    apply (maskUnion_bit _ _ _).mpr
    refine ⟨_, List.mem_map.mpr ⟨_, MaskTable.mem_rows hd htwo hroot, rfl⟩, ?_⟩
    change (shifted j (d, stride MaskTable.cap d 20)).testBit k = true
    simp only [shifted, if_pos hsq, Nat.testBit_shiftRight]
    simpa only [←ht, Nat.add_comm] using hs
  have hwin : ((1 <<< (span+1) : ℕ)-1).testBit k = true := by
    simp [Nat.one_shiftLeft, show k < span+1 by omega]
  rw [clear, Nat.testBit_xor, hwin, hstrike] at hit
  contradiction

theorem checked_sound {j n : ℕ} (hc : checked j = true)
    (hl : start j ≤ n/2) (hu : n/2 < start j+width)
    (hN : n ≤ 4294967296) (he : Even n) (hne : n≠1847133842) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ 1789 ∧ p+q=n := by
  let k := n/2 - start j
  have hk : k < width := by dsimp [k]; omega
  have hf : full.testBit k = true := by simp [full, Nat.one_shiftLeft, hk]
  have hev : n%2=0 := Nat.even_iff.mp he
  have hexc : (exception j).testBit k = false := by
    by_cases hj : j=737
    · have hdiff : k≠295752 := by dsimp [k, start, width]; omega
      have single {a b : ℕ} (h : a≠b) : ((1 <<< a) : ℕ).testBit b = false := by
        rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
        exact decide_eq_false h
      simpa only [exception, if_pos hj] using single (Ne.symm hdiff)
    · simp [exception, hj]
  have hb := congrArg (fun a : ℕ => a.testBit k) (beq_iff_eq.mp hc)
  simp only [Nat.testBit_and, hf, Bool.true_and, Nat.testBit_or, hexc, Bool.or_false] at hb
  obtain ⟨p, hp, hbit⟩ := (maskUnion_bit _ _ k).mp hb
  obtain ⟨hm, ho⟩ := List.mem_filter.mp hp
  obtain ⟨hcap, hp⟩ := mem_smallPrimes.mp hm
  have hodd : p%2=1 := by simpa using ho
  rw [Nat.testBit_shiftRight] at hbit
  have hstart : halo ≤ start j := by dsimp [start, halo]; omega
  have hsum : 2*(base j+(k+(halo-(p+1)/2)))+1+p=n := by
    dsimp [k, base]
    dsimp [halo] at *
    omega
  have hlow : 2 ≤ 2*(base j+(k+(halo-(p+1)/2)))+1 := by
    dsimp [base, start, halo]
    omega
  have hhigh : 2*(base j+(k+(halo-(p+1)/2)))+1 ≤ 4294967296 := by omega
  have hq := unstruck_prime (j := j) (k := k+(halo-(p+1)/2))
    (by dsimp [span]; omega) hlow hhigh (by simpa [Nat.add_comm] using hbit)
  exact ⟨p, _, hp, hq, hcap, (Nat.add_comm _ _).trans hsum⟩

end Goldbach.ExtendedOdd
