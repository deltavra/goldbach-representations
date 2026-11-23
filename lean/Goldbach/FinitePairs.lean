import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Group.Nat.Even

namespace Goldbach

private def limit : ℕ := 1048576

namespace PrimeBits

/-- Double the number of equally spaced bits while the new shift is in range. -/
def stride (cap d : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 =>
    let m := stride cap d k
    let shift := d * 2 ^ k
    if shift ≤ cap then m ||| (m <<< shift) else m

theorem stride_bit (cap d k t : ℕ) (ht : t < 2 ^ k) (hn : d * t ≤ cap) :
    (stride cap d k).testBit (d * t) = true := by
  induction k generalizing t with
  | zero =>
    have : t = 0 := by simpa using ht
    simp [this, stride]
  | succ k ih =>
    by_cases h : t < 2 ^ k
    · have ok := ih t h hn
      by_cases hs : d * 2 ^ k ≤ cap <;> simp [stride, hs, ok]
    · have hs := Nat.mul_le_mul_left d (Nat.le_of_not_gt h)
      have ht' : t - 2 ^ k < 2 ^ k := by rw [pow_succ] at ht; omega
      have he := Nat.mul_sub_left_distrib d t (2 ^ k)
      have hd : d * (t - 2 ^ k) ≤ cap := by omega
      simp [stride, hs.trans hn, hs, ← he, ih _ ht' hd]

def maskUnion (l : List ℕ) (bits : ℕ → ℕ) : ℕ :=
  l.foldr (fun d rest => bits d ||| rest) 0

theorem maskUnion_bit (l : List ℕ) (bits : ℕ → ℕ) (n : ℕ) :
    (maskUnion l bits).testBit n = true ↔ ∃ d ∈ l, (bits d).testBit n = true := by
  induction l with
  | nil => simp [maskUnion]
  | cons d l ih => simpa [maskUnion, Nat.testBit_or] using
      (or_congr Iff.rfl ih : (_ ∨ _) ↔ (_ ∨ _))

def smallPrimes (u : ℕ) : List ℕ :=
  (List.range (u + 1)).filter fun d => decide (2 ≤ d) && (d.minFac == d)

theorem mem_smallPrimes {u d : ℕ} : d ∈ smallPrimes u ↔ d ≤ u ∧ d.Prime := by
  simp [smallPrimes, Nat.prime_def_minFac, Nat.lt_succ_iff]

end PrimeBits

open PrimeBits

private abbrev strideMask := stride limit
private abbrev strideMask_bit := stride_bit limit

private def strikes (d : ℕ) : ℕ := strideMask d 20 <<< (d * 2)
private def fullMask : ℕ := (1 <<< (limit + 1)) - 1
private def primeMask : ℕ :=
  (fullMask ^^^ maskUnion (smallPrimes 1024) strikes) &&& (fullMask <<< 2)

private theorem primeMask_sound {n : ℕ} (hn : n ≤ limit) (h : primeMask.testBit n = true) :
    n.Prime := by
  have hfull : fullMask.testBit n = true := by
    simp [fullMask, Nat.one_shiftLeft, show n < limit + 1 by omega]
  rw [primeMask, Nat.testBit_and, Bool.and_eq_true_iff, Nat.testBit_xor, hfull,
    Nat.testBit_shiftLeft, Bool.and_eq_true_iff] at h
  have h2 : 2 ≤ n := of_decide_eq_true h.2.1
  by_contra hnp
  let d := n.minFac
  have hp : d.Prime := Nat.minFac_prime (by omega)
  have hsmall : d ≤ 1024 := by
    have hs : d ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
    by_contra! hh
    have hh2 := Nat.pow_le_pow_left (show 1025 ≤ d by omega) 2
    dsimp [limit] at hn
    omega
  obtain ⟨k, he⟩ := Nat.minFac_dvd n
  change n = d * k at he
  have hk : k ≤ n := by
    have := Nat.mul_le_mul_right k hp.one_le
    simpa only [one_mul, ← he] using this
  have hk2 : 2 ≤ k := by
    by_contra! hlt
    rcases (show k = 0 ∨ k = 1 by omega) with e | e
    · simp [e] at he; omega
    · have eq : n = d := by simpa [e] using he
      exact hnp (eq.symm ▸ hp)
  have hstart : d * 2 ≤ n := he.symm ▸ Nat.mul_le_mul_left d hk2
  have hdiff : n - d * 2 = d * (k - 2) := by rw [he, Nat.mul_sub_left_distrib]
  have ht : k - 2 < 2 ^ 20 := by dsimp [limit] at hn; omega
  have hbit := strideMask_bit d 20 (k - 2) ht (by omega)
  have hd : (strikes d).testBit n = true := by simp [strikes, Nat.testBit_shiftLeft, hstart, hdiff, hbit]
  have hb := (maskUnion_bit _ strikes n).mpr ⟨d, mem_smallPrimes.mpr ⟨hsmall, hp⟩, hd⟩
  simp [hb] at h

private def evenTargets : ℕ := strideMask 2 19 <<< 4

set_option maxRecDepth 12000 in
private theorem bit_coverage :
    evenTargets &&& maskUnion (smallPrimes 523) (fun p => primeMask <<< p) = evenTargets := by
  decide +kernel

/-- Every even integer from four through 2²⁰ is a sum of two primes;
one summand can always be chosen at most 523. -/
theorem goldbach_through_1048576 {n : ℕ} (hn : 4 ≤ n) (hN : n ≤ 1048576) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ 523 ∧ p + q = n := by
  obtain ⟨j, hj⟩ := he
  have hj' : j - 2 < 2 ^ 19 := by omega
  have hpos : n - 4 = 2 * (j - 2) := by omega
  have ht : evenTargets.testBit n = true := by
    have hbit := strideMask_bit 2 19 (j - 2) hj' (by dsimp [limit]; omega)
    simp [evenTargets, Nat.testBit_shiftLeft, hn, hpos, hbit]
  have hcover := congrArg (fun z : ℕ => z.testBit n) bit_coverage
  simp only [Nat.testBit_and, ht, Bool.true_and] at hcover
  obtain ⟨p, hp, hbit⟩ := (maskUnion_bit _ _ n).mp hcover
  obtain ⟨hle, hp'⟩ := mem_smallPrimes.mp hp
  rw [Nat.testBit_shiftLeft, Bool.and_eq_true_iff] at hbit
  exact ⟨p, n - p, hp', primeMask_sound (by dsimp [limit]; omega) hbit.2, hle,
    Nat.add_sub_of_le (of_decide_eq_true hbit.1)⟩

/-- At 503222 every prime summand is at least 523, so the uniform bound is sharp. -/
theorem summand_ge_523_at_503222 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hs : p + q = 503222) :
    523 ≤ p := by
  have table : (smallPrimes 522).all (fun a => (503222 - a).minFac != 503222 - a) = true := by
    decide +kernel
  by_contra! hl
  have ht := List.all_eq_true.mp table p (mem_smallPrimes.mpr ⟨by omega, hp⟩)
  have he : 503222 - p = q := by omega
  simp [he, hq.minFac_eq] at ht

/-- No prime above 524288 + 1281 can appear in the near-center certificate. -/
private def centerPrimes : ℕ := primeMask % (1 <<< 525570)

private theorem centerPrimes_sound {p : ℕ} (h : centerPrimes.testBit p = true) : p.Prime := by
  simp only [centerPrimes, Nat.one_shiftLeft, Nat.testBit_mod_two_pow, Bool.and_eq_true_iff,
    decide_eq_true_eq] at h
  exact primeMask_sound (by dsimp [limit]; omega) h.2

/-- Keep the intersection of the opposite shifts at centers below 44 or at least 3d. -/
private def centerPairMask (d : ℕ) : ℕ :=
  let pairs := (centerPrimes <<< d) &&& (centerPrimes >>> d)
  (pairs % (1 <<< 44)) ||| ((pairs >>> (3 * d)) <<< (3 * d))

private theorem centerPairMask_sound {m d : ℕ} (h : (centerPairMask d).testBit m = true) :
    (m - d).Prime ∧ (m + d).Prime ∧ (44 ≤ m → 3 * d ≤ m) := by
  let pairs := (centerPrimes <<< d) &&& (centerPrimes >>> d)
  change ((pairs % (1 <<< 44)) ||| ((pairs >>> (3 * d)) <<< (3 * d))).testBit m = true at h
  simp only [Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  have hp : pairs.testBit m = true ∧ (44 ≤ m → 3 * d ≤ m) := by
    rcases h with ⟨hlt, hb⟩ | ⟨hle, hb⟩
    · exact ⟨hb, by omega⟩
    · exact ⟨by simpa only [Nat.add_sub_of_le hle] using hb, fun _ => hle⟩
  have hb := hp.1
  simp only [pairs, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Bool.and_eq_true_iff] at hb
  exact ⟨centerPrimes_sound hb.1.2, centerPrimes_sound (by simpa only [Nat.add_comm] using hb.2), hp.2⟩

private def centerTargets : ℕ := ((1 <<< 524285) - 1) <<< 4

set_option maxRecDepth 24000 in
private theorem center_coverage :
    centerTargets &&& (maskUnion (List.range 1280) (fun k => centerPairMask (k + 1)) |||
      (1 <<< 371428)) = centerTargets := by
  decide +kernel

/-- All centers through 2¹⁹ have a distinct symmetric prime pair. The pair can
be chosen in the middle third from center 44, and only center 371428 needs radius 1281. -/
theorem symmetric_prime_pair_through_524288 {m : ℕ} (hm : 4 ≤ m) (hM : m ≤ 524288) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ 1281 ∧ (m - d).Prime ∧ (m + d).Prime ∧
      (44 ≤ m → 3 * d ≤ m) ∧ (m ≠ 371428 → d ≤ 1280) := by
  by_cases hex : m = 371428
  · subst m
    exact ⟨1281, by decide, by decide, Nat.prime_def_minFac.mpr (by decide +kernel),
      Nat.prime_def_minFac.mpr (by decide +kernel), by decide, by simp⟩
  have ht : centerTargets.testBit m = true := by
    simp only [centerTargets, Nat.testBit_shiftLeft, decide_eq_true hm, Bool.true_and,
      Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, decide_eq_true (show m - 4 < 524285 by omega)]
  have hc := congrArg (fun z : ℕ => z.testBit m) center_coverage
  simp only [Nat.testBit_and, ht, Bool.true_and, Nat.testBit_or, Nat.one_shiftLeft,
    Nat.testBit_two_pow, decide_eq_false (Ne.symm hex), Bool.or_false] at hc
  obtain ⟨k, hk, hb⟩ := (maskUnion_bit _ _ m).mp hc
  have hl := List.mem_range.mp hk
  obtain ⟨hp, hq, hmid⟩ := centerPairMask_sound hb
  exact ⟨k + 1, by omega, by omega, hp, hq, hmid, by omega⟩

/-- The central representation has ordered, distinct primes and gap at most 2562. -/
theorem goldbach_middle_third_through_1048576 {n : ℕ} (hn : 88 ≤ n) (hN : n ≤ 1048576)
    (he : Even n) : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ p + q = n ∧
      n ≤ 3 * p ∧ 3 * q ≤ 2 * n ∧ q - p ≤ 2562 := by
  obtain ⟨m, hm⟩ := he
  obtain ⟨d, hd, hD, hp, hq, hs, _⟩ := symmetric_prime_pair_through_524288
    (m := m) (by omega) (by omega)
  have := hs (by omega)
  exact ⟨m - d, m + d, hp, hq, by omega, by omega, by omega, by omega, by omega⟩

theorem symmetric_prime_radius_ge_1281_at_371428 {d : ℕ}
    (hp : (371428 - d).Prime) (hq : (371428 + d).Prime) : 1281 ≤ d := by
  have tab : (List.range 1281).all (fun k => ((371428 - k).minFac != 371428 - k) ||
      ((371428 + k).minFac != 371428 + k)) = true := by decide +kernel
  by_contra! h
  have ht := List.all_eq_true.mp tab d (List.mem_range.mpr h)
  simp [hp.minFac_eq, hq.minFac_eq] at ht

/-- 43 + 43 is the only central prime pair at the preceding even target. -/
theorem middle_prime_pair_at_86 {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hs : p + q = 86) (h₁ : 86 ≤ 3 * p) (h₂ : 86 ≤ 3 * q) : p = 43 ∧ q = 43 := by
  have tab : ∀ a : Fin 87, (a : ℕ).Prime → (86 - (a : ℕ)).Prime →
      86 ≤ 3 * (a : ℕ) → 86 ≤ 3 * (86 - (a : ℕ)) → (a : ℕ) = 43 := by decide +kernel
  have he : 86 - p = q := by omega
  have ht : p = 43 := tab ⟨p, by omega⟩ hp (he ▸ hq) h₁ (he ▸ h₂)
  exact ⟨ht, by omega⟩

end Goldbach
