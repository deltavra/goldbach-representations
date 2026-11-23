import Goldbach.FinitePairs
import Mathlib.Data.Nat.Prime.Factorial

namespace Goldbach.CentralCoprime

/-- Product of the primes through 4096. Only its checked divisibility
properties are used by the primality decision below. -/
private def wheel : ℕ := 0x4fe43c99ab1d4b82fb62181608cdf254da35e2509ca1ed2c61a2bc632b4ab01e7665bdc31494e92728925dd7211e8f94b33cf972e2da39b982cb3198b48b74f444d48c40a4286b87bea0b342dd5b00cfd3fe713196fe1a8ef91bfdb256567e83d0f5e4ef8f6f9ff93a21acff3cb617353bc083f1ab635e8507d26ee4308e43ea5d24dde0b1c0b54c1ae384925f2bc1b4283dd5a1d6818e43ed2055fb92d7615f7aeeeb20453336aede273f9dbc43147355bed9561b3167d47f61365a5992721e1c3cd5e6b1b79446b05bc870771d736d4107df5b51059b9a3bff8319130832b54f6820037de9ea7b9cf653b6d1c0d9a37e82d299f2b2116364710c914889f6c5c434731116567cef6d762085c1ce7e7f208db9f843b93d4478594a76af1793d223c27d0702cd452d627568648bad61b1ef7ec587d8ee97c3ad83eef04dd264c0ea1dad1adea22ae802a68734da7e4a1312de6e133630b46620919769a561060cc0caedfd396a9ade2550c1603d29840d68d64c2926fe0d7d245f1819f8ec09ed98e718eb0c68415bd6dbcceb2ae3a354611db9601f72512100a679c9baadc7e2ef50684dae00f67df611174a37f0e0d4ab9828a78c8e5d7a07fd94fd92813231964f0475240b9a774bf08d679d0ff0f27ba0923366a8e3d56f04134f2f87b6acb0e79f4806136de2f7443a0a3d2f3a4716ec861f62dcfc63f58a181987d26ec1c05015a9223b822688cd18e8934197b55f94bd3fbbf956d93c74cb54193fa4235492be0371bac7c60c03b2d3ab16fac739a8b664739ac4334684779568f7ba8358664e5012ef9447d20db63182edebe75ec48aa62444146a198b25836d74d954225debb8bde3fd1fc702db92d856c497cf39a316cdb72d61f205a8eeffbbf4e1c08e4fdc500a6931ff93603bdb5302749b6faa6674a337c963c027a1af07146ea2a7db8fb555d5fc9a6c63def4697757c11e623c79733d1a9e1ed585af2fe3667580230c2bfdb9bb81938dbf0a7cbf93ef619c08baa76

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem covers : (PrimeBits.smallPrimes 4096).all (fun p => wheel%p==0) = true := by
  decide +kernel

set_option maxRecDepth 20000 in
private theorem divides_factorial : wheel ∣ Nat.factorial 4096 := by decide +kernel

def quickPrime (n : ℕ) : Bool :=
  if 4096<n ∧ n≤16777216 then decide (n.Coprime wheel) else decide (2≤n ∧ n.minFac=n)

theorem quickPrime_iff {n : ℕ} : quickPrime n = true ↔ n.Prime := by
  unfold quickPrime
  split
  next h =>
    simp only [decide_eq_true_eq]
    constructor
    · intro hc
      by_contra hnp
      have hp := Nat.minFac_prime (by omega : n≠1)
      have hs := Nat.minFac_sq_le_self (by omega : 0<n) hnp
      have hl : n.minFac≤4096 := by
        by_contra! hb
        have := Nat.pow_le_pow_left (by omega : 4097≤n.minFac) 2
        omega
      have hz := List.all_eq_true.mp covers n.minFac (PrimeBits.mem_smallPrimes.mpr ⟨hl,hp⟩)
      exact hp.not_dvd_one (hc ▸ Nat.dvd_gcd (Nat.minFac_dvd n)
        (Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hz)))
    · intro hp
      exact hp.coprime_iff_not_dvd.mpr fun hd => (not_le_of_gt h.1)
        (hp.dvd_factorial.mp (hd.trans divides_factorial))
  next => simp [Nat.prime_def_minFac]

end Goldbach.CentralCoprime
