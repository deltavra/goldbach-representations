import Goldbach.FinitePairs
import Goldbach.FactorTable
import Mathlib.Data.Nat.Prime.Basic

namespace Goldbach.OddWindow

open PrimeBits

private abbrev width : ℕ := 524288
private abbrev halo : ℕ := 895
private abbrev root : ℕ := 32768
private abbrev span : ℕ := width+halo
def start (j : ℕ) := 33554433+width*j
private def base (j : ℕ) := start j-halo
private def shift (j d : ℕ) := (base j+(d+1)/2)%d

private def oddPrimes (cap : ℕ) := (smallPrimes cap).filter (fun p => p%2=1)
private def strikes (j : ℕ) : ℕ :=
  maskUnion FactorTable.odds (fun d => stride (span+root) d 20 >>> shift j d)

private def window (mask : ℕ) := ((1 <<< (span+1))-1) ^^^ mask
private def full : ℕ := (1 <<< width)-1
private def covers (mask : ℕ) : Bool :=
  let bits := window mask
  (full &&& maskUnion (oddPrimes 1789) (fun p => bits >>> (halo-(p+1)/2))) == full

def checked (j : ℕ) : Bool := covers (strikes j)

private theorem window_sound {j k : ℕ}
    (hk : k≤span) (hlo : 2≤2*(base j+k)+1)
    (hhi : 2*(base j+k)+1 ≤ 1073741824)
    (hit : (window (strikes j)).testBit k=true) : (2*(base j+k)+1).Prime := by
  let n := 2*(base j+k)+1
  change n.Prime
  by_contra hn
  let d := n.minFac
  have hlon : 2 ≤ n := hlo
  have hd : d.Prime := Nat.minFac_prime (by omega)
  have hdvd : d ∣ n := Nat.minFac_dvd n
  have htwo : d ≠ 2 := by
    rintro h
    obtain ⟨a,ha⟩ := hdvd
    rw [h] at ha
    dsimp [n] at ha
    omega
  have hodd := hd.odd_of_ne_two htwo
  have hroot : d≤root := by
    have hsq := Nat.minFac_sq_le_self (show 0<n by dsimp [n]; omega) hn
    change d^2≤n at hsq
    change n≤1073741824 at hhi
    by_contra! hh
    have h := Nat.pow_le_pow_left (show 32769≤d by dsimp [root] at hh; omega) 2
    omega
  have hd1 : 2*((d+1)/2)=d+1 := by obtain ⟨a,ha⟩ := hodd; omega
  have hd2 : d ∣ 2*(base j+(d+1)/2+k) := by
    have he : 2*(base j+(d+1)/2+k)=n+d := by dsimp [n]; omega
    rw [he]
    exact Nat.dvd_add hdvd (dvd_refl d)
  have hdiv : d ∣ base j+(d+1)/2+k := (hd.dvd_mul.mp hd2).resolve_left
    (fun h => htwo ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hd.ne_one))
  have hshift : d ∣ shift j d+k := by
    apply Nat.dvd_of_mod_eq_zero
    rw [shift,Nat.mod_add_mod]
    exact Nat.mod_eq_zero_of_dvd hdiv
  obtain ⟨t,ht⟩ := hshift
  have hlim : d*t≤span+root := by
    have := Nat.mod_lt (base j+(d+1)/2) hd.pos
    change (base j+(d+1)/2)%d+k=d*t at ht
    omega
  have ht' : t<2^20 := by
    have h := Nat.mul_le_mul_right t hd.one_le
    simp only [one_mul] at h
    dsimp [span,width,halo,root] at hlim
    omega
  have hs := stride_bit (span+root) d 20 t ht' hlim
  have hstruck : (strikes j).testBit k=true := by
    apply (maskUnion_bit _ _ _).mpr
    refine ⟨d,FactorTable.mem_odds hd htwo hroot,?_⟩
    simpa [Nat.testBit_shiftRight, ←ht, Nat.add_comm] using hs
  have hfull : ((1 <<< (span+1) : ℕ)-1).testBit k=true := by
    simp [Nat.one_shiftLeft,show k<span+1 by omega]
  rw [window,Nat.testBit_xor,hfull,hstruck] at hit
  contradiction

theorem checked_sound {j n : ℕ} (hc : checked j=true)
    (hl : start j≤n/2) (hu : n/2<start j+width)
    (hN : n≤1073741824) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≤1789 ∧ p+q=n := by
  let k := n/2-start j
  have hcov : covers (strikes j)=true := hc
  have hk : k<width := by dsimp [k]; omega
  have hf : full.testBit k=true := by simp [full,Nat.one_shiftLeft,hk]
  have hb := congrArg (fun a : ℕ => a.testBit k) (beq_iff_eq.mp hcov)
  simp only [Nat.testBit_and,hf,Bool.true_and] at hb
  obtain ⟨p,hp,hbit⟩ := (maskUnion_bit _ _ k).mp hb
  obtain ⟨hh,hodd⟩ := List.mem_filter.mp hp
  obtain ⟨hbound,hprime⟩ := mem_smallPrimes.mp hh
  have hodd' : p%2=1 := by simpa using hodd
  rw [Nat.testBit_shiftRight] at hbit
  have hstart : halo≤start j := by dsimp [start,halo]; omega
  have hev : n%2=0 := Nat.even_iff.mp he
  have heq : 2*(base j+(k+(halo-(p+1)/2)))+1+p=n := by
    dsimp [k,base]
    change start j≤n/2 at hl
    dsimp [halo] at *
    omega
  have hlow : 2≤2*(base j+(k+(halo-(p+1)/2)))+1 := by dsimp [base,start,halo]; omega
  have hupper : 2*(base j+(k+(halo-(p+1)/2)))+1 ≤ 1073741824 := by omega
  have hqp := window_sound (j:=j) (k:=k+(halo-(p+1)/2))
    (by dsimp [span]; omega) hlow hupper (by simpa [Nat.add_comm] using hbit)
  exact ⟨p,_,hprime,hqp,hbound,(Nat.add_comm _ _).trans heq⟩

end Goldbach.OddWindow
