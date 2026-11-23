import Goldbach.FinitePairs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Term

namespace Goldbach.ExtendedOdd.MaskTable

open Lean Elab Term PrimeBits

abbrev cap : ℕ := 524288 + 931 + 65536

-- Generate one closed numeral for the periodic mask of each sieving prime.
-- Equality to the mathematical mask and completeness are both checked below.
elab "factorPeriodTable%" : term => do
  let rows := (Array.range 256).map fun g =>
    (List.range 256).filterMap fun i =>
      let d := 256*g+i
      if 2<d ∧ d.minFac=d then some (d, stride cap d 20) else none
  return toExpr rows

noncomputable def rows : Array (List (ℕ × ℕ)) := factorPeriodTable%

private noncomputable def complete (g : ℕ) := (List.range 256).all fun i =>
  let d := 256*g+i
  if 2<d ∧ d.minFac=d then
    rows[g]!.any fun e => e.1 == d && e.2 == stride cap d 20
  else true

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
set_option Elab.async false in
private theorem blocks (g : ℕ) (hg : g<256) : complete g=true := by
  interval_cases g <;> as_aux_lemma => decide +kernel

theorem mem_rows {d : ℕ} (hd : d.Prime) (hodd : d ≠ 2) (hroot : d ≤ 65536) :
    (d, stride cap d 20) ∈ rows.toList.flatten := by
  have ho := hd.odd_of_ne_two hodd
  have hbound : d/256<256 := by obtain ⟨t, ht⟩ := ho; omega
  have hsize : rows.size=256 := by decide +kernel
  have hidx : d/256<rows.size := by omega
  have hb := List.all_eq_true.mp (blocks _ hbound) (d%256)
    (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have he : 256*(d/256)+d%256=d := by omega
  have h2 := hd.two_le
  simp only [he, if_pos (And.intro (by omega : 2<d) hd.minFac_eq),
    getElem!_pos rows (d/256) hidx, List.any_eq_true] at hb
  obtain ⟨⟨a,b⟩, hm, ha⟩ := hb
  simp only [Bool.and_eq_true, beq_iff_eq] at ha
  obtain ⟨rfl,rfl⟩ := ha
  exact List.mem_flatten.mpr ⟨_, Array.mem_toList_iff.mpr (Array.getElem_mem hidx), hm⟩

end Goldbach.ExtendedOdd.MaskTable
