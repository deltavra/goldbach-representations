import Goldbach.OddWindow
import Mathlib.Tactic.IntervalCases

namespace Goldbach.OddBlocks

set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
set_option Elab.async false in
theorem last (j : ℕ) (hj : j<320) : OddWindow.checked (640+j)=true := by
  interval_cases j <;> as_aux_lemma => decide +kernel

end Goldbach.OddBlocks
