import Goldbach.ExtendedOdd.First

namespace Goldbach.ExtendedOdd

set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
set_option Elab.async false in
theorem blocks00 : Covered 0 128 := by
  apply firstFour.append
  apply covered_of_four (a:=1) (b:=31)
  intro r hr
  interval_cases r <;> as_aux_lemma => decide +kernel

end Goldbach.ExtendedOdd
