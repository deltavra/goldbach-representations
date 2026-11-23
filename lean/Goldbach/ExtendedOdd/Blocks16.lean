import Goldbach.ExtendedOdd.Blocks14

namespace Goldbach.ExtendedOdd

set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
set_option Elab.async false in
theorem blocks16 : Covered 2048 2176 := by
  apply covered_of_four (a:=512) (b:=32)
  intro r hr
  interval_cases r <;> as_aux_lemma => decide +kernel

end Goldbach.ExtendedOdd
