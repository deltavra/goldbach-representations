import Goldbach.ExtendedOdd.Blocks06

namespace Goldbach.ExtendedOdd

set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
set_option Elab.async false in
theorem blocks08 : Covered 1024 1152 := by
  apply covered_of_four (a:=256) (b:=32)
  intro r hr
  interval_cases r <;> as_aux_lemma => decide +kernel

end Goldbach.ExtendedOdd
