import Goldbach.ExtendedOdd.Blocks19

namespace Goldbach.ExtendedOdd

set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
set_option Elab.async false in
theorem blocks21 : Covered 2688 2816 := by
  apply covered_of_four (a:=672) (b:=32)
  intro r hr
  interval_cases r <;> as_aux_lemma => decide +kernel

end Goldbach.ExtendedOdd
