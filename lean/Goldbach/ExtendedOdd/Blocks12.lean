import Goldbach.ExtendedOdd.Blocks10

namespace Goldbach.ExtendedOdd

set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
set_option Elab.async false in
theorem blocks12 : Covered 1536 1664 := by
  apply covered_of_four (a:=384) (b:=32)
  intro r hr
  interval_cases r <;> as_aux_lemma => decide +kernel

end Goldbach.ExtendedOdd
