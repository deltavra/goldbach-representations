import Goldbach.ExtendedOdd.Blocks03

namespace Goldbach.ExtendedOdd

set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
set_option Elab.async false in
theorem blocks05 : Covered 640 768 := by
  apply Covered.append (b:=736)
  · apply covered_of_four (a:=160) (b:=24)
    intro r hr
    interval_cases r <;> as_aux_lemma => decide +kernel
  · apply witnessFour.append
    apply covered_of_four (a:=185) (b:=7)
    intro r hr
    interval_cases r <;> as_aux_lemma => decide +kernel

end Goldbach.ExtendedOdd
