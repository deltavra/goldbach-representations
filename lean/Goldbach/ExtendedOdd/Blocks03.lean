import Goldbach.ExtendedOdd.Blocks01

-- Two dependency chains bound the number of simultaneous sieve checks.

namespace Goldbach.ExtendedOdd

set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
set_option Elab.async false in
theorem blocks03 : Covered 384 512 := by
  apply covered_of_four (a:=96) (b:=32)
  intro r hr
  interval_cases r <;> as_aux_lemma => decide +kernel

end Goldbach.ExtendedOdd
