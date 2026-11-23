import Goldbach.ExtendedOdd.Coverage

namespace Goldbach.ExtendedOdd

set_option maxRecDepth 160000 in
set_option maxHeartbeats 0 in
set_option Elab.async false in
theorem firstFour : Covered 0 4 := by
  apply covered_of_four (a:=0) (b:=1)
  intro r hr
  interval_cases r <;> decide +kernel

end Goldbach.ExtendedOdd
