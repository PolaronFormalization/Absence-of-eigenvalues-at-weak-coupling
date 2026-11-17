import Froehlich.Nodes.CA03SingleDifference
import Froehlich.Nodes.CA03VariableDifferences
import Froehlich.Nodes.CA03Even

/-!
CA03 / `lem:finitedifferences`, in source order:

* `norm_finiteDifference_le` proves the one-difference bound
  2M min(‖h‖,1), reusing the native mean-value estimate.
* `norm_iteratedVariableDifference` proves the exact multiple-difference
  bound 2^l M ∏ min(‖h_i‖,1) in distinct vector variables. Its hypotheses
  bound only the actual selected mixed derivative operators, including
  order zero. `selectedMixedFDeriv` is the native iterated derivative
  restricted to the chosen variable slots.
* `norm_iteratedFiniteDifference_of_selectedMixed_fixedDerivative` starts
  at a fixed actual derivative and counts its initial order in |A0|+l ≤ r.
  It needs only the selected mixed derivatives of that fixed function.
* `even_fderiv_zero` and `even_norm_sub_le_quadratic` give the even real
  C² conclusion |f(h)-f(0)| ≤ M‖h‖²/2 using the exact CA01 remainder.
-/
