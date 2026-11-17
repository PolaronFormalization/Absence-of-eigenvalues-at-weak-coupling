import Froehlich.Nodes.CA01TotalDerivative
import Froehlich.Nodes.CA01GeneralTaylor
import Froehlich.Nodes.CA01MultiIndexInverse

/-!
CA01 / `lem:normcalculus`, clauses in source order:

1. `coordinateLine_hasDerivAt_of_integral` gives the norm partial from the
   coordinate-line integral. `continuousCoordinatePartials_hasFDerivAt`
   and `euclideanContinuousPartials_hasFDerivAt` assemble the total derivative;
   `euclideanContinuousPartials_continuousDerivative` gives its continuity.
2. `realBilinear_hasFDerivAt` is the native real bounded-bilinear product rule.
   `coordinateMultiPartial_realBilinear` gives the full finite multi-index
   sum, with literal box β ≤ α and coefficient `multiIndexBinomial α β`.
3. `actualInverseFamily_hasFDerivAt` and
   `actualInverseFamily_derivative_apply` differentiate the chosen actual
   inverse on End_ℂ with its real scalar structure.
   `actualInverseFamily_contDiffAt` transfers C^r regularity, and
   `actualInverseFamily_coordinateMultiPartial` gives the exact nonzero-α
   inverse recurrence with the source's multiplication order.
4. `norm_remainder_of_actual_secondDerivative` and
   `norm_remainder_of_second_fderiv` prove the segment remainder bound
   L‖h‖²/2 from actual first/second derivatives on that segment.
-/
