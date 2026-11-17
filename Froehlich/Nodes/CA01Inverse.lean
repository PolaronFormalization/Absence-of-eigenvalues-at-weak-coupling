import Froehlich.Nodes.BA02
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Real norm differentiation of actual bounded complex-linear inverses. -/
noncomputable section
open scoped Topology
namespace Froehlich
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

namespace BoundedEndReal
/-- The native restriction-of-scalars algebra is installed on the SAME
complex-linear endomorphism carrier, only when this calculus scope is opened. -/
scoped instance realNormedAlgebra : NormedAlgebra ℝ (E →L[ℂ] E) :=
  NormedAlgebra.restrictScalars ℝ ℂ (E →L[ℂ] E)

scoped instance realScalarTower : IsScalarTower ℝ (E →L[ℂ] E) (E →L[ℂ] E) where
  smul_assoc r T S := by
    change (r • T)*S = r • (T*S)
    apply ContinuousLinearMap.ext
    intro z
    rfl

scoped instance realSMulComm : SMulCommClass ℝ (E →L[ℂ] E) (E →L[ℂ] E) where
  smul_comm r T S := by
    change r • (T*S) = T*(r • S)
    apply ContinuousLinearMap.ext
    intro z
    change r • T (S z) = T (r • S z)
    exact ((T.restrictScalars ℝ).map_smul r (S z)).symm
end BoundedEndReal

open scoped BoundedEndReal

def actualInverseUnit (T R : E →L[ℂ] E) (hTR : T*R = 1) (hRT : R*T = 1) : (E →L[ℂ] E)ˣ where
  val := T
  inv := R
  val_inv := hTR
  inv_val := hRT

theorem actualInverseUnit_inv_coe (T R : E →L[ℂ] E) (hTR : T*R = 1) (hRT : R*T = 1) :
    ((actualInverseUnit T R hTR hRT)⁻¹ : (E →L[ℂ] E)ˣ) =
      actualInverseUnit R T hRT hTR := rfl

theorem actualInverse_ringInverse (T R : E →L[ℂ] E) (hTR : T*R = 1) (hRT : R*T = 1) :
    Ring.inverse T = R := Ring.inverse_unit (actualInverseUnit T R hTR hRT)

/-- The parameter field is genuinely real; the algebra consists of the same
bounded complex-linear endomorphisms used by the resolvent construction. -/
theorem actualInverse_hasFDerivAt (T R : E →L[ℂ] E) (hTR : T*R = 1) (hRT : R*T = 1) :
    HasFDerivAt (Ring.inverse : (E →L[ℂ] E) → (E →L[ℂ] E))
      (-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℂ] E) R R) T :=
  hasFDerivAt_ringInverse (𝕜 := ℝ) (actualInverseUnit T R hTR hRT)

theorem actualInverse_derivative_apply (R A : E →L[ℂ] E) :
    (-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℂ] E) R R) A = -R*A*R := by
  change -(R*A*R) = -R*A*R
  simp only [neg_mul]

/-- A concrete instantiation also checks the actual real-algebra instances. -/
example : HasFDerivAt (Ring.inverse : (ℂ →L[ℂ] ℂ) → (ℂ →L[ℂ] ℂ))
    (-ContinuousLinearMap.mulLeftRight ℝ (ℂ →L[ℂ] ℂ) 1 1) 1 :=
  actualInverse_hasFDerivAt 1 1 (one_mul _) (one_mul _)

end Froehlich
