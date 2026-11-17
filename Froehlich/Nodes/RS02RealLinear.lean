import Froehlich.Nodes.RS02RieszTransport
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Native real-linear views of continuous conjugate-linear maps. Their
functions and norms are unchanged; real differentiation never assumes
complex differentiability of conjugation. -/
noncomputable section
namespace Froehlich
variable {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [NormedSpace ℂ A] [NormedSpace ℂ B] [NormedSpace ℝ A] [NormedSpace ℝ B]
    [ContinuousSMul ℝ A] [ContinuousSMul ℝ B]

def conjugateLinearReal (f : A →L⋆[ℂ] B) : A →L[ℝ] B :=
  ({ toFun := f
     map_zero' := map_zero f
     map_add' := fun x y => map_add f x y } : A →+ B).toRealLinearMap f.continuous

@[simp] theorem conjugateLinearReal_apply (f : A →L⋆[ℂ] B) (x : A) :
    conjugateLinearReal f x = f x := rfl

theorem conjugateLinearReal_norm_le (f : A →L⋆[ℂ] B) :
    ‖conjugateLinearReal f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ f.opNorm_nonneg
  exact f.le_opNorm

section Adjoint
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedSpace ℝ H] [SMulCommClass ℂ ℝ H] [ContinuousSMul ℝ (H →L[ℂ] H)]

def boundedAdjointReal : (H →L[ℂ] H) →L[ℝ] (H →L[ℂ] H) :=
  conjugateLinearReal (ContinuousLinearMap.adjoint.toLinearIsometry.toContinuousLinearMap :
    (H →L[ℂ] H) →L⋆[ℂ] (H →L[ℂ] H))

@[simp] theorem boundedAdjointReal_apply (T : H →L[ℂ] H) :
    boundedAdjointReal T = T.adjoint := rfl

theorem boundedAdjointReal_norm_le : ‖boundedAdjointReal (H := H)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  simpa only [boundedAdjointReal_apply,one_mul] using (ContinuousLinearMap.adjoint.norm_map T).le

end Adjoint
end Froehlich
