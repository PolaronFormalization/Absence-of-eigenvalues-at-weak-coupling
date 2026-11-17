import Froehlich.Nodes.FA02

/-! The actual bounded Hermitian form in PO01, using native rank-one maps. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def twoVectorOperator (B : H →L[ℂ] H) (b t : H) (c : ℝ) : H →L[ℂ] H :=
  B + (c : ℂ) • InnerProductSpace.rankOne ℂ t t +
    InnerProductSpace.rankOne ℂ b t + InnerProductSpace.rankOne ℂ t b

def twoVectorForm (B : H →L[ℂ] H) (b t : H) (c : ℝ) : GW.Analysis.BoundedForm H :=
  (innerSL ℂ).comp (twoVectorOperator B b t c).adjoint

theorem twoVectorForm_apply (B : H →L[ℂ] H) (b t : H) (c : ℝ) (w u : H) :
    twoVectorForm B b t c w u = ⟪w,twoVectorOperator B b t c u⟫_ℂ :=
  (twoVectorOperator B b t c).adjoint_inner_left u w

theorem twoVectorOperator_selfadjoint (B : H →L[ℂ] H) (hB : B.adjoint = B)
    (b t : H) (c : ℝ) : (twoVectorOperator B b t c).adjoint = twoVectorOperator B b t c := by
  simp only [twoVectorOperator, map_add, map_smulₛₗ, InnerProductSpace.adjoint_rankOne,
    Complex.conj_ofReal, hB]
  abel

theorem twoVectorForm_hermitian (B : H →L[ℂ] H) (hB : B.adjoint = B)
    (b t : H) (c : ℝ) (w u : H) :
    twoVectorForm B b t c w u = (starRingEnd ℂ) (twoVectorForm B b t c u w) := by
  rw [twoVectorForm_apply,twoVectorForm_apply,← (twoVectorOperator B b t c).adjoint_inner_left,
    twoVectorOperator_selfadjoint B hB]
  exact (inner_conj_symm _ _).symm

theorem twoVectorForm_diagonal (B : H →L[ℂ] H) (b t : H) (c : ℝ) (u : H) :
    (twoVectorForm B b t c u u).re = (⟪u,B u⟫_ℂ).re + c*‖⟪t,u⟫_ℂ‖^2 +
      2*((starRingEnd ℂ) ⟪t,u⟫_ℂ*⟪b,u⟫_ℂ).re := by
  rw [twoVectorForm_apply]
  simp only [twoVectorOperator,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    InnerProductSpace.rankOne_apply,inner_add_right,inner_smul_right]
  rw [← inner_conj_symm u t,← inner_conj_symm u b]
  simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_re,Complex.conj_im,Complex.sq_norm,Complex.normSq_apply]
  ring

end Froehlich
