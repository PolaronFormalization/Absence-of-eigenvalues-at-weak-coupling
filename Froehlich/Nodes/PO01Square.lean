import Froehlich.Nodes.FA02

/-! Exact completion of the square for the source two-vector form. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem twoVector_completion_square (B R : H →L[ℂ] H) (hB : B.adjoint = B)
    (hBR : ∀ v, B (R v) = v) (b u : H) (a : ℂ) (c : ℝ) :
    (⟪u,B u⟫_ℂ).re + c*‖a‖^2 + 2*((starRingEnd ℂ) a * ⟪b,u⟫_ℂ).re =
      (⟪u+a • R b,B (u+a • R b)⟫_ℂ).re + (c-(⟪b,R b⟫_ℂ).re)*‖a‖^2 := by
  have hx := hBR b
  have hy : ⟪R b,B u⟫_ℂ = ⟪b,u⟫_ℂ := by
    rw [← B.adjoint_inner_left,hB,hx]
  have hquad : ⟪u+a • R b,B (u+a • R b)⟫_ℂ =
      ⟪u,B u⟫_ℂ + a*⟪u,b⟫_ℂ + (starRingEnd ℂ) a*⟪b,u⟫_ℂ +
        ((starRingEnd ℂ) a*a)*⟪R b,b⟫_ℂ := by
    simp only [map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,
      inner_smul_right,hx,hy]
    ring
  have hconj : ⟪u,b⟫_ℂ = (starRingEnd ℂ) ⟪b,u⟫_ℂ := (inner_conj_symm _ _).symm
  have hreal : (⟪R b,b⟫_ℂ).re = (⟪b,R b⟫_ℂ).re := inner_re_symm (𝕜 := ℂ) _ _
  rw [hquad,hconj]
  simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.sq_norm,Complex.normSq_apply,hreal]
  ring

end Froehlich
