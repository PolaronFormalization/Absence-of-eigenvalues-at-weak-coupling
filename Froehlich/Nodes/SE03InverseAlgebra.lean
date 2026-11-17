import Froehlich.Nodes.OP03

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

/-- The final saturation algebra divides only by the positive vacuum scalar. -/
theorem se03_saturation_of_cancelled_vectors
    (B R : GW.OnePhonon →L[ℂ] GW.OnePhonon) (b u : GW.OnePhonon)
    (tau c : ℝ) (htau : 0 < tau)
    (hRB : R.comp B = ContinuousLinearMap.id ℂ GW.OnePhonon)
    (hBu : B u = (tau : ℂ) • b)
    (hpair : ⟪b,u⟫_ℂ = ((tau*c : ℝ) : ℂ)) :
    ⟪b,R b⟫_ℂ = (c : ℂ) := by
  have hu : u = (tau : ℂ) • R b := by
    have h := congrArg (fun T : GW.OnePhonon →L[ℂ] GW.OnePhonon => T u) hRB
    have hr : R (B u) = u := by
      simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using h
    rw [hBu,map_smul] at hr
    exact hr.symm
  have hscalar : (tau : ℂ)*⟪b,R b⟫_ℂ = (tau : ℂ)*(c : ℂ) := by
    have h := hpair
    rw [hu,inner_smul_right,Complex.ofReal_mul] at h
    exact h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr htau.ne') hscalar

end Froehlich
