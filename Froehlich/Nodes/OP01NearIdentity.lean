import Froehlich.Nodes.BA02

/-! OP01's near-identity step in the actual Banach algebra of bounded
operators. The inverse is the accepted geometric series, with both sides. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

def nearIdentityInverse (B : V →L[ℂ] V) : V →L[ℂ] V := neumannInverse (1-B)

theorem nearIdentityInverse_spec (B : V →L[ℂ] V) (hB : ‖B-1‖ ≤ 1/2) :
    nearIdentityInverse B * B = 1 ∧ B * nearIdentityInverse B = 1 ∧
      ‖nearIdentityInverse B‖ ≤ 2 := by
  have h : ‖1-B‖ ≤ (1/2 : ℝ) := by simpa only [norm_sub_rev] using hB
  have hlt : ‖1-B‖ < 1 := lt_of_le_of_lt h (by norm_num)
  have hl := neumannInverse_left (1-B) hlt
  have hr := neumannInverse_right (1-B) hlt
  have hn := neumannInverse_norm_le (1-B) h (by norm_num : (1/2 : ℝ) < 1)
  simpa only [sub_sub_cancel, nearIdentityInverse] using
    (show neumannInverse (1-B)*B=1 ∧ B*neumannInverse (1-B)=1 ∧
        ‖neumannInverse (1-B)‖ ≤ 2 from
      ⟨by simpa only [sub_sub_cancel] using hl,
       by simpa only [sub_sub_cancel] using hr,by norm_num at hn ⊢; exact hn⟩)

theorem nearIdentity_quadratic_lower (B : V →L[ℂ] V)
    (hB : ‖B-1‖ ≤ 1/2) (u : V) :
    ‖u‖^2/2 ≤ (⟪u,B u⟫_ℂ).re := by
  have hN : ‖(B-1) u‖ ≤ (1/2 : ℝ)*‖u‖ :=
    ((B-1).le_opNorm u).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg u))
  have hinner := re_inner_le_norm (𝕜 := ℂ) (-u) ((B-1) u)
  simp only [inner_neg_left,map_neg,norm_neg] at hinner
  have hinner' : -(⟪u,(B-1) u⟫_ℂ).re ≤ ‖u‖*((1/2 : ℝ)*‖u‖) := by
    exact hinner.trans (mul_le_mul_of_nonneg_left hN (norm_nonneg u))
  have heq : (⟪u,(B-1) u⟫_ℂ).re = (⟪u,B u⟫_ℂ).re-‖u‖^2 := by
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,
      inner_sub_right,Complex.sub_re]
    exact congrArg (fun a : ℝ => (⟪u,B u⟫_ℂ).re-a)
      (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  rw [heq] at hinner'
  nlinarith

end Froehlich
