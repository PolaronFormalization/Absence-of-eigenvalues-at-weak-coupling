import Froehlich.Nodes.KE02MomentumDifferences
import Froehlich.Nodes.KE02PsiZeroQuadratic

set_option autoImplicit false
noncomputable section
namespace Froehlich

/-- The source's two contributions are the even zero-momentum quadratic
term and the mixed P,q difference, with constants fixed before coupling. -/
theorem kernelPsi_uniform_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P q : GW.Space), ‖P‖ ≤ 1/4 →
      |kernelPsi e he g hg hs P q| ≤ C*omega q*(omega q+‖P‖) := by
  obtain ⟨A,hA,hZero⟩ := kernelPsi_zero_quadratic_uniform
  obtain ⟨B,hB,hDiff⟩ := kernelMomentumDifferences_uniform
  refine ⟨A+B,by positivity,?_⟩
  intro e he g hg hs P q hP
  have hz := hZero e he g hg hs q
  have hd := (hDiff e he g hg hs P hP).1 q
  have ht := abs_add_le (kernelPsi e he g hg hs P q-kernelPsi e he g hg hs 0 q)
    (kernelPsi e he g hg hs 0 q)
  simp only [sub_add_cancel] at ht
  have hquad : A*(omega q)^2 ≤ (A+B)*(omega q)^2 :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB.le) (sq_nonneg _)
  have hlin : B*‖P‖*omega q ≤ (A+B)*‖P‖*omega q :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le) (norm_nonneg P)) (omega_nonneg q)
  calc
    _ ≤ B*‖P‖*omega q+A*(omega q)^2 := ht.trans (add_le_add hd hz)
    _ ≤ (A+B)*‖P‖*omega q+(A+B)*(omega q)^2 := add_le_add hlin hquad
    _ = _ := by ring

end Froehlich
