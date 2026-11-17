import Froehlich.Nodes.WE06

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Froehlich

/-- Enlarging uniform numerical witnesses preserves the actual scalar package. -/
theorem WE06FixedReference_mono
    (CU CT CN CU' CT' CN' CD e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
    (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (hCU : CU ≤ CU') (hCT : CT ≤ CT') (hCN : CN ≤ CN')
    (h : WE06FixedReference CU CT CN CD e he g hg hs hLower hCD hquad) :
    WE06FixedReference CU' CT' CN' CD e he g hg hs hLower hCD hquad := by
  refine ⟨h.1,h.2.1,?_,?_⟩
  · intro P hP
    exact (h.2.2.1 P hP).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCN (sq_nonneg g)) (norm_nonneg P))
  · intro P hP hP0
    obtain ⟨hi,hr,hu,ht,hp,hb⟩ := h.2.2.2 P hP hP0
    exact ⟨hi,hr,hu.trans (mul_le_mul_of_nonneg_right hCU (sq_nonneg g)),ht,hp,
      hb.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCT (sq_nonneg g)) (norm_nonneg P))⟩

end Froehlich
