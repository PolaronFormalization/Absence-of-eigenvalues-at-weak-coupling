import Froehlich.Nodes.WE06Scalars

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

/-- The genuine nonzero-momentum source has squared norm proportional to 1/|P|. -/
theorem translatedHilbertSource_norm_sq (g : ℝ) (P : GW.Space) (hP0 : P ≠ 0) :
    ‖translatedHilbertSource g P hP0‖^2 = g^2*(∫ q : GW.Space,muDensity P q) := by
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  calc
    _ = ∫ q : GW.Space,g^2*muDensity P q := by
      apply integral_congr_ae
      filter_upwards [translatedHilbertSource_ae g P hP0] with q hq
      rw [hq]
      simp only [thresholdSource,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        mul_pow,sq_abs,wDensity_sq]
    _ = _ := integral_const_mul _ _

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4)
    (hN : ‖thresholdBoundedOperator e he g hg hs CD hCD hquad P hP-1‖ ≤ 1/2)

include hN in
theorem thresholdScalarT_bound_norm (hP0 : P ≠ 0) :
    0 ≤ thresholdScalarT e he g hg hs CD hCD hquad P hP hP0 ∧
    thresholdScalarT e he g hg hs CD hCD hquad P hP hP0 ≤
      2*‖translatedHilbertSource g P hP0‖^2 := by
  let B := thresholdBoundedOperator e he g hg hs CD hCD hquad P hP
  let R := thresholdBoundedInverse e he g hg hs CD hCD hquad P hP
  let t := translatedHilbertSource g P hP0
  have hInv := thresholdBoundedInverse_spec e he g hg hs CD hCD hquad P hP hN
  have hBR (z : GW.OnePhonon) : B (R z) = z := by
    have h := congrArg (fun A : GW.OnePhonon →L[ℂ] GW.OnePhonon => A z) hInv.2.1
    simpa only [mul_apply_eq_comp,one_apply_eq_self] using h
  have hPos (v : GW.OnePhonon) : 0 ≤ (⟪v,B v⟫_ℂ).re :=
    (div_nonneg (sq_nonneg ‖v‖) (by norm_num : (0 : ℝ) ≤ 2)).trans
      (thresholdBoundedOperator_quadratic_lower e he g hg hs CD hCD hquad P hP hN v)
  constructor
  · exact inverse_nonnegative B R
      (thresholdBoundedOperator_selfadjoint e he g hg hs CD hCD hquad P hP) hBR hPos t
  · have hRt : ‖R t‖ ≤ 2*‖t‖ := (R.le_opNorm t).trans
      (mul_le_mul_of_nonneg_right hInv.2.2 (norm_nonneg t))
    have h := (re_inner_le_norm (𝕜 := ℂ) t (R t)).trans
      (mul_le_mul_of_nonneg_left hRt (norm_nonneg t))
    exact h.trans_eq (by ring)

/-- The source's T estimate retains the exact single inverse momentum power. -/
theorem thresholdScalarT_uniform : ∃ CT : ℝ, 0 < CT ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (CD : ℝ) (hCD : 0 ≤ CD)
      (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
      (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
      ‖thresholdBoundedOperator e he g hg hs CD hCD hquad P hP-1‖ ≤ 1/2 →
      ∀ hP0 : P ≠ 0,
      0 ≤ thresholdScalarT e he g hg hs CD hCD hquad P hP hP0 ∧
      thresholdScalarT e he g hg hs CD hCD hquad P hP hP0 ≤ CT*g^2/‖P‖ := by
  obtain ⟨CI,hCI,hWeighted,hMu⟩ := moving_singularity_estimates
  refine ⟨2*CI,mul_pos (by norm_num) hCI,?_⟩
  intro e he g hg hs CD hCD hquad P hP hN hP0
  have ht := thresholdScalarT_bound_norm e he g hg hs CD hCD hquad P hP hN hP0
  refine ⟨ht.1,ht.2.trans ?_⟩
  rw [translatedHilbertSource_norm_sq]
  have h := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (hMu P hP0).2 (sq_nonneg g)) (by norm_num : (0 : ℝ) ≤ 2)
  exact h.trans_eq (by simp only [div_eq_mul_inv]; ring)

end Froehlich
