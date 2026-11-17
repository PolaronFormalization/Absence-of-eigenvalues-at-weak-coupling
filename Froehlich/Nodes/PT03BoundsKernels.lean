import Froehlich.Nodes.PT03BoundsCutoffSource
import Froehlich.Nodes.RS02SourceDerivativesCompositionFinalBounds

set_option autoImplicit false

/-! Uniform scalar bounds for the literal PT03 kernels. No threshold-form
identity, pull-through substitution or distributional object is assumed. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

private theorem pt03_extended_norm (n : ℕ) (e : ℝ) (p : GW.Space)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) :
    ‖auxiliaryExtendedResolvent n e p he g hg hs‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖auxiliaryResolvent n e p he g hg hs (highSectorProject n f)‖ ≤ _
  exact ((auxiliaryResolvent n e p he g hg hs).le_opNorm _).trans
    (mul_le_mul (auxiliaryResolvent_norm_le n e p he g hg hs)
      (highSectorProjection_norm_le n f) (norm_nonneg _) (by norm_num))

private theorem pt03_matrix_bound (u v : GW.Fock.Carrier)
    (Z X : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) (H : ℝ) (hH : 0 ≤ H)
    (hu : ‖u‖ ≤ H) (hv : ‖v‖ ≤ H) (hZ : ‖Z‖ ≤ 2) (hX : ‖X‖ ≤ 2) :
    ‖⟪GW.Fock.vacuum-u,Z (GW.Fock.vacuum-v)⟫_ℂ+⟪u,X v⟫_ℂ‖ ≤
      2*(1+H)^2+2*H^2 := by
  have hu0 : ‖GW.Fock.vacuum-u‖ ≤ 1+H :=
    (norm_sub_le _ _).trans (by simpa only [GW.Fock.vacuum_norm] using add_le_add le_rfl hu)
  have hv0 : ‖GW.Fock.vacuum-v‖ ≤ 1+H :=
    (norm_sub_le _ _).trans (by simpa only [GW.Fock.vacuum_norm] using add_le_add le_rfl hv)
  have hzv : ‖Z (GW.Fock.vacuum-v)‖ ≤ 2*(1+H) :=
    (Z.le_opNorm _).trans (mul_le_mul hZ hv0 (norm_nonneg _) (by norm_num))
  have hxv : ‖X v‖ ≤ 2*H :=
    (X.le_opNorm _).trans (mul_le_mul hX hv (norm_nonneg _) (by norm_num))
  have h1 : ‖⟪GW.Fock.vacuum-u,Z (GW.Fock.vacuum-v)⟫_ℂ‖ ≤ 2*(1+H)^2 := by
    refine (norm_inner_le_norm _ _).trans ?_
    exact (mul_le_mul hu0 hzv (norm_nonneg _) (by linarith)).trans_eq (by ring)
  have h2 : ‖⟪u,X v⟫_ℂ‖ ≤ 2*H^2 := by
    refine (norm_inner_le_norm _ _).trans ?_
    exact (mul_le_mul hu hxv (norm_nonneg _) hH).trans_eq (by ring)
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

theorem thresholdKernels_uniform_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P q r : GW.Space), ‖P‖ ≤ 1/4 →
      ‖thresholdKernelJ e he g hg hs P q r‖ ≤ C ∧
      ‖thresholdKernelC e he g hg hs P q r‖ ≤ C ∧
      ∀ Lambda : GW.Operators.PositiveCutoff,
        ‖cutoffThresholdKernelJ e he g hg hs Lambda P q r‖ ≤ C ∧
        ‖cutoffThresholdKernelC e he g hg hs Lambda P q r‖ ≤ C := by
  obtain ⟨CS,hCS,hS⟩ := auxiliaryGroundSourceVector_derivatives_uniform 0 (by simp)
  obtain ⟨CC,hCC,hCut⟩ := cutoffThresholdSourceVector_uniform
  let H := CS+CC
  have hH : 0 ≤ H := (add_pos hCS hCC).le
  let B := 2*(1+H)^2+2*H^2
  have hB : 0 ≤ B := add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (by norm_num) (sq_nonneg _))
  let C := 16/11+B+1
  refine ⟨C,by dsimp only [C]; linarith,?_⟩
  intro g e he hg hs P q r hP
  have hSing (t : GW.Space) : ‖auxiliaryGroundSourceVector e t he g hg hs‖ ≤ H := by
    have h := hS g e he hg hs ((EuclideanSpace.equiv (Fin 3) ℝ) t)
    have hlin : ‖auxiliaryGroundSourceVector e t he g hg hs‖ ≤ CS*|g| := by
      simpa only [coordinateMultiPartial_zero,ContinuousLinearEquiv.symm_apply_apply] using! h
    exact hlin.trans ((mul_le_mul_of_nonneg_left hg hCS.le).trans
      (by dsimp only [H]; nlinarith))
  have hCutoff (Lambda : GW.Operators.PositiveCutoff) (t : GW.Space) :
      ‖cutoffThresholdSourceVector e he g hg hs Lambda t‖ ≤ H :=
    (hCut g e he hg hs Lambda t).trans ((mul_le_mul_of_nonneg_left hg hCC.le).trans
      (by dsimp only [H]; nlinarith))
  have hj : ‖thresholdKernelJ e he g hg hs P q r‖ ≤ B :=
    pt03_matrix_bound _ _ _ _ H hH (hSing q) (hSing r)
      (pt03_extended_norm 0 e (P+q+r) he g hg hs) (pt03_extended_norm 2 e (-P) he g hg hs)
  have hdelta : ‖(((1+e-‖P‖^2)⁻¹ : ℝ) : ℂ)‖ ≤ (16/11 : ℝ) := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact thresholdKernel_denominator_inv_bound e he P hP
  have hBC : B ≤ C := by dsimp only [C]; linarith
  refine ⟨hj.trans hBC,?_,?_⟩
  · exact ((norm_sub_le _ _).trans (add_le_add hdelta hj)).trans (by dsimp only [C]; linarith)
  · intro Lambda
    have hjc : ‖cutoffThresholdKernelJ e he g hg hs Lambda P q r‖ ≤ B :=
      pt03_matrix_bound _ _ _ _ H hH (hCutoff Lambda q) (hCutoff Lambda r)
        (cutoffAuxiliaryExtendedResolvent_norm_le 0 e (P+q+r) he Lambda g hg hs)
        (cutoffAuxiliaryExtendedResolvent_norm_le 2 e (-P) he Lambda g hg hs)
    exact ⟨hjc.trans hBC,((norm_sub_le _ _).trans (add_le_add hdelta hjc)).trans
      (by dsimp only [C]; linarith)⟩

end Froehlich
