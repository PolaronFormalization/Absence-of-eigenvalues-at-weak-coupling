import Froehlich.Nodes.WE03IntegralQuadratic

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

theorem weightedEquationEta_zero_quadratic_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
      (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
      (CD : ℝ) (hCD : 0 ≤ CD)
      (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2),
      ‖weightedEquationPerturbation e he g hg hs hLower 0 (by simp)‖ ≤ 1/2 →
      (∀ q, |weightedEquationEtaPrime e he g hg hs 0 hLower (by simp) q| ≤ C*(omega q)^2) ∧
      ∀ᵐ q ∂volume, |weightedEquationEta e he g hg hs hLower 0 (by simp) q| ≤ C*(omega q)^2 := by
  obtain ⟨CP,hCP,hPsi⟩ := kernelPsi_zero_quadratic_uniform
  obtain ⟨CJ,hCJ,hJ⟩ := weightedEquationEta_integral_zero_quadratic
  refine ⟨(4/3 : ℝ)*(CP+CJ),by positivity,?_⟩
  intro e he g hg hs hLower CD hCD hquad hSmall
  have hgSq : g^2 ≤ (1 : ℝ) := by nlinarith [abs_nonneg g,sq_abs g]
  have hPrime (q : GW.Space) : |weightedEquationEtaPrime e he g hg hs 0 hLower (by simp) q| ≤
      ((4/3 : ℝ)*(CP+CJ))*(omega q)^2 := by
    have hI := hJ e he g hg hs hLower CD hCD hquad hSmall q
    have hInner : |kernelPsi e he g hg hs 0 q-g^2*weightedEtaIntegral e he g hg hs 0
        (weightedEquationEta e he g hg hs hLower 0 (by simp)) q| ≤ (CP+CJ)*(omega q)^2 := by
      have hi : g^2*|weightedEtaIntegral e he g hg hs 0
          (weightedEquationEta e he g hg hs hLower 0 (by simp)) q| ≤ CJ*(omega q)^2 := by
        have h := mul_le_mul hgSq hI (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        simpa only [one_mul] using h
      have ht := abs_sub_le (kernelPsi e he g hg hs 0 q) 0
        (g^2*weightedEtaIntegral e he g hg hs 0 (weightedEquationEta e he g hg hs hLower 0 (by simp)) q)
      simp only [sub_zero,zero_sub,abs_neg,abs_mul,abs_of_nonneg (sq_nonneg g)] at ht
      exact ht.trans ((add_le_add (hPsi e he g hg hs q) hi).trans_eq (by ring))
    have hInv : |(thresholdDiagonalMultiplier e he g hg hs q)⁻¹| ≤ (4/3 : ℝ) :=
      thresholdInverseMultiplierCoefficient_bound e he g hg hs hLower q
    unfold weightedEquationEtaPrime
    rw [abs_mul]
    have h := mul_le_mul hInv hInner (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4/3)
    simpa only [mul_assoc] using h
  refine ⟨hPrime,?_⟩
  filter_upwards [weightedEquationEtaPrime_ae e he g hg hs 0 hLower (by simp) CD hCD hquad hSmall] with q hq
  rw [←hq]
  exact hPrime q

/-- Actual zero-momentum solution and raw integral; no regularity is claimed
for a chosen L-infinity representative or the multiplier at zero. -/
def WE03FixedReference (C e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q) : Prop :=
  realLinftyReflection (weightedEquationSolution e he g hg hs hLower 0 (by simp)) =
    weightedEquationSolution e he g hg hs hLower 0 (by simp) ∧
  (∀ᵐ q ∂volume, weightedEquationEta e he g hg hs hLower 0 (by simp) (-q) =
    weightedEquationEta e he g hg hs hLower 0 (by simp) q) ∧
  Function.Even (weightedEtaIntegral e he g hg hs 0 (weightedEquationEta e he g hg hs hLower 0 (by simp))) ∧
  weightedEtaIntegral e he g hg hs 0 (weightedEquationEta e he g hg hs hLower 0 (by simp)) 0 = 0 ∧
  (∀ q, |weightedEtaIntegral e he g hg hs 0 (weightedEquationEta e he g hg hs hLower 0 (by simp)) q| ≤ C*(omega q)^2) ∧
  (∀ q, |weightedEquationEtaPrime e he g hg hs 0 hLower (by simp) q| ≤ C*(omega q)^2) ∧
  ∀ᵐ q ∂volume, |weightedEquationEta e he g hg hs hLower 0 (by simp) q| ≤ C*(omega q)^2

theorem finalWE03 : ∃ C CD s : ℝ, 0 < C ∧ 0 < CD ∧ 0 < s ∧
    ∀ g : ℝ, |g| < s →
      ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
      ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
      ∃ hCD : 0 ≤ CD,
      ∃ hquad : ∀ q : GW.Space,
        |auxiliarySelfEnergy (groundEnergy (fiberHamiltonian g 0)) q he g hg hs-groundEnergy (fiberHamiltonian g 0)| ≤ CD*g^2*‖q‖^2,
      ∃ hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier (groundEnergy (fiberHamiltonian g 0)) he g hg hs q,
      WE03FixedReference C (groundEnergy (fiberHamiltonian g 0)) he g hg hs hLower := by
  obtain ⟨CE,hCE,hEta⟩ := weightedEquationEta_zero_quadratic_uniform
  obtain ⟨CJ,hCJ,hJ⟩ := weightedEquationEta_integral_zero_quadratic
  obtain ⟨CZ,CD,s,hCZ,hCD,hs,hGround⟩ := weightedEquation_ground_smallness
  refine ⟨CE+CJ,CD,s,add_pos hCE hCJ,hCD,hs,?_⟩
  intro g hgs
  obtain ⟨he,hg,haux,hCD0,hquad,hLower,hControl⟩ := hGround g hgs
  have hSmall := (hControl 0 (by simp)).1
  obtain ⟨hp,ha⟩ := hEta _ he g hg haux hLower CD hCD0 hquad hSmall
  refine ⟨he,hg,haux,hCD0,hquad,hLower,
    weightedEquationSolution_zero_reflection _ he g hg haux hLower CD hCD0 hquad hSmall,
    weightedEquationEta_zero_ae_even _ he g hg haux hLower CD hCD0 hquad hSmall,
    weightedEquationEta_integral_zero_even _ he g hg haux hLower CD hCD0 hquad hSmall,
    weightedEtaIntegral_zero _ he g hg haux 0 _,?_,?_,?_⟩
  · intro q
    exact (hJ _ he g hg haux hLower CD hCD0 hquad hSmall q).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCE.le) (sq_nonneg _))
  · intro q
    exact (hp q).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCJ.le) (sq_nonneg _))
  · filter_upwards [ha] with q hq
    exact hq.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCJ.le) (sq_nonneg _))

end Froehlich
