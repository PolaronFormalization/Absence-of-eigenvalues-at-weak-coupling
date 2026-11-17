import Froehlich.Nodes.WE02Representative
import Froehlich.Nodes.WE02Uniform

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

/-- The convenient integral-defined representative has a genuine everywhere
weighted bound, without a pointwise bound on any chosen L-infinity representative. -/
theorem weightedEquationEtaPrime_bound_uniform : ∃ CE : ℝ, 0 < CE ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
      (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
      (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
      ‖weightedEquationPerturbation e he g hg hs hLower P hP‖ ≤ 1/2 → ∀ q : GW.Space,
      |weightedEquationEtaPrime e he g hg hs P hLower hP q| ≤ CE*omega q := by
  obtain ⟨CP,hCP,hPsi⟩ := normalizedKernelPsi_bound_uniform
  obtain ⟨CZ,hCZ,hZ⟩ := weightedEquationSolution_norm_uniform
  obtain ⟨CI,hCI,hI⟩ := weightedEtaIntegral_uniform
  refine ⟨(4/3 : ℝ)*(CP+CI*CZ),by positivity,?_⟩
  intro e he g hg hs hLower P hP hSmall q
  have hz := hZ e he g hg hs hLower P hP hSmall
  have hEta : ∀ᵐ r ∂volume, |weightedEquationEta e he g hg hs hLower P hP r| ≤ CZ*omega r := by
    filter_upwards [weightedEquationEta_bound e he g hg hs hLower P hP] with r hr
    exact hr.trans (mul_le_mul_of_nonneg_right hz (omega_nonneg r))
  have hInt := (hI e he g hg hs P hP CZ hCZ.le
    (weightedEquationEta e he g hg hs hLower P hP)
    (weightedEquationEta_aestronglyMeasurable e he g hg hs hLower P hP) hEta q).2
  have hPsiBound : |kernelPsi e he g hg hs P q| ≤ CP*omega q := by
    rw [←omega_normalizedKernelPsi e he g hg hs P q,abs_mul,abs_of_nonneg (omega_nonneg q)]
    have hp := hPsi e he g hg hs P q hP
    simpa only [Real.norm_eq_abs,mul_comm] using mul_le_mul_of_nonneg_left hp (omega_nonneg q)
  have hgSq : g^2 ≤ (1 : ℝ) := by nlinarith [abs_nonneg g,sq_abs g]
  have hInner : |kernelPsi e he g hg hs P q-g^2*weightedEtaIntegral e he g hg hs P
      (weightedEquationEta e he g hg hs hLower P hP) q| ≤ (CP+CI*CZ)*omega q := by
    have hi : g^2*|weightedEtaIntegral e he g hg hs P
        (weightedEquationEta e he g hg hs hLower P hP) q| ≤ CI*CZ*omega q := by
      have hIntAbs : |weightedEtaIntegral e he g hg hs P
          (weightedEquationEta e he g hg hs hLower P hP) q| ≤ CI*CZ*omega q := by
        simpa only [Real.norm_eq_abs] using hInt
      have hmul := mul_le_mul hgSq hIntAbs
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simpa only [one_mul] using hmul
    have ht : |kernelPsi e he g hg hs P q-g^2*weightedEtaIntegral e he g hg hs P
        (weightedEquationEta e he g hg hs hLower P hP) q| ≤
        |kernelPsi e he g hg hs P q|+|g^2*weightedEtaIntegral e he g hg hs P
          (weightedEquationEta e he g hg hs hLower P hP) q| := by
      simpa only [sub_zero,zero_sub,abs_neg] using
        (abs_sub_le (kernelPsi e he g hg hs P q) 0
          (g^2*weightedEtaIntegral e he g hg hs P (weightedEquationEta e he g hg hs hLower P hP) q))
    rw [abs_mul,abs_of_nonneg (sq_nonneg g)] at ht
    exact ht.trans ((add_le_add hPsiBound hi).trans_eq (by ring))
  have hInv : |(thresholdDiagonalMultiplier e he g hg hs q)⁻¹| ≤ (4/3 : ℝ) :=
    thresholdInverseMultiplierCoefficient_bound e he g hg hs hLower q
  unfold weightedEquationEtaPrime
  rw [abs_mul]
  have h := mul_le_mul hInv hInner (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4/3)
  simpa only [mul_assoc] using h

end Froehlich
