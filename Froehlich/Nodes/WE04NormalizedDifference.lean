import Froehlich.Nodes.WE04SpecificIntegral

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

theorem weightedKernelSource_difference_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
      ‖weightedKernelSource e he g hg hs P hP-weightedKernelSource e he g hg hs 0 (by simp)‖ ≤ C*‖P‖ := by
  obtain ⟨C,hC,hB⟩ := kernelMomentumDifferences_uniform
  refine ⟨C,hC,?_⟩
  intro e he g hg hs P hP
  apply linftyReal_norm_le_of_ae_bound _ _ (mul_nonneg hC.le (norm_nonneg P))
  filter_upwards [Lp.coeFn_sub (weightedKernelSource e he g hg hs P hP)
      (weightedKernelSource e he g hg hs 0 (by simp)),
    weightedKernelSource_ae e he g hg hs P hP,weightedKernelSource_ae e he g hg hs 0 (by simp)] with q hsub hp hz
  rw [hsub,Pi.sub_apply,hp,hz,Real.norm_eq_abs]
  by_cases hq : q = 0
  · subst q
    rw [normalizedKernelPsi_zero,normalizedKernelPsi_zero,sub_self,abs_zero]
    positivity
  · have ho : 0 < omega q := lt_min (norm_pos_iff.mpr hq) zero_lt_one
    simp only [normalizedKernelPsi,ite_eq_right hq]
    rw [←sub_div,abs_div,abs_of_pos ho]
    exact (div_le_iff₀ ho).mpr ((hB e he g hg hs P hP).1 q)

/-- Only the actual zero-momentum solution is tested; this is not an
operator-norm Lipschitz estimate on arbitrary L-infinity inputs. -/
theorem weightedKernelOperator_specific_difference_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
      (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
      (CD : ℝ) (hCD : 0 ≤ CD)
      (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2),
      ‖weightedEquationPerturbation e he g hg hs hLower 0 (by simp)‖ ≤ 1/2 →
      ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
      ‖weightedKernelOperator e he g hg hs P hP (weightedEquationSolution e he g hg hs hLower 0 (by simp))-
        weightedKernelOperator e he g hg hs 0 (by simp) (weightedEquationSolution e he g hg hs hLower 0 (by simp))‖ ≤ C*‖P‖ := by
  obtain ⟨CI,hCI,hI⟩ := weightedEtaIntegral_difference_uniform
  obtain ⟨CE,hCE,hE⟩ := weightedEquationEta_zero_quadratic_uniform
  refine ⟨CI*CE,mul_pos hCI hCE,?_⟩
  intro e he g hg hs hLower CD hCD hquad hSmall P hP
  let z := weightedEquationSolution e he g hg hs hLower 0 (by simp)
  let eta := weightedEquationEta e he g hg hs hLower 0 (by simp)
  have hQuad : ∀ᵐ r ∂volume, |eta r| ≤ CE*(omega r)^2 :=
    (hE e he g hg hs hLower CD hCD hquad hSmall).2
  have hInt (q : GW.Space) := hI e he g hg hs P hP CE hCE.le eta
    (weightedEquationEta_aestronglyMeasurable e he g hg hs hLower 0 (by simp)) hQuad q
  apply linftyReal_norm_le_of_ae_bound _ _ (mul_nonneg (mul_nonneg hCI.le hCE.le) (norm_nonneg P))
  filter_upwards [Lp.coeFn_sub (weightedKernelOperator e he g hg hs P hP z)
      (weightedKernelOperator e he g hg hs 0 (by simp) z),
    weightedKernelOperator_ae e he g hg hs P hP z,weightedKernelOperator_ae e he g hg hs 0 (by simp) z]
      with q hsub hp hz
  rw [hsub,Pi.sub_apply,hp,hz,Real.norm_eq_abs]
  by_cases hq : q = 0
  · subst q
    rw [normalizedWeightedIntegral_zero,normalizedWeightedIntegral_zero,sub_self,abs_zero]
    positivity
  · have ho : 0 < omega q := lt_min (norm_pos_iff.mpr hq) zero_lt_one
    have hlink : omega q*(normalizedWeightedIntegral e he g hg hs P z q-
        normalizedWeightedIntegral e he g hg hs 0 z q) =
        weightedEtaIntegral e he g hg hs P eta q-weightedEtaIntegral e he g hg hs 0 eta q := by
      change omega q*(normalizedWeightedIntegral e he g hg hs P z q-
        normalizedWeightedIntegral e he g hg hs 0 z q) =
        weightedEtaIntegral e he g hg hs P (fun r => omega r*z r) q-
          weightedEtaIntegral e he g hg hs 0 (fun r => omega r*z r) q
      rw [weightedEtaIntegral_omega_mul,weightedEtaIntegral_omega_mul]
      ring
    have h := hInt q
    rw [←hlink,abs_mul,abs_of_pos ho] at h
    apply (mul_le_mul_iff_right₀ ho).mp
    simpa only [mul_assoc,mul_comm,mul_left_comm] using h

end Froehlich
