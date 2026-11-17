import Froehlich.Nodes.WE06InverseIntegrals
import Froehlich.Nodes.WE06ProductDifference

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

/-- The critical linear momentum gain for the actual inverse-response scalar. -/
theorem thresholdScalarN_comparison_uniform : ∃ CN : ℝ, 0 < CN ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
      (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
      (CD : ℝ) (hCD : 0 ≤ CD)
      (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2),
      ‖weightedEquationPerturbation e he g hg hs hLower 0 (by simp)‖ ≤ 1/2 →
      ‖thresholdBoundedOperator e he g hg hs CD hCD hquad 0 (by simp)-1‖ ≤ 1/2 →
      ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
      ‖weightedEquationPerturbation e he g hg hs hLower P hP‖ ≤ 1/2 →
      ‖thresholdBoundedOperator e he g hg hs CD hCD hquad P hP-1‖ ≤ 1/2 →
      |thresholdScalarN e he g hg hs CD hCD hquad P hP-
        thresholdScalarN e he g hg hs CD hCD hquad 0 (by simp)| ≤ CN*g^2*‖P‖ := by
  obtain ⟨C,hC,hProduct⟩ := we06_psi_eta_product_difference_uniform
  obtain ⟨CI,hCI,hMom⟩ := weightedKernelDensity_integral_uniform
  obtain ⟨CDiff,hCDiff,hMoving,_⟩ := moving_singularity_estimates
  refine ⟨C*(CI+CDiff),by positivity,?_⟩
  intro e he g hg hs hLower CD hCD hquad hSmall0 hN0 P hP hSmallP hNP
  let fP := fun q : GW.Space => kernelPsi e he g hg hs P q*weightedEquationEta e he g hg hs hLower P hP q
  let f0 := fun q : GW.Space => kernelPsi e he g hg hs 0 q*weightedEquationEta e he g hg hs hLower 0 (by simp) q
  have hIP := thresholdScalarN_integral e he g hg hs hLower CD hCD hquad P hP hSmallP hNP
  have hI0 := thresholdScalarN_integral e he g hg hs hLower CD hCD hquad 0 (by simp) hSmall0 hN0
  let D := fun q : GW.Space => ‖P‖*weightedKernelDensity P q+weightedMuDifference P q
  have hID : Integrable D volume :=
    ((weightedKernelDensity_integrable P hP).const_mul ‖P‖).add (hMoving P hP).2.1
  have hBound : ∀ᵐ q ∂volume,
      ‖fP q*muDensity P q-f0 q*muDensity 0 q‖ ≤ C*D q := by
    filter_upwards [hProduct e he g hg hs hLower CD hCD hquad hSmall0 P hP hSmallP] with q hq
    have h1 := mul_le_mul_of_nonneg_right hq.1 (muDensity_nonneg P q)
    have h2 := mul_le_mul_of_nonneg_right hq.2 (abs_nonneg (muDensity P q-muDensity 0 q))
    have hsplit : fP q*muDensity P q-f0 q*muDensity 0 q =
        (fP q-f0 q)*muDensity P q+f0 q*(muDensity P q-muDensity 0 q) := by ring
    rw [hsplit,Real.norm_eq_abs]
    have ht := abs_add_le ((fP q-f0 q)*muDensity P q) (f0 q*(muDensity P q-muDensity 0 q))
    rw [abs_mul,abs_of_nonneg (muDensity_nonneg P q),abs_mul] at ht
    exact ht.trans ((add_le_add h1 h2).trans_eq (by
      dsimp only [D,weightedKernelDensity,weightedMuDifference]
      ring))
  have hNorm := norm_integral_le_of_norm_le (hID.const_mul C) hBound
  have hIntD : (∫ q : GW.Space,D q) ≤ (CI+CDiff)*‖P‖ := by
    have hAdd := integral_add ((weightedKernelDensity_integrable P hP).const_mul ‖P‖) (hMoving P hP).2.1
    have hEq : (∫ q : GW.Space,D q) = ‖P‖*(∫ q : GW.Space,weightedKernelDensity P q)+
        (∫ q : GW.Space,weightedMuDifference P q) := by
      simpa only [D,Pi.add_def,integral_const_mul] using! hAdd
    rw [hEq]
    exact (add_le_add (mul_le_mul_of_nonneg_left (hMom P hP) (norm_nonneg P))
      (hMoving P hP).2.2).trans_eq (by ring)
  have hEqDiff : (∫ q : GW.Space,fP q*muDensity P q)-(∫ q : GW.Space,f0 q*muDensity 0 q) =
      ∫ q : GW.Space,fP q*muDensity P q-f0 q*muDensity 0 q := by
    exact (integral_sub hIP.1 hI0.1).symm
  have hDiff : |(∫ q : GW.Space,fP q*muDensity P q)-(∫ q : GW.Space,f0 q*muDensity 0 q)| ≤
      C*(CI+CDiff)*‖P‖ := by
    rw [hEqDiff]
    have h : ‖∫ q : GW.Space,fP q*muDensity P q-f0 q*muDensity 0 q‖ ≤ C*(∫ q : GW.Space,D q) := by
      simpa only [integral_const_mul] using hNorm
    exact h.trans ((mul_le_mul_of_nonneg_left hIntD hC.le).trans_eq (by ring))
  rw [hIP.2,hI0.2,←mul_sub,abs_mul,abs_of_nonneg (sq_nonneg g)]
  exact (mul_le_mul_of_nonneg_left hDiff (sq_nonneg g)).trans_eq (by ring)

end Froehlich
