import Froehlich.Nodes.WE06InverseIntegrals
import Froehlich.Nodes.WE04

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

/-- The sharp weighted solution estimate compensates the moving infrared singularity. -/
theorem thresholdScalarU_uniform : ∃ CU : ℝ, 0 < CU ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
      (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
      (CD : ℝ) (hCD : 0 ≤ CD)
      (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2),
      ‖weightedEquationPerturbation e he g hg hs hLower 0 (by simp)‖ ≤ 1/2 →
      ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
      ‖weightedEquationPerturbation e he g hg hs hLower P hP‖ ≤ 1/2 →
      ‖thresholdBoundedOperator e he g hg hs CD hCD hquad P hP-1‖ ≤ 1/2 →
      ∀ hP0 : P ≠ 0,
      ‖thresholdScalarU e he g hg hs CD hCD hquad P hP hP0‖ ≤ CU*g^2 := by
  obtain ⟨CE,hCE,hEta⟩ := weightedEquationEta_comparison_uniform
  obtain ⟨CI,hCI,hWeighted,_⟩ := moving_singularity_estimates
  refine ⟨CE*CI,mul_pos hCE hCI,?_⟩
  intro e he g hg hs hLower CD hCD hquad hSmall0 P hP hSmallP hNP hP0
  let eta := weightedEquationEta e he g hg hs hLower P hP
  have hdom : ∀ᵐ q ∂volume, ‖eta q*muDensity P q‖ ≤ CE*weightedMuDensity P q := by
    filter_upwards [hEta e he g hg hs hLower CD hCD hquad hSmall0 P hP hSmallP] with q hq
    have h := mul_le_mul_of_nonneg_right hq.2 (muDensity_nonneg P q)
    simpa only [eta,Real.norm_eq_abs,abs_mul,abs_of_nonneg (muDensity_nonneg P q),
      weightedMuDensity,mul_assoc] using h
  have hn := norm_integral_le_of_norm_le (((hWeighted P hP).1.1).const_mul CE) hdom
  have hInt : |∫ q : GW.Space,eta q*muDensity P q| ≤ CE*CI := by
    have h : |∫ q : GW.Space,eta q*muDensity P q| ≤ CE*(∫ q : GW.Space,weightedMuDensity P q) := by
      simpa only [Real.norm_eq_abs,integral_const_mul] using hn
    exact h.trans (mul_le_mul_of_nonneg_left (hWeighted P hP).1.2 hCE.le)
  rw [(thresholdScalarU_integral e he g hg hs hLower CD hCD hquad P hP hSmallP hNP hP0).2,
    Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg g)]
  exact (mul_le_mul_of_nonneg_left hInt (sq_nonneg g)).trans_eq (by ring)

end Froehlich
