import Froehlich.Nodes.WE06SourceIntegral
import Froehlich.Nodes.WE06HilbertSourceIntegral

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
    (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4)
    (hSmall : ‖weightedEquationPerturbation e he g hg hs hLower P hP‖ ≤ 1/2)
    (hN : ‖thresholdBoundedOperator e he g hg hs CD hCD hquad P hP-1‖ ≤ 1/2)

include hSmall hN in
theorem we06_actual_inverse_response :
    weightedEquationHilbertVector e he g hg hs hLower P hP =
      thresholdBoundedInverse e he g hg hs CD hCD hquad P hP
        (thresholdKernelSourceVector e he g hg hs P hP) := by
  exact weightedHilbertVector_eq_inverse e he g hg hs CD hCD hquad P hP
    (weightedEquationEta e he g hg hs hLower P hP)
    (weightedEquationEta_aestronglyMeasurable e he g hg hs hLower P hP)
    ‖weightedEquationSolution e he g hg hs hLower P hP‖ (norm_nonneg _)
    (weightedEquationEta_bound e he g hg hs hLower P hP)
    (weightedEquationEta_equation_ae e he g hg hs hLower P hP CD hCD hquad hSmall) hN

include hSmall hN in
/-- The actual N formula, including P=0 and g=0, with a genuinely absolute integral. -/
theorem thresholdScalarN_integral :
    Integrable (fun q : GW.Space => kernelPsi e he g hg hs P q*
      weightedEquationEta e he g hg hs hLower P hP q*muDensity P q) volume ∧
    thresholdScalarN e he g hg hs CD hCD hquad P hP =
      g^2*(∫ q : GW.Space,kernelPsi e he g hg hs P q*
        weightedEquationEta e he g hg hs hLower P hP q*muDensity P q) := by
  have hi := we06_source_product_integrable e he g hg hs P hP
    (weightedEquationEta e he g hg hs hLower P hP)
    (weightedEquationEta_aestronglyMeasurable e he g hg hs hLower P hP)
    ‖weightedEquationSolution e he g hg hs hLower P hP‖ (norm_nonneg _)
    (weightedEquationEta_bound e he g hg hs hLower P hP)
  have hp := weightedHilbertVector_source_inner_integral e he g hg hs P hP
    (weightedEquationEta e he g hg hs hLower P hP)
    (weightedEquationEta_aestronglyMeasurable e he g hg hs hLower P hP)
    ‖weightedEquationSolution e he g hg hs hLower P hP‖ (norm_nonneg _)
    (weightedEquationEta_bound e he g hg hs hLower P hP)
  change ⟪thresholdKernelSourceVector e he g hg hs P hP,
    weightedEquationHilbertVector e he g hg hs hLower P hP⟫_ℂ = _ at hp
  rw [we06_actual_inverse_response e he g hg hs hLower CD hCD hquad P hP hSmall hN] at hp
  refine ⟨hi,?_⟩
  exact congrArg Complex.re hp

include hSmall hN in
/-- The actual U formula uses tP only at nonzero P; no division by g is used. -/
theorem thresholdScalarU_integral (hP0 : P ≠ 0) :
    Integrable (fun q : GW.Space => weightedEquationEta e he g hg hs hLower P hP q*muDensity P q) volume ∧
    thresholdScalarU e he g hg hs CD hCD hquad P hP hP0 =
      ((g^2*(∫ q : GW.Space,weightedEquationEta e he g hg hs hLower P hP q*muDensity P q) : ℝ) : ℂ) := by
  have hi := we06_eta_mu_integrable P hP0
    (weightedEquationEta e he g hg hs hLower P hP)
    (weightedEquationEta_aestronglyMeasurable e he g hg hs hLower P hP)
    ‖weightedEquationSolution e he g hg hs hLower P hP‖ (norm_nonneg _)
    (weightedEquationEta_bound e he g hg hs hLower P hP)
  have hp := weightedHilbertVector_hilbertSource_inner_integral g P hP hP0
    (weightedEquationEta e he g hg hs hLower P hP)
    (weightedEquationEta_aestronglyMeasurable e he g hg hs hLower P hP)
    ‖weightedEquationSolution e he g hg hs hLower P hP‖ (norm_nonneg _)
    (weightedEquationEta_bound e he g hg hs hLower P hP)
  change ⟪weightedEquationHilbertVector e he g hg hs hLower P hP,
    translatedHilbertSource g P hP0⟫_ℂ = _ at hp
  rw [we06_actual_inverse_response e he g hg hs hLower CD hCD hquad P hP hSmall hN] at hp
  have hAdj := (thresholdBoundedInverse e he g hg hs CD hCD hquad P hP).adjoint_inner_left
    (translatedHilbertSource g P hP0) (thresholdKernelSourceVector e he g hg hs P hP)
  rw [thresholdBoundedInverse_selfadjoint e he g hg hs CD hCD hquad P hP hN] at hAdj
  exact ⟨hi,hAdj.symm.trans hp⟩

include hSmall hN in
theorem thresholdScalarU_real (hP0 : P ≠ 0) :
    (starRingEnd ℂ) (thresholdScalarU e he g hg hs CD hCD hquad P hP hP0) =
      thresholdScalarU e he g hg hs CD hCD hquad P hP hP0 := by
  rw [(thresholdScalarU_integral e he g hg hs hLower CD hCD hquad P hP hSmall hN hP0).2]
  exact Complex.conj_ofReal _

end Froehlich
