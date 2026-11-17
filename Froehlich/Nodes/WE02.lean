import Froehlich.Nodes.WE02PointwiseBound

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

/-- The actual quotient solution and its integral-defined representative.
All pointwise assertions concern etaPrime, never a chosen Lp representative. -/
def WE02FixedReference (C CD e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q) : Prop :=
  ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
    ‖weightedEquationPerturbation e he g hg hs hLower P hP‖ ≤ 1/2 ∧
    (weightedEquationNormalizedInverse e he g hg hs hLower P hP *
      (1+weightedEquationPerturbation e he g hg hs hLower P hP) = 1) ∧
    ((1+weightedEquationPerturbation e he g hg hs hLower P hP) *
      weightedEquationNormalizedInverse e he g hg hs hLower P hP = 1) ∧
    ‖weightedEquationNormalizedInverse e he g hg hs hLower P hP‖ ≤ 2 ∧
    ‖weightedEquationSolutionMap e he g hg hs hLower P hP‖ ≤ (8/3 : ℝ) ∧
    weightedEquationOperator e he g hg hs CD hCD hquad P hP
      (weightedEquationSolution e he g hg hs hLower P hP) = weightedKernelSource e he g hg hs P hP ∧
    (∀ z : Lp ℝ ⊤ (volume : Measure GW.Space),
      weightedEquationOperator e he g hg hs CD hCD hquad P hP z = weightedKernelSource e he g hg hs P hP →
      z = weightedEquationSolution e he g hg hs hLower P hP) ∧
    ‖weightedEquationSolution e he g hg hs hLower P hP‖ ≤ C ∧
    (∀ᵐ q ∂volume, |weightedEquationEta e he g hg hs hLower P hP q| ≤ C*omega q) ∧
    (∀ᵐ q ∂volume,
      thresholdDiagonalMultiplier e he g hg hs q*weightedEquationEta e he g hg hs hLower P hP q+
        g^2*weightedEtaIntegral e he g hg hs P (weightedEquationEta e he g hg hs hLower P hP) q =
          kernelPsi e he g hg hs P q) ∧
    AEStronglyMeasurable (weightedEquationEtaPrime e he g hg hs P hLower hP) volume ∧
    (weightedEquationEtaPrime e he g hg hs P hLower hP =ᵐ[volume]
      weightedEquationEta e he g hg hs hLower P hP) ∧
    weightedEquationEtaPrime e he g hg hs P hLower hP 0 = 0 ∧
    ∀ q : GW.Space,
      |weightedEquationEtaPrime e he g hg hs P hLower hP q| ≤ C*omega q ∧
      weightedEtaIntegral e he g hg hs P (weightedEquationEtaPrime e he g hg hs P hLower hP) q =
        weightedEtaIntegral e he g hg hs P (weightedEquationEta e he g hg hs hLower P hP) q ∧
      thresholdDiagonalMultiplier e he g hg hs q*weightedEquationEtaPrime e he g hg hs P hLower hP q+
        g^2*weightedEtaIntegral e he g hg hs P (weightedEquationEtaPrime e he g hg hs P hLower hP) q =
          kernelPsi e he g hg hs P q

theorem finalWE02 : ∃ C CD s : ℝ, 0 < C ∧ 0 < CD ∧ 0 < s ∧
    ∀ g : ℝ, |g| < s →
      ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
      ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
      ∃ hCD : 0 ≤ CD,
      ∃ hquad : ∀ q : GW.Space,
        |auxiliarySelfEnergy (groundEnergy (fiberHamiltonian g 0)) q he g hg hs-groundEnergy (fiberHamiltonian g 0)| ≤
          CD*g^2*‖q‖^2,
      ∃ hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier
        (groundEnergy (fiberHamiltonian g 0)) he g hg hs q,
      WE02FixedReference C CD (groundEnergy (fiberHamiltonian g 0)) he g hg hs hCD hquad hLower := by
  obtain ⟨CZ,CD,s,hCZ,hCD,hs,hGround⟩ := weightedEquation_ground_smallness
  obtain ⟨CE,hCE,hPrime⟩ := weightedEquationEtaPrime_bound_uniform
  refine ⟨CZ+CE,CD,s,add_pos hCZ hCE,hCD,hs,?_⟩
  intro g hgs
  obtain ⟨he,hg,haux,hCD0,hquad,hLower,hControl⟩ := hGround g hgs
  refine ⟨he,hg,haux,hCD0,hquad,hLower,?_⟩
  intro P hP
  obtain ⟨hSmall,hZ⟩ := hControl P hP
  have hN := weightedEquationNormalizedInverse_spec _ he g hg haux hLower P hP hSmall
  have hNorm : ‖weightedEquationSolution _ he g hg haux hLower P hP‖ ≤ CZ+CE :=
    hZ.trans (le_add_of_nonneg_right hCE.le)
  have hEta : ∀ᵐ q ∂volume,
      |weightedEquationEta _ he g hg haux hLower P hP q| ≤ (CZ+CE)*omega q := by
    filter_upwards [weightedEquationEta_bound _ he g hg haux hLower P hP] with q hq
    exact hq.trans (mul_le_mul_of_nonneg_right hNorm (omega_nonneg q))
  refine ⟨hSmall,hN.1,hN.2.1,hN.2.2,
    weightedEquationSolutionMap_norm_le _ he g hg haux hLower P hP hSmall,
    weightedEquationSolution_equation _ he g hg haux hLower CD hCD0 hquad P hP hSmall,
    weightedEquationSolution_unique _ he g hg haux hLower CD hCD0 hquad P hP hSmall,
    hNorm,hEta,weightedEquationEta_equation_ae _ he g hg haux hLower P hP CD hCD0 hquad hSmall,
    weightedEquationEtaPrime_aestronglyMeasurable _ he g hg haux P hLower hP,
    weightedEquationEtaPrime_ae _ he g hg haux P hLower hP CD hCD0 hquad hSmall,
    weightedEquationEtaPrime_zero _ he g hg haux P hLower hP,?_⟩
  intro q
  exact ⟨(hPrime _ he g hg haux hLower P hP hSmall q).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCZ.le) (omega_nonneg q)),
    weightedEquationEtaPrime_integral_eq _ he g hg haux P hLower hP CD hCD0 hquad hSmall q,
    weightedEquationEtaPrime_equation _ he g hg haux P hLower hP CD hCD0 hquad hSmall q⟩

end Froehlich
