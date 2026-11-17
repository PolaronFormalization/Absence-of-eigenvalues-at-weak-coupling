import Froehlich.Nodes.WE06UBound
import Froehlich.Nodes.WE06NComparison
import Froehlich.Nodes.WE06TBound

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

/-- Actual scalar formulas and all three source estimates; t occurs only at nonzero P. -/
def WE06FixedReference (CU CT CN CD e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
    (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2) : Prop :=
  (∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
    ‖thresholdBoundedOperator e he g hg hs CD hCD hquad P hP-1‖ ≤ 1/2) ∧
  (∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
    (thresholdScalarN e he g hg hs CD hCD hquad P hP : ℂ) =
      ⟪thresholdKernelSourceVector e he g hg hs P hP,
        thresholdBoundedInverse e he g hg hs CD hCD hquad P hP
          (thresholdKernelSourceVector e he g hg hs P hP)⟫_ℂ ∧
    Integrable (fun q : GW.Space => kernelPsi e he g hg hs P q*
      weightedEquationEta e he g hg hs hLower P hP q*muDensity P q) volume ∧
    thresholdScalarN e he g hg hs CD hCD hquad P hP =
      g^2*(∫ q : GW.Space,kernelPsi e he g hg hs P q*
        weightedEquationEta e he g hg hs hLower P hP q*muDensity P q)) ∧
  (∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
    |thresholdScalarN e he g hg hs CD hCD hquad P hP-
      thresholdScalarN e he g hg hs CD hCD hquad 0 (by simp)| ≤ CN*g^2*‖P‖) ∧
  ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4) (hP0 : P ≠ 0),
    (Integrable (fun q : GW.Space => weightedEquationEta e he g hg hs hLower P hP q*muDensity P q) volume ∧
      thresholdScalarU e he g hg hs CD hCD hquad P hP hP0 =
        ((g^2*(∫ q : GW.Space,weightedEquationEta e he g hg hs hLower P hP q*muDensity P q) : ℝ) : ℂ)) ∧
    (starRingEnd ℂ) (thresholdScalarU e he g hg hs CD hCD hquad P hP hP0) =
      thresholdScalarU e he g hg hs CD hCD hquad P hP hP0 ∧
    ‖thresholdScalarU e he g hg hs CD hCD hquad P hP hP0‖ ≤ CU*g^2 ∧
    (thresholdScalarT e he g hg hs CD hCD hquad P hP hP0 : ℂ) =
      ⟪translatedHilbertSource g P hP0,
        thresholdBoundedInverse e he g hg hs CD hCD hquad P hP (translatedHilbertSource g P hP0)⟫_ℂ ∧
    0 ≤ thresholdScalarT e he g hg hs CD hCD hquad P hP hP0 ∧
    thresholdScalarT e he g hg hs CD hCD hquad P hP hP0 ≤ CT*g^2/‖P‖

/-- Uniform constants are selected before all signed couplings and closed-quarter momenta. -/
theorem finalWE06 : ∃ CU CT CN C CD s : ℝ,
    0 < CU ∧ 0 < CT ∧ 0 < CN ∧ 0 < C ∧ 0 < CD ∧ 0 < s ∧
    ∀ g : ℝ, |g| < s →
      ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
      ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
      ∃ hCD : 0 ≤ CD,
      ∃ hquad : ∀ q : GW.Space,
        |auxiliarySelfEnergy (groundEnergy (fiberHamiltonian g 0)) q he g hg hs-groundEnergy (fiberHamiltonian g 0)| ≤ CD*g^2*‖q‖^2,
      ∃ hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier (groundEnergy (fiberHamiltonian g 0)) he g hg hs q,
      WE02FixedReference C CD (groundEnergy (fiberHamiltonian g 0)) he g hg hs hCD hquad hLower ∧
      WE06FixedReference CU CT CN CD (groundEnergy (fiberHamiltonian g 0)) he g hg hs hLower hCD hquad := by
  obtain ⟨CU,hCU,hU⟩ := thresholdScalarU_uniform
  obtain ⟨CT,hCT,hT⟩ := thresholdScalarT_uniform
  obtain ⟨CN,hCN,hNCompare⟩ := thresholdScalarN_comparison_uniform
  obtain ⟨C,CD,sW,hC,hCD,hsW,hGround⟩ := finalWE05
  obtain ⟨CK,hCK,hDist⟩ := thresholdBoundedOperator_distance_uniform
  obtain ⟨a,ha,haD⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1/2) (CD+CK)
  refine ⟨CU,CT,CN,C,CD,min sW a,hCU,hCT,hCN,hC,hCD,lt_min hsW ha,?_⟩
  intro g hgs
  obtain ⟨he,hg,haux,hCD0,hquad,hLower,hRef,_⟩ := hGround g (hgs.trans_le (min_le_left _ _))
  have hsq : g^2 ≤ |g| := by nlinarith [abs_nonneg g,sq_abs g]
  have hTiny : (CD+CK)*g^2 ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hsq (add_pos hCD hCK).le).trans
      ((mul_le_mul_of_nonneg_left (hgs.trans_le (min_le_right _ _)).le (add_pos hCD hCK).le).trans haD.le)
  have hN (P : GW.Space) (hP : ‖P‖ ≤ 1/4) :
      ‖thresholdBoundedOperator _ he g hg haux CD hCD0 hquad P hP-1‖ ≤ 1/2 :=
    (hDist _ he g hg haux CD hCD0 hquad P hP).trans hTiny
  have hSmall0 := (hRef 0 (by simp)).1
  refine ⟨he,hg,haux,hCD0,hquad,hLower,hRef,hN,?_,?_,?_⟩
  · intro P hP
    exact ⟨thresholdScalarN_ofReal _ he g hg haux CD hCD0 hquad P hP (hN P hP),
      thresholdScalarN_integral _ he g hg haux hLower CD hCD0 hquad P hP (hRef P hP).1 (hN P hP)⟩
  · intro P hP
    exact hNCompare _ he g hg haux hLower CD hCD0 hquad hSmall0 (hN 0 (by simp)) P hP
      (hRef P hP).1 (hN P hP)
  · intro P hP hP0
    exact ⟨thresholdScalarU_integral _ he g hg haux hLower CD hCD0 hquad P hP (hRef P hP).1 (hN P hP) hP0,
      thresholdScalarU_real _ he g hg haux hLower CD hCD0 hquad P hP (hRef P hP).1 (hN P hP) hP0,
      hU _ he g hg haux hLower CD hCD0 hquad hSmall0 P hP (hRef P hP).1 (hN P hP) hP0,
      thresholdScalarT_ofReal _ he g hg haux CD hCD0 hquad P hP (hN P hP) hP0,
      hT _ he g hg haux CD hCD0 hquad P hP (hN P hP) hP0⟩

end Froehlich
