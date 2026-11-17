import Froehlich.Nodes.WE05Identification
import Froehlich.Nodes.WE02

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

/-- The actual Hilbert vector from WE02's ordinary L-infinity solution. -/
def weightedEquationHilbertVector : GW.OnePhonon :=
  weightedHilbertVector g P hP (weightedEquationEta e he g hg hs hLower P hP)
    (weightedEquationEta_aestronglyMeasurable e he g hg hs hLower P hP)
    ‖weightedEquationSolution e he g hg hs hLower P hP‖
    (weightedEquationEta_bound e he g hg hs hLower P hP)

theorem weightedEquationHilbertVector_ae :
    weightedEquationHilbertVector e he g hg hs hLower P hP =ᵐ[volume]
      weightedHilbertCoefficient g P (weightedEquationEta e he g hg hs hLower P hP) :=
  weightedHilbertVector_ae _ _ _ _ _ _ _

variable (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)

def WE05FixedReference : Prop :=
  ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
    (weightedEquationHilbertVector e he g hg hs hLower P hP =ᵐ[volume]
      weightedHilbertCoefficient g P (weightedEquationEtaPrime e he g hg hs P hLower hP)) ∧
    thresholdBoundedOperator e he g hg hs CD hCD hquad P hP
      (weightedEquationHilbertVector e he g hg hs hLower P hP) =
        thresholdKernelSourceVector e he g hg hs P hP ∧
    weightedEquationHilbertVector e he g hg hs hLower P hP =
      thresholdBoundedInverse e he g hg hs CD hCD hquad P hP
        (thresholdKernelSourceVector e he g hg hs P hP) ∧
    ∀ q : GW.Space,
      Integrable (fun r => boundedThresholdKernel e he g hg hs P q r*
        weightedEquationHilbertVector e he g hg hs hLower P hP r) volume ∧
      Integrable (fun r => remainderKernel e he g hg hs P q r*muDensity P r*
        weightedEquationEta e he g hg hs hLower P hP r) volume

theorem finalWE05 : ∃ C CD s : ℝ, 0 < C ∧ 0 < CD ∧ 0 < s ∧
    ∀ g : ℝ, |g| < s →
      ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
      ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
      ∃ hCD : 0 ≤ CD,
      ∃ hquad : ∀ q : GW.Space,
        |auxiliarySelfEnergy (groundEnergy (fiberHamiltonian g 0)) q he g hg hs-
          groundEnergy (fiberHamiltonian g 0)| ≤ CD*g^2*‖q‖^2,
      ∃ hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier
        (groundEnergy (fiberHamiltonian g 0)) he g hg hs q,
      WE02FixedReference C CD (groundEnergy (fiberHamiltonian g 0)) he g hg hs hCD hquad hLower ∧
      WE05FixedReference (groundEnergy (fiberHamiltonian g 0)) he g hg hs hLower CD hCD hquad := by
  obtain ⟨C,CD,s,hC,hCD,hs,hGround⟩ := finalWE02
  obtain ⟨CK,hCK,hDist⟩ := thresholdBoundedOperator_distance_uniform
  obtain ⟨a,ha,haD⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1/2) (CD+CK)
  refine ⟨C,CD,min s a,hC,hCD,lt_min hs ha,?_⟩
  intro g hgs
  obtain ⟨he,hg,haux,hCD0,hquad,hLower,hRef⟩ := hGround g (hgs.trans_le (min_le_left _ _))
  refine ⟨he,hg,haux,hCD0,hquad,hLower,hRef,?_⟩
  intro P hP
  have hSmall := (hRef P hP).1
  have hgSq : g^2 ≤ |g| := by nlinarith [abs_nonneg g,sq_abs g]
  have hTiny : (CD+CK)*g^2 ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hgSq (add_pos hCD hCK).le).trans
      ((mul_le_mul_of_nonneg_left (hgs.trans_le (min_le_right _ _)).le
        (add_pos hCD hCK).le).trans haD.le)
  have hN := (hDist _ he g hg haux CD hCD0 hquad P hP).trans hTiny
  let eta := weightedEquationEta _ he g hg haux hLower P hP
  have hEta := weightedEquationEta_aestronglyMeasurable _ he g hg haux hLower P hP
  have hBound := weightedEquationEta_bound _ he g hg haux hLower P hP
  have hEq := weightedEquationEta_equation_ae _ he g hg haux hLower P hP CD hCD0 hquad hSmall
  have hM := norm_nonneg (weightedEquationSolution _ he g hg haux hLower P hP)
  refine ⟨?_,?_,?_,?_⟩
  · filter_upwards [weightedEquationHilbertVector_ae _ he g hg haux hLower P hP,
      weightedEquationEtaPrime_ae _ he g hg haux P hLower hP CD hCD0 hquad hSmall] with q hx hp
    rw [hx]
    unfold weightedHilbertCoefficient
    rw [hp]
  · exact weightedHilbertVector_boundedOperator _ he g hg haux CD hCD0 hquad P hP
      eta hEta _ hM hBound hEq
  · exact weightedHilbertVector_eq_inverse _ he g hg haux CD hCD0 hquad P hP
      eta hEta _ hM hBound hEq hN
  · intro q
    have hRows := weightedHilbertVector_kernel_row _ he g hg haux P hP eta hEta _ hM hBound q
    exact ⟨hRows.1,hRows.2.1⟩

end Froehlich
