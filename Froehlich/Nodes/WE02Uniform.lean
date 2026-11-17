import Froehlich.Nodes.WE02Neumann
import Froehlich.Nodes.OP01

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Froehlich

theorem weightedEquationPerturbation_norm_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
      (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
      (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
      ‖weightedEquationPerturbation e he g hg hs hLower P hP‖ ≤ C*g^2 := by
  obtain ⟨A,hA,hOp⟩ := weightedKernelOperator_norm_uniform
  refine ⟨(4/3 : ℝ)*A,by positivity,?_⟩
  intro e he g hg hs hLower P hP
  have hN := ContinuousLinearMap.opNorm_comp_le
    (thresholdInverseLinftyMultiplier e he g hg hs hLower) (weightedKernelOperator e he g hg hs P hP)
  have hNM : ‖(thresholdInverseLinftyMultiplier e he g hg hs hLower).comp
      (weightedKernelOperator e he g hg hs P hP)‖ ≤ (4/3 : ℝ)*A := hN.trans
    (mul_le_mul (thresholdInverseLinftyMultiplier_norm_le e he g hg hs hLower)
      (hOp e he g hg hs P hP) (ContinuousLinearMap.opNorm_nonneg _) (by norm_num))
  have h := ContinuousLinearMap.opNorm_smul_le (g^2)
    ((thresholdInverseLinftyMultiplier e he g hg hs hLower).comp (weightedKernelOperator e he g hg hs P hP))
  have h' := h.trans (mul_le_mul_of_nonneg_left hNM (norm_nonneg (g^2)))
  simpa only [weightedEquationPerturbation,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg g),mul_comm] using h'

theorem weightedEquationSolution_norm_uniform : ∃ CZ : ℝ, 0 < CZ ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
      (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
      (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
      ‖weightedEquationPerturbation e he g hg hs hLower P hP‖ ≤ 1/2 →
      ‖weightedEquationSolution e he g hg hs hLower P hP‖ ≤ CZ := by
  obtain ⟨B,hB,hSource⟩ := weightedKernelSource_norm_uniform
  refine ⟨(8/3 : ℝ)*B,by positivity,?_⟩
  intro e he g hg hs hLower P hP hSmall
  exact ((weightedEquationSolutionMap e he g hg hs hLower P hP).le_opNorm
    (weightedKernelSource e he g hg hs P hP)).trans
    (mul_le_mul (weightedEquationSolutionMap_norm_le e he g hg hs hLower P hP hSmall)
      (hSource e he g hg hs P hP) (norm_nonneg _) (by norm_num))

/-- Actual OP01 ground data and perturbative smallness are constructed
uniformly before coupling and all closed-quarter momenta. -/
theorem weightedEquation_ground_smallness : ∃ CZ CD s : ℝ, 0 < CZ ∧ 0 < CD ∧ 0 < s ∧
    ∀ g : ℝ, |g| < s →
      ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
      ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
      ∃ hCD : 0 ≤ CD,
      ∃ hquad : ∀ q : GW.Space,
        |auxiliarySelfEnergy (groundEnergy (fiberHamiltonian g 0)) q he g hg hs-groundEnergy (fiberHamiltonian g 0)| ≤
          CD*g^2*‖q‖^2,
      ∃ hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier
        (groundEnergy (fiberHamiltonian g 0)) he g hg hs q,
      ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
        ‖weightedEquationPerturbation (groundEnergy (fiberHamiltonian g 0)) he g hg hs hLower P hP‖ ≤ 1/2 ∧
        ‖weightedEquationSolution (groundEnergy (fiberHamiltonian g 0)) he g hg hs hLower P hP‖ ≤ CZ := by
  obtain ⟨C,hC,hT⟩ := weightedEquationPerturbation_norm_uniform
  obtain ⟨CZ,hCZ,hZ⟩ := weightedEquationSolution_norm_uniform
  obtain ⟨CO,CD,sO,hCO,hCD,hsO,hGround⟩ := finalOP01
  obtain ⟨a,ha,haC⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1/2) C
  refine ⟨CZ,CD,min sO a,hCZ,hCD,lt_min hsO ha,?_⟩
  intro g hgs
  obtain ⟨he,hg,haux,hCD0,hquad,hOP⟩ := hGround g (hgs.trans_le (min_le_left _ _))
  have hLower := hOP.2.2.2.2.1
  refine ⟨he,hg,haux,hCD0,hquad,hLower,?_⟩
  have hsq : g^2 ≤ |g| := by nlinarith [abs_nonneg g,sq_abs g]
  have hSmall : C*g^2 ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hsq hC.le).trans
      ((mul_le_mul_of_nonneg_left (hgs.trans_le (min_le_right _ _)).le hC.le).trans haC.le)
  intro P hP
  have ht := (hT _ he g hg haux hLower P hP).trans hSmall
  exact ⟨ht,hZ _ he g hg haux hLower P hP ht⟩

end Froehlich
