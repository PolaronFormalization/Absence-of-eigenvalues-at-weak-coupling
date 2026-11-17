import Froehlich.Nodes.WE04NormalizedDifference
import Froehlich.Nodes.WE04InverseEstimate

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
    (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4)
    (hSmall0 : ‖weightedEquationPerturbation e he g hg hs hLower 0 (by simp)‖ ≤ 1/2)
    (hSmallP : ‖weightedEquationPerturbation e he g hg hs hLower P hP‖ ≤ 1/2)

include hSmall0 hSmallP in
theorem weightedEquation_residual_difference :
    weightedEquationOperator e he g hg hs CD hCD hquad P hP
      (weightedEquationSolution e he g hg hs hLower P hP-
        weightedEquationSolution e he g hg hs hLower 0 (by simp)) =
      weightedKernelSource e he g hg hs P hP-weightedKernelSource e he g hg hs 0 (by simp)-
      g^2 • (weightedKernelOperator e he g hg hs P hP
        (weightedEquationSolution e he g hg hs hLower 0 (by simp))-
        weightedKernelOperator e he g hg hs 0 (by simp)
          (weightedEquationSolution e he g hg hs hLower 0 (by simp))) := by
  let z0 := weightedEquationSolution e he g hg hs hLower 0 (by simp)
  let M := weightedEquationMultiplier e he g hg hs CD hCD hquad
  let LP := weightedKernelOperator e he g hg hs P hP
  let L0 := weightedKernelOperator e he g hg hs 0 (by simp)
  have h0 := weightedEquationSolution_equation e he g hg hs hLower CD hCD hquad 0 (by simp) hSmall0
  have hP' := weightedEquationSolution_equation e he g hg hs hLower CD hCD hquad P hP hSmallP
  have hAction : weightedEquationOperator e he g hg hs CD hCD hquad P hP z0 =
      weightedKernelSource e he g hg hs 0 (by simp)+g^2 • (LP z0-L0 z0) := by
    change M z0+g^2 • LP z0 = _
    change M z0+g^2 • L0 z0 = _ at h0
    calc
      _ = (M z0+g^2 • L0 z0)+g^2 • (LP z0-L0 z0) := by rw [smul_sub]; abel
      _ = _ := by rw [h0]
  rw [map_sub,hP',hAction]
  abel

/-- The inverse is applied only after bounding the residual on the actual
zero-momentum solution; no norm continuity of the whole kernel is used. -/
theorem weightedEquationSolution_comparison_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
      (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
      (CD : ℝ) (hCD : 0 ≤ CD)
      (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2),
      ‖weightedEquationPerturbation e he g hg hs hLower 0 (by simp)‖ ≤ 1/2 →
      ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
      ‖weightedEquationPerturbation e he g hg hs hLower P hP‖ ≤ 1/2 →
      ‖weightedEquationSolution e he g hg hs hLower P hP-
        weightedEquationSolution e he g hg hs hLower 0 (by simp)‖ ≤ C*‖P‖ := by
  obtain ⟨A,hA,hChi⟩ := weightedKernelSource_difference_uniform
  obtain ⟨B,hB,hKernel⟩ := weightedKernelOperator_specific_difference_uniform
  refine ⟨(8/3 : ℝ)*(A+B),by positivity,?_⟩
  intro e he g hg hs hLower CD hCD hquad hSmall0 P hP hSmallP
  let z0 := weightedEquationSolution e he g hg hs hLower 0 (by simp)
  let zP := weightedEquationSolution e he g hg hs hLower P hP
  let d := weightedKernelOperator e he g hg hs P hP z0-
    weightedKernelOperator e he g hg hs 0 (by simp) z0
  have hd : ‖d‖ ≤ B*‖P‖ := hKernel e he g hg hs hLower CD hCD hquad hSmall0 P hP
  have hgSq : g^2 ≤ (1 : ℝ) := by nlinarith [abs_nonneg g,sq_abs g]
  have hgTerm : ‖g^2 • d‖ ≤ B*‖P‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg g)]
    have h := mul_le_mul hgSq hd (norm_nonneg d) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using h
  have hResidual : ‖weightedEquationOperator e he g hg hs CD hCD hquad P hP (zP-z0)‖ ≤
      (A+B)*‖P‖ := by
    rw [weightedEquation_residual_difference e he g hg hs hLower CD hCD hquad P hP hSmall0 hSmallP]
    have h := (norm_sub_le (weightedKernelSource e he g hg hs P hP-
      weightedKernelSource e he g hg hs 0 (by simp)) (g^2 • d)).trans
      (add_le_add (hChi e he g hg hs P hP) hgTerm)
    exact h.trans_eq (by ring)
  have h := weightedEquation_aPriori_norm e he g hg hs hLower CD hCD hquad P hP hSmallP (zP-z0)
  exact h.trans ((mul_le_mul_of_nonneg_left hResidual (by norm_num : (0 : ℝ) ≤ 8/3)).trans_eq (by ring))

end Froehlich
