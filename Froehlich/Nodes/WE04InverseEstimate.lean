import Froehlich.Nodes.WE02

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
    (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

theorem weightedEquation_preconditioned (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    thresholdInverseLinftyMultiplier e he g hg hs hLower
      (weightedEquationOperator e he g hg hs CD hCD hquad P hP f) =
        (1+weightedEquationPerturbation e he g hg hs hLower P hP) f := by
  change thresholdInverseLinftyMultiplier e he g hg hs hLower
      (weightedEquationMultiplier e he g hg hs CD hCD hquad f+
        g^2 • weightedKernelOperator e he g hg hs P hP f) =
      f+g^2 • thresholdInverseLinftyMultiplier e he g hg hs hLower
        (weightedKernelOperator e he g hg hs P hP f)
  rw [map_add,map_smul,weightedEquationMultiplier_inverse_left]

theorem weightedEquation_unpreconditioned (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    weightedEquationMultiplier e he g hg hs CD hCD hquad
      ((1+weightedEquationPerturbation e he g hg hs hLower P hP) f) =
        weightedEquationOperator e he g hg hs CD hCD hquad P hP f := by
  change weightedEquationMultiplier e he g hg hs CD hCD hquad
      (f+g^2 • thresholdInverseLinftyMultiplier e he g hg hs hLower
        (weightedKernelOperator e he g hg hs P hP f)) =
      weightedEquationMultiplier e he g hg hs CD hCD hquad f+
        g^2 • weightedKernelOperator e he g hg hs P hP f
  rw [map_add,map_smul,weightedEquationMultiplier_inverse_right]

variable (hSmall : ‖weightedEquationPerturbation e he g hg hs hLower P hP‖ ≤ 1/2)

include hSmall in
theorem weightedEquationSolutionMap_left (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    weightedEquationSolutionMap e he g hg hs hLower P hP
      (weightedEquationOperator e he g hg hs CD hCD hquad P hP f) = f := by
  let N := weightedEquationNormalizedInverse e he g hg hs hLower P hP
  have h := congrArg (fun A : Lp ℝ ⊤ (volume : Measure GW.Space) →L[ℝ] Lp ℝ ⊤ (volume : Measure GW.Space) => A f)
    (weightedEquationNormalizedInverse_spec e he g hg hs hLower P hP hSmall).1
  have hN : N ((1+weightedEquationPerturbation e he g hg hs hLower P hP) f) = f := by
    simpa only [mul_apply_eq_comp,one_apply_eq_self] using h
  change N (thresholdInverseLinftyMultiplier e he g hg hs hLower
    (weightedEquationOperator e he g hg hs CD hCD hquad P hP f)) = f
  rw [weightedEquation_preconditioned]
  exact hN

include hSmall in
theorem weightedEquationSolutionMap_right (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    weightedEquationOperator e he g hg hs CD hCD hquad P hP
      (weightedEquationSolutionMap e he g hg hs hLower P hP f) = f := by
  let N := weightedEquationNormalizedInverse e he g hg hs hLower P hP
  let I := thresholdInverseLinftyMultiplier e he g hg hs hLower
  let M := weightedEquationMultiplier e he g hg hs CD hCD hquad
  have h := congrArg (fun A : Lp ℝ ⊤ (volume : Measure GW.Space) →L[ℝ] Lp ℝ ⊤ (volume : Measure GW.Space) => A (I f))
    (weightedEquationNormalizedInverse_spec e he g hg hs hLower P hP hSmall).2.1
  have hN : (1+weightedEquationPerturbation e he g hg hs hLower P hP) (N (I f)) = I f := by
    simpa only [mul_apply_eq_comp,one_apply_eq_self] using h
  have hM : M ((1+weightedEquationPerturbation e he g hg hs hLower P hP) (N (I f))) = f :=
    (congrArg M hN).trans (weightedEquationMultiplier_inverse_right e he g hg hs hLower CD hCD hquad f)
  exact (weightedEquation_unpreconditioned e he g hg hs hLower CD hCD hquad P hP (N (I f))).symm.trans hM

include hSmall in
/-- The original equation has inverse bound 8/3, distinct from the normalized bound 2. -/
theorem weightedEquation_aPriori_norm (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    ‖f‖ ≤ (8/3 : ℝ)*‖weightedEquationOperator e he g hg hs CD hCD hquad P hP f‖ := by
  have hleft := weightedEquationSolutionMap_left e he g hg hs hLower CD hCD hquad P hP hSmall f
  calc
    ‖f‖ = ‖weightedEquationSolutionMap e he g hg hs hLower P hP
        (weightedEquationOperator e he g hg hs CD hCD hquad P hP f)‖ := congrArg norm hleft.symm
    _ ≤ ‖weightedEquationSolutionMap e he g hg hs hLower P hP‖*
        ‖weightedEquationOperator e he g hg hs CD hCD hquad P hP f‖ :=
      (weightedEquationSolutionMap e he g hg hs hLower P hP).le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (weightedEquationSolutionMap_norm_le e he g hg hs hLower P hP hSmall) (norm_nonneg _)

end Froehlich
