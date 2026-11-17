import Froehlich.Nodes.WE01
import Froehlich.Nodes.BA02

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

/-- The source's actual normalized perturbation on ordinary real L-infinity. -/
def weightedEquationPerturbation :
    Lp ℝ ⊤ (volume : Measure GW.Space) →L[ℝ] Lp ℝ ⊤ (volume : Measure GW.Space) :=
  (g^2) • (thresholdInverseLinftyMultiplier e he g hg hs hLower).comp
    (weightedKernelOperator e he g hg hs P hP)

def weightedEquationNormalizedInverse :
    Lp ℝ ⊤ (volume : Measure GW.Space) →L[ℝ] Lp ℝ ⊤ (volume : Measure GW.Space) :=
  neumannInverse (-(weightedEquationPerturbation e he g hg hs hLower P hP))

variable (hSmall : ‖weightedEquationPerturbation e he g hg hs hLower P hP‖ ≤ 1/2)

include hSmall in
theorem weightedEquationNormalizedInverse_spec :
    weightedEquationNormalizedInverse e he g hg hs hLower P hP *
      (1+weightedEquationPerturbation e he g hg hs hLower P hP) = 1 ∧
    (1+weightedEquationPerturbation e he g hg hs hLower P hP) *
      weightedEquationNormalizedInverse e he g hg hs hLower P hP = 1 ∧
    ‖weightedEquationNormalizedInverse e he g hg hs hLower P hP‖ ≤ 2 := by
  let T := weightedEquationPerturbation e he g hg hs hLower P hP
  have hn : ‖-T‖ ≤ (1/2 : ℝ) := (ContinuousLinearMap.opNorm_neg T).trans_le hSmall
  have ht : ‖-T‖ < 1 := hn.trans_lt (by norm_num)
  have hl := neumannInverse_left (-T) ht
  have hr := neumannInverse_right (-T) ht
  have hb := neumannInverse_norm_le (-T) hn (by norm_num : (1/2 : ℝ) < 1)
  refine ⟨?_,?_,?_⟩
  · simpa only [weightedEquationNormalizedInverse,T,sub_neg_eq_add] using hl
  · simpa only [weightedEquationNormalizedInverse,T,sub_neg_eq_add] using hr
  · simpa only [weightedEquationNormalizedInverse,T,show (1-(1/2 : ℝ))⁻¹=2 by norm_num] using hb

/-- The solution map includes multiplication of the source by m inverse.
Its bound is 8/3, distinct from the normalized inverse's bound 2. -/
def weightedEquationSolutionMap :
    Lp ℝ ⊤ (volume : Measure GW.Space) →L[ℝ] Lp ℝ ⊤ (volume : Measure GW.Space) :=
  (weightedEquationNormalizedInverse e he g hg hs hLower P hP).comp
    (thresholdInverseLinftyMultiplier e he g hg hs hLower)

include hSmall in
theorem weightedEquationSolutionMap_norm_le :
    ‖weightedEquationSolutionMap e he g hg hs hLower P hP‖ ≤ (8/3 : ℝ) := by
  have hN := (weightedEquationNormalizedInverse_spec e he g hg hs hLower P hP hSmall).2.2
  have hM := thresholdInverseLinftyMultiplier_norm_le e he g hg hs hLower
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hN hM (ContinuousLinearMap.opNorm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by norm_num))

def weightedEquationSolution : Lp ℝ ⊤ (volume : Measure GW.Space) :=
  weightedEquationSolutionMap e he g hg hs hLower P hP (weightedKernelSource e he g hg hs P hP)

include hSmall in
theorem weightedEquationSolution_normalized :
    (1+weightedEquationPerturbation e he g hg hs hLower P hP)
      (weightedEquationSolution e he g hg hs hLower P hP) =
      thresholdInverseLinftyMultiplier e he g hg hs hLower (weightedKernelSource e he g hg hs P hP) := by
  have h := congrArg (fun A : Lp ℝ ⊤ (volume : Measure GW.Space) →L[ℝ] Lp ℝ ⊤ (volume : Measure GW.Space) =>
      A (thresholdInverseLinftyMultiplier e he g hg hs hLower (weightedKernelSource e he g hg hs P hP)))
    (weightedEquationNormalizedInverse_spec e he g hg hs hLower P hP hSmall).2.1
  simpa only [weightedEquationSolution,weightedEquationSolutionMap,ContinuousLinearMap.comp_apply,
    mul_apply_eq_comp,ContinuousLinearMap.one_apply] using h

end Froehlich
