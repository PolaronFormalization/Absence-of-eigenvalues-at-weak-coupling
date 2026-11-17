import Froehlich.Nodes.WE03Reflection

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
    (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)

theorem weightedEquationMultiplier_reflection (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    weightedEquationMultiplier e he g hg hs CD hCD hquad (realLinftyReflection f) =
      realLinftyReflection (weightedEquationMultiplier e he g hg hs CD hCD hquad f) := by
  have hneg := space_negation_preserving.quasiMeasurePreserving.ae
    (weightedEquationMultiplier_ae e he g hg hs CD hCD hquad f)
  apply Lp.ext
  filter_upwards [weightedEquationMultiplier_ae e he g hg hs CD hCD hquad (realLinftyReflection f),
    realLinftyReflection_ae f,realLinftyReflection_ae (weightedEquationMultiplier e he g hg hs CD hCD hquad f),
    hneg] with q hm hf hr hneg
  rw [hm,hf,hr,hneg,thresholdDiagonalMultiplier_even]

theorem weightedEquationOperator_zero_reflection (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    weightedEquationOperator e he g hg hs CD hCD hquad 0 (by simp) (realLinftyReflection f) =
      realLinftyReflection (weightedEquationOperator e he g hg hs CD hCD hquad 0 (by simp) f) := by
  change weightedEquationMultiplier e he g hg hs CD hCD hquad (realLinftyReflection f)+
      g^2 • weightedKernelOperator e he g hg hs 0 (by simp) (realLinftyReflection f) =
      realLinftyReflection (weightedEquationMultiplier e he g hg hs CD hCD hquad f+
        g^2 • weightedKernelOperator e he g hg hs 0 (by simp) f)
  rw [weightedEquationMultiplier_reflection,weightedKernelOperator_zero_reflection,map_add,map_smul]

variable (hSmall : ‖weightedEquationPerturbation e he g hg hs hLower 0 (by simp)‖ ≤ 1/2)

include hCD hquad hSmall in
theorem weightedEquationSolution_zero_reflection :
    realLinftyReflection (weightedEquationSolution e he g hg hs hLower 0 (by simp)) =
      weightedEquationSolution e he g hg hs hLower 0 (by simp) := by
  apply weightedEquationSolution_unique e he g hg hs hLower CD hCD hquad 0 (by simp) hSmall
  rw [weightedEquationOperator_zero_reflection,
    weightedEquationSolution_equation e he g hg hs hLower CD hCD hquad 0 (by simp) hSmall,
    weightedKernelSource_zero_reflection]

include hCD hquad hSmall in
theorem weightedEquationEta_zero_ae_even :
    ∀ᵐ q ∂volume, weightedEquationEta e he g hg hs hLower 0 (by simp) (-q) =
      weightedEquationEta e he g hg hs hLower 0 (by simp) q := by
  have hr := realLinftyReflection_ae (weightedEquationSolution e he g hg hs hLower 0 (by simp))
  rw [weightedEquationSolution_zero_reflection e he g hg hs hLower CD hCD hquad hSmall] at hr
  filter_upwards [hr] with q hq
  simp only [weightedEquationEta,omega,norm_neg]
  rw [hq]

/-- Reflection of the absolutely meaningful raw integral uses only one AE
identity of its fixed input, never a parameter-dependent null-set substitution. -/
theorem weightedEtaIntegral_zero_even_of_ae (eta : GW.Space → ℝ)
    (hEven : ∀ᵐ r ∂volume, eta (-r) = eta r) :
    Function.Even (weightedEtaIntegral e he g hg hs 0 eta) := by
  intro q
  unfold weightedEtaIntegral
  have hchange := space_negation_preserving.integral_comp (MeasurableEquiv.neg GW.Space).measurableEmbedding
    (fun r => remainderKernel e he g hg hs 0 (-q) r*muDensity 0 r*eta r)
  calc
    _ = ∫ r,remainderKernel e he g hg hs 0 (-q) (-r)*muDensity 0 (-r)*eta (-r) := hchange.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hEven] with r hr
      have hF := remainderKernel_reflection e he g hg hs 0 q r
      simp only [neg_zero] at hF
      simp only [hF,muDensity,add_zero,norm_neg,hr]

include hCD hquad hSmall in
theorem weightedEquationEta_integral_zero_even :
    Function.Even (weightedEtaIntegral e he g hg hs 0
      (weightedEquationEta e he g hg hs hLower 0 (by simp))) :=
  weightedEtaIntegral_zero_even_of_ae e he g hg hs _
    (weightedEquationEta_zero_ae_even e he g hg hs hLower CD hCD hquad hSmall)

end Froehlich
