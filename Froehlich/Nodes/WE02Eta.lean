import Froehlich.Nodes.WE02Equation

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

def weightedEquationEta (q : GW.Space) : ℝ :=
  omega q*weightedEquationSolution e he g hg hs hLower P hP q

theorem weightedEquationEta_aestronglyMeasurable :
    AEStronglyMeasurable (weightedEquationEta e he g hg hs hLower P hP) volume :=
  omega_measurable.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)

theorem weightedEquationEta_bound : ∀ᵐ q ∂volume,
    |weightedEquationEta e he g hg hs hLower P hP q| ≤
      ‖weightedEquationSolution e he g hg hs hLower P hP‖*omega q := by
  filter_upwards [linftyReal_ae_norm_le (weightedEquationSolution e he g hg hs hLower P hP)] with q hq
  rw [weightedEquationEta,abs_mul,abs_of_nonneg (omega_nonneg q)]
  simpa only [Real.norm_eq_abs,mul_comm] using mul_le_mul_of_nonneg_left hq (omega_nonneg q)

theorem omega_normalizedKernelPsi (q : GW.Space) :
    omega q*normalizedKernelPsi e he g hg hs P q = kernelPsi e he g hg hs P q := by
  by_cases hq : q = 0
  · subst q
    rw [normalizedKernelPsi_zero,kernelPsi_zero,mul_zero]
  · have ho : omega q ≠ 0 := ne_of_gt (lt_min (norm_pos_iff.mpr hq) zero_lt_one)
    rw [normalizedKernelPsi,ite_eq_right hq]
    field_simp [ho]

variable (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (hSmall : ‖weightedEquationPerturbation e he g hg hs hLower P hP‖ ≤ 1/2)

include hCD hquad hSmall in
theorem weightedEquationSolution_equation_ae : ∀ᵐ q ∂volume,
    thresholdDiagonalMultiplier e he g hg hs q*weightedEquationSolution e he g hg hs hLower P hP q+
      g^2*normalizedWeightedIntegral e he g hg hs P
        (weightedEquationSolution e he g hg hs hLower P hP) q = normalizedKernelPsi e he g hg hs P q := by
  let z := weightedEquationSolution e he g hg hs hLower P hP
  let M := weightedEquationMultiplier e he g hg hs CD hCD hquad
  let L := weightedKernelOperator e he g hg hs P hP
  have hEq := weightedEquationSolution_equation e he g hg hs hLower CD hCD hquad P hP hSmall
  filter_upwards [Lp.coeFn_add (M z) (g^2 • L z),Lp.coeFn_smul (g^2) (L z),
    weightedEquationMultiplier_ae e he g hg hs CD hCD hquad z,
    weightedKernelOperator_ae e he g hg hs P hP z,weightedKernelSource_ae e he g hg hs P hP]
      with q hadd hsmul hm hl hchi
  have h := congrArg (fun f : Lp ℝ ⊤ (volume : Measure GW.Space) => f q) hEq
  change (M z+g^2 • L z) q = _ at h
  rw [hadd,Pi.add_apply,hsmul,Pi.smul_apply,smul_eq_mul,hm,hl,hchi] at h
  exact h

include hCD hquad hSmall in
theorem weightedEquationEta_equation_ae : ∀ᵐ q ∂volume,
    thresholdDiagonalMultiplier e he g hg hs q*weightedEquationEta e he g hg hs hLower P hP q+
      g^2*weightedEtaIntegral e he g hg hs P (weightedEquationEta e he g hg hs hLower P hP) q =
        kernelPsi e he g hg hs P q := by
  filter_upwards [weightedEquationSolution_equation_ae e he g hg hs hLower P hP CD hCD hquad hSmall] with q hq
  calc
    _ = omega q*(thresholdDiagonalMultiplier e he g hg hs q*
        weightedEquationSolution e he g hg hs hLower P hP q+
        g^2*normalizedWeightedIntegral e he g hg hs P
          (weightedEquationSolution e he g hg hs hLower P hP) q) := by
      unfold weightedEquationEta
      rw [weightedEtaIntegral_omega_mul]
      ring
    _ = omega q*normalizedKernelPsi e he g hg hs P q := congrArg (fun z : ℝ => omega q*z) hq
    _ = _ := omega_normalizedKernelPsi e he g hg hs P q

end Froehlich
