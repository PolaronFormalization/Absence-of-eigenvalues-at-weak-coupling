import Froehlich.Nodes.WE02Eta

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space)

/-- The same raw eta integral is AE strongly measurable without any
pointwise choice or alteration of its input. -/
theorem weightedEtaIntegral_aestronglyMeasurable (eta : GW.Space → ℝ)
    (hEta : AEStronglyMeasurable eta volume) :
    AEStronglyMeasurable (weightedEtaIntegral e he g hg hs P eta) volume := by
  have hMu : Measurable (fun qr : GW.Space × GW.Space => muDensity P qr.2) :=
    (muDensity_measurable P).comp measurable_snd
  have hm : AEStronglyMeasurable
      (fun qr : GW.Space × GW.Space => remainderKernel e he g hg hs P qr.1 qr.2*muDensity P qr.2*eta qr.2)
      (volume.prod volume) :=
    ((remainderKernel_measurable e he g hg hs P).mul hMu).aestronglyMeasurable.mul hEta.comp_snd
  exact hm.integral_prod_right'

variable (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
    (hP : ‖P‖ ≤ 1/4)

/-- The manuscript's convenient representative, defined by its actual integral. -/
def weightedEquationEtaPrime (q : GW.Space) : ℝ :=
  (thresholdDiagonalMultiplier e he g hg hs q)⁻¹*
    (kernelPsi e he g hg hs P q-g^2*weightedEtaIntegral e he g hg hs P
      (weightedEquationEta e he g hg hs hLower P hP) q)

theorem weightedEquationEtaPrime_aestronglyMeasurable :
    AEStronglyMeasurable (weightedEquationEtaPrime e he g hg hs P hLower hP) volume := by
  have hm : AEStronglyMeasurable
      (fun q : GW.Space => (thresholdDiagonalMultiplier e he g hg hs q)⁻¹) volume :=
    (thresholdDiagonalMultiplier_measurable e he g hg hs).inv.aestronglyMeasurable
  have hi := weightedEtaIntegral_aestronglyMeasurable e he g hg hs P
    (weightedEquationEta e he g hg hs hLower P hP)
    (weightedEquationEta_aestronglyMeasurable e he g hg hs hLower P hP)
  exact hm.mul ((kernelPsi_measurable e he g hg hs P).aestronglyMeasurable.sub (hi.const_mul (g^2)))

theorem weightedEquationEtaPrime_zero : weightedEquationEtaPrime e he g hg hs P hLower hP 0 = 0 := by
  simp only [weightedEquationEtaPrime,kernelPsi_zero,weightedEtaIntegral_zero,mul_zero,sub_self]

variable (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (hSmall : ‖weightedEquationPerturbation e he g hg hs hLower P hP‖ ≤ 1/2)

include hCD hquad hSmall in
theorem weightedEquationEtaPrime_ae :
    weightedEquationEtaPrime e he g hg hs P hLower hP =ᵐ[volume]
      weightedEquationEta e he g hg hs hLower P hP := by
  filter_upwards [weightedEquationEta_equation_ae e he g hg hs hLower P hP CD hCD hquad hSmall] with q hq
  have hn : thresholdDiagonalMultiplier e he g hg hs q ≠ 0 := by have h := hLower q; linarith
  have hsolve : kernelPsi e he g hg hs P q-g^2*weightedEtaIntegral e he g hg hs P
      (weightedEquationEta e he g hg hs hLower P hP) q =
      thresholdDiagonalMultiplier e he g hg hs q*weightedEquationEta e he g hg hs hLower P hP q := by linarith
  rw [weightedEquationEtaPrime,hsolve,←mul_assoc,inv_mul_cancel₀ hn,one_mul]

include hCD hquad hSmall in
theorem weightedEquationEtaPrime_integral_eq (q : GW.Space) :
    weightedEtaIntegral e he g hg hs P (weightedEquationEtaPrime e he g hg hs P hLower hP) q =
      weightedEtaIntegral e he g hg hs P (weightedEquationEta e he g hg hs hLower P hP) q :=
  weightedEtaIntegral_congr_ae e he g hg hs P _ _
    (weightedEquationEtaPrime_ae e he g hg hs P hLower hP CD hCD hquad hSmall) q

include hCD hquad hSmall in
theorem weightedEquationEtaPrime_equation (q : GW.Space) :
    thresholdDiagonalMultiplier e he g hg hs q*weightedEquationEtaPrime e he g hg hs P hLower hP q+
      g^2*weightedEtaIntegral e he g hg hs P (weightedEquationEtaPrime e he g hg hs P hLower hP) q =
        kernelPsi e he g hg hs P q := by
  rw [weightedEquationEtaPrime_integral_eq e he g hg hs P hLower hP CD hCD hquad hSmall]
  unfold weightedEquationEtaPrime
  have hn : thresholdDiagonalMultiplier e he g hg hs q ≠ 0 := by have h := hLower q; linarith
  rw [←mul_assoc,mul_inv_cancel₀ hn,one_mul]
  ring

end Froehlich
