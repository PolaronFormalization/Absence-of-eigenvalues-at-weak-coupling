import Froehlich.Nodes.CA02FixedEnergyPhysical
import Froehlich.Nodes.RS01EnergyEquivalence

/-! The source bounded relative multipliers D_alpha on the actual physical
high sector. They factor every genuine weight jet and satisfy D_0=I. -/
noncomputable section
namespace Froehlich

theorem auxiliaryEnergyEmbedding_injective (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    Function.Injective (auxiliaryEnergyEmbedding n e p he) := by
  intro u v h
  apply Subtype.ext
  apply auxiliaryFullEmbedding_injective n e p he
  exact congrArg (fun z : HighSectorSpace n => (z : GW.Fock.Carrier)) h

theorem auxiliaryPhysicalFreeInverse_injective (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    Function.Injective (auxiliaryPhysicalFreeInverse n e p he) := by
  intro u v h
  apply (auxiliaryFreeInverseEnergy n e p he).injective
  apply auxiliaryEnergyEmbedding_injective n e p he
  exact h

def auxiliaryRelativeWeightJet (is : List (Fin 3)) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  (auxiliaryEnergyCoordinates n e p he).toLinearIsometry.toContinuousLinearMap.comp
    (auxiliaryFixedEnergyWeightJet is n e p p he)

theorem auxiliaryRelativeWeightJet_norm_le (is : List (Fin 3)) (n : ℕ) (e : ℝ)
    (p : GW.Space) (he : e ≤ 0) :
    ‖auxiliaryRelativeWeightJet is n e p he‖ ≤ scalarDerivativeCoefficientBound is.length := by
  have hb := auxiliaryFixedEnergyWeightJet_norm_le is n e p p he
  simp only [sub_self,norm_zero,add_zero,mul_one] at hb
  apply ContinuousLinearMap.opNorm_le_bound _ (scalarDerivativeCoefficientBound_nonnegative _)
  intro u
  change ‖auxiliaryEnergyCoordinates n e p he (auxiliaryFixedEnergyWeightJet is n e p p he u)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact ((auxiliaryFixedEnergyWeightJet is n e p p he).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg u))

theorem auxiliaryRelativeWeightJet_factor (is : List (Fin 3)) (n : ℕ) (e : ℝ)
    (p : GW.Space) (he : e ≤ 0) :
    (auxiliaryPhysicalFreeInverse n e p he).comp (auxiliaryRelativeWeightJet is n e p he) =
      auxiliaryPhysicalWeightJet is n e p he := by
  rw [← auxiliaryFixedEnergyWeightJet_physical is n e p p he]
  apply ContinuousLinearMap.ext
  intro u
  change auxiliaryEnergyEmbedding n e p he
    (auxiliaryFreeInverseEnergy n e p he
      (auxiliaryEnergyCoordinates n e p he (auxiliaryFixedEnergyWeightJet is n e p p he u))) = _
  rw [auxiliaryFreeInverseEnergy,LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem auxiliaryRelativeWeightJet_nil (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    auxiliaryRelativeWeightJet [] n e p he = 1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply auxiliaryPhysicalFreeInverse_injective n e p he
  have h := congrArg (fun A : HighSectorSpace n →L[ℂ] HighSectorSpace n => A u)
    (auxiliaryRelativeWeightJet_factor [] n e p he)
  simpa only [ContinuousLinearMap.comp_apply,auxiliaryPhysicalWeightJet_nil,
    ContinuousLinearMap.one_apply] using h

end Froehlich
