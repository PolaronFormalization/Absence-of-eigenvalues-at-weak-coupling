import Froehlich.Nodes.CA02FixedEnergyJets

set_option autoImplicit false

/-! Actual normalized symbols in the existing onto energy coordinates.
This identity is the fixed-target multiplier input for the norm calculus. -/
noncomputable section
open MeasureTheory
namespace Froehlich

def auxiliaryFixedEnergyJetCoordinates (is : List (Fin 3)) (n : ℕ) (e : ℝ)
    (p0 p : GW.Space) (he : e ≤ 0) : HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  (auxiliaryEnergyCoordinates n e p0 he).toLinearIsometry.toContinuousLinearMap.comp
    (auxiliaryFixedEnergyWeightJet is n e p0 p he)

theorem auxiliaryFixedEnergyJetCoordinates_ae (is : List (Fin 3)) (n m : ℕ) (e : ℝ)
    (p0 p : GW.Space) (he : e ≤ 0) (f : HighSectorSpace n) :
    (fun K => ((auxiliaryWeight n e p0 m K * auxiliaryInverseWeightJet is n e p m K : ℝ) : ℂ) •
      physicalSector m ((f : GW.Fock.Carrier) m) K) =ᵐ[GW.Fock.sectorMeasure m]
      physicalSector m ((auxiliaryFixedEnergyJetCoordinates is n e p0 p he f : GW.Fock.Carrier) m) := by
  let a : ∀ m, GW.Fock.Coordinates m → ℝ :=
    fun m K => auxiliaryWeight n e p0 m K * auxiliaryInverseWeightJet is n e p m K
  let C := scalarDerivativeCoefficientBound is.length*(1+‖p0-p‖)
  have hC : 0 ≤ C := mul_nonneg (scalarDerivativeCoefficientBound_nonnegative is.length) (by positivity)
  have ha : ∀ m, Measurable (a m) := fun m =>
    (auxiliaryWeight_measurable n e p0 m).mul (auxiliaryInverseWeightJet_measurable is n m e p)
  have hb : ∀ m K, |a m K| ≤ C := fun m K =>
    auxiliaryInverseWeightJet_fixed_weight_bound is n m e he p0 p K
  have hp : ∀ m (tau : Equiv.Perm (Fin m)) K, a m (fun j => K (tau j)) = a m K := by
    intro m tau K
    dsimp only [a]
    rw [auxiliaryWeight_permutation n m e p0 tau K,
      auxiliaryInverseWeightJet_permutation is n m e p tau K]
  have hcoord : auxiliaryFixedEnergyJetCoordinates is n e p0 p he f =
      boundedHighFockAction n a ha C hC hb hp f := by
    change (auxiliaryEnergyCoordinates n e p0 he)
      ((auxiliaryEnergyCoordinates n e p0 he).symm (boundedHighFockAction n a ha C hC hb hp f)) = _
    exact (auxiliaryEnergyCoordinates n e p0 he).apply_symm_apply _
  rw [hcoord]
  exact boundedHighFockAction_ae n a ha C hC hb hp f m

end Froehlich
