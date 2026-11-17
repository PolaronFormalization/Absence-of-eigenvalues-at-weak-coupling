import Froehlich.Nodes.CA02PhysicalJets
import Froehlich.Nodes.CA02WeightComparison

set_option autoImplicit false

/-! Genuine globally defined fixed-energy operator candidates. Their symbols
are normalized by the fixed weight; no parameter-dependent target or default
outside a parameter ball is used. -/
noncomputable section
open MeasureTheory
namespace Froehlich

def auxiliaryFixedEnergyWeightJet (is : List (Fin 3)) (n : ℕ) (e : ℝ)
    (p0 p : GW.Space) (he : e ≤ 0) :
    HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he :=
  (auxiliaryFreeInverseEnergy n e p0 he).toLinearIsometry.toContinuousLinearMap.comp
    (boundedHighFockAction n
      (fun m K => auxiliaryWeight n e p0 m K * auxiliaryInverseWeightJet is n e p m K)
      (fun m => (auxiliaryWeight_measurable n e p0 m).mul
        (auxiliaryInverseWeightJet_measurable is n m e p))
      (scalarDerivativeCoefficientBound is.length*(1+‖p0-p‖))
      (mul_nonneg (scalarDerivativeCoefficientBound_nonnegative is.length)
        (by positivity))
      (fun m K => auxiliaryInverseWeightJet_fixed_weight_bound is n m e he p0 p K)
      (by
        intro m tau K
        rw [auxiliaryWeight_permutation n m e p0 tau K,
          auxiliaryInverseWeightJet_permutation is n m e p tau K]))

theorem auxiliaryFixedEnergyWeightJet_norm_le (is : List (Fin 3)) (n : ℕ) (e : ℝ)
    (p0 p : GW.Space) (he : e ≤ 0) :
    ‖auxiliaryFixedEnergyWeightJet is n e p0 p he‖ ≤
      scalarDerivativeCoefficientBound is.length*(1+‖p0-p‖) := by
  let C := scalarDerivativeCoefficientBound is.length*(1+‖p0-p‖)
  have hC : 0 ≤ C := mul_nonneg (scalarDerivativeCoefficientBound_nonnegative is.length)
    (by positivity)
  let a : ∀ m, GW.Fock.Coordinates m → ℝ :=
    fun m K => auxiliaryWeight n e p0 m K * auxiliaryInverseWeightJet is n e p m K
  have ha : ∀ m, Measurable (a m) := fun m =>
    (auxiliaryWeight_measurable n e p0 m).mul
      (auxiliaryInverseWeightJet_measurable is n m e p)
  have hb : ∀ m K, |a m K| ≤ C := fun m K =>
    auxiliaryInverseWeightJet_fixed_weight_bound is n m e he p0 p K
  have hp : ∀ m (tau : Equiv.Perm (Fin m)) K,
      a m (fun i => K (tau i)) = a m K := by
    intro m tau K
    dsimp only [a]
    rw [auxiliaryWeight_permutation n m e p0 tau K,
      auxiliaryInverseWeightJet_permutation is n m e p tau K]
  let L : HighSectorSpace n →L[ℂ] HighSectorSpace n :=
    boundedHighFockAction n a ha C hC hb hp
  have hL : ‖L‖ ≤ C := by
    apply operator_norm_le_of_ae_multiplier_coordinates
      (HighSectorSpace n).subtypeₗᵢ (HighSectorSpace n).subtypeₗᵢ L
      (fun m K => (a m K : ℂ)) C hC
    · intro m K
      simpa only [Complex.norm_real,Real.norm_eq_abs] using hb m K
    · intro f m
      exact boundedHighFockAction_ae n a ha C hC hb hp f m
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  change ‖(auxiliaryFreeInverseEnergy n e p0 he) (L f)‖ ≤ C*‖f‖
  rw [LinearIsometryEquiv.norm_map]
  exact (ContinuousLinearMap.le_opNorm L f).trans
    (mul_le_mul_of_nonneg_right hL (norm_nonneg f))

theorem auxiliaryFixedEnergyWeightJet_local_norm_le (is : List (Fin 3)) (n : ℕ) (e : ℝ)
    (p0 p : GW.Space) (he : e ≤ 0) (hp : ‖p0-p‖ ≤ 1) :
    ‖auxiliaryFixedEnergyWeightJet is n e p0 p he‖ ≤
      2*scalarDerivativeCoefficientBound is.length := by
  have h := auxiliaryFixedEnergyWeightJet_norm_le is n e p0 p he
  have hc := scalarDerivativeCoefficientBound_nonnegative is.length
  nlinarith

end Froehlich
