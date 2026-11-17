import Froehlich.Nodes.RS01WeightedSpace
import Froehlich.Nodes.FD02WeightComparison

/-! The bounded comparison map to the actual original fiber energy
space. Its clipped ratio is retained FD02 infrastructure; physical equality
on high support is proved separately, before this map is used on forms. -/
noncomputable section
namespace Froehlich

def auxiliaryComparisonAction (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  boundedFockAction (comparisonRatio (energyWeight (-p)) (auxiliaryWeight n e p) (Real.sqrt 3))
    (comparisonRatio_measurable _ _ (energyWeight_measurable (-p))
      (auxiliaryWeight_measurable n e p) (Real.sqrt 3))
    (Real.sqrt 3) (Real.sqrt_nonneg 3)
    (comparisonRatio_bound _ _ (energyWeight_ge_one (-p))
      (fun m K => auxiliaryWeight_ge_one n m e p he K) (Real.sqrt 3) (Real.sqrt_nonneg 3))
    (comparisonRatio_permutation _ _ (energyWeight_permutation (-p))
      (fun m tau K => auxiliaryWeight_permutation n m e p tau K) (Real.sqrt 3))

def auxiliaryToEnergy (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    AuxiliaryEnergySpace n e p he →L[ℂ] EnergySpace (-p) :=
  (energyCoordinates (-p)).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((auxiliaryComparisonAction n e p he).comp
      ((auxiliaryWeightedCoordinates n e p he).toLinearIsometry.toContinuousLinearMap.comp
        (AuxiliaryEnergySpace n e p he).subtypeL))

theorem auxiliaryComparisonAction_norm_le (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (u : GW.Fock.Carrier) : ‖auxiliaryComparisonAction n e p he u‖ ≤ Real.sqrt 3 * ‖u‖ := by
  let r := comparisonRatio (energyWeight (-p)) (auxiliaryWeight n e p) (Real.sqrt 3)
  let hr := comparisonRatio_measurable _ _ (energyWeight_measurable (-p))
    (auxiliaryWeight_measurable n e p) (Real.sqrt 3)
  let hb := comparisonRatio_bound _ _ (energyWeight_ge_one (-p))
    (fun m K => auxiliaryWeight_ge_one n m e p he K) (Real.sqrt 3) (Real.sqrt_nonneg 3)
  let hp := comparisonRatio_permutation _ _ (energyWeight_permutation (-p))
    (fun m tau K => auxiliaryWeight_permutation n m e p tau K) (Real.sqrt 3)
  exact GW.Spaces.diagonal_norm_bound (boundedFockSector r hr (Real.sqrt 3) hb hp)
    (Real.sqrt_nonneg 3) (boundedFockSector_norm r hr (Real.sqrt 3) (Real.sqrt_nonneg 3) hb hp) u

theorem auxiliaryToEnergy_norm_le (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (u : AuxiliaryEnergySpace n e p he) :
    ‖auxiliaryToEnergy n e p he u‖ ≤ Real.sqrt 3 * ‖u‖ := by
  change ‖(energyCoordinates (-p)).symm (auxiliaryComparisonAction n e p he
    (auxiliaryWeightedCoordinates n e p he (u : AuxiliaryFullEnergy n e p he)))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (auxiliaryComparisonAction_norm_le n e p he _).trans_eq
    (congrArg (fun a : ℝ => Real.sqrt 3 * a) ((auxiliaryWeightedCoordinates n e p he).norm_map u))

end Froehlich
