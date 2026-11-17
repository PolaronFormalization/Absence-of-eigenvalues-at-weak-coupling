import Froehlich.Nodes.UV02FreeInverse
import Froehlich.Nodes.FD02WeightComparison

/-! The stronger free form-norm bound for (F+c)^-1, on the actual original
energy carrier. Physical identification is proved before form use. -/
noncomputable section
namespace Froehlich
variable (P : GW.Space) (c : ℝ) (hc : 1 ≤ c)

include hc in
theorem freeShift_energy_ratio (n : ℕ) (K : GW.Fock.Coordinates n) :
    energyWeight P n K/freeShiftWeight P c n K ≤ (Real.sqrt c)⁻¹ := by
  have hF := freeSymbol_nonneg P n K
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hW : 0 < freeShiftWeight P c n K := zero_lt_one.trans_le (freeShiftWeight_lower P c hc n K)
  have hs : (energyWeight P n K/freeShiftWeight P c n K)^2 ≤ 1/c := by
    rw [div_pow]
    unfold energyWeight
    rw [Real.sq_sqrt (by positivity)]
    simpa only [freeShiftWeight,zero_add,add_zero,add_comm] using
      freeShift_number_ratio_sq 0 (freeSymbol P n K) c (by norm_num) hF hc
  apply (sq_le_sq₀ (div_nonneg (zero_le_one.trans (energyWeight_ge_one P n K)) hW.le)
    (inv_nonneg.mpr (Real.sqrt_nonneg c))).mp
  refine hs.trans_eq ?_
  rw [inv_pow,Real.sq_sqrt hcpos.le]
  exact one_div c

def freeShiftEnergyAction : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  boundedFockAction (comparisonRatio (energyWeight P) (freeShiftWeight P c) (Real.sqrt c)⁻¹)
    (comparisonRatio_measurable _ _ (energyWeight_measurable P) (freeShiftWeight_measurable P c) _)
    (Real.sqrt c)⁻¹ (inv_nonneg.mpr (Real.sqrt_nonneg c))
    (comparisonRatio_bound _ _ (energyWeight_ge_one P) (freeShiftWeight_lower P c hc) _ (inv_nonneg.mpr (Real.sqrt_nonneg c)))
    (comparisonRatio_permutation _ _ (energyWeight_permutation P) (freeShiftWeight_permutation P c) _)

def freeShiftEnergyInverse : GW.Fock.Carrier →L[ℂ] EnergySpace P :=
  (energyCoordinates P).symm.toLinearIsometry.toContinuousLinearMap.comp (freeShiftEnergyAction P c hc)

theorem freeShiftEnergyInverse_norm_le (f : GW.Fock.Carrier) :
    ‖freeShiftEnergyInverse P c hc f‖ ≤ (Real.sqrt c)⁻¹*‖f‖ := by
  change ‖(energyCoordinates P).symm (freeShiftEnergyAction P c hc f)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  let r := comparisonRatio (energyWeight P) (freeShiftWeight P c) (Real.sqrt c)⁻¹
  let hr := comparisonRatio_measurable _ _ (energyWeight_measurable P) (freeShiftWeight_measurable P c) (Real.sqrt c)⁻¹
  let hb := comparisonRatio_bound _ _ (energyWeight_ge_one P) (freeShiftWeight_lower P c hc) (Real.sqrt c)⁻¹ (inv_nonneg.mpr (Real.sqrt_nonneg c))
  let hp := comparisonRatio_permutation _ _ (energyWeight_permutation P) (freeShiftWeight_permutation P c) (Real.sqrt c)⁻¹
  exact GW.Spaces.diagonal_norm_bound (boundedFockSector r hr (Real.sqrt c)⁻¹ hb hp)
    (inv_nonneg.mpr (Real.sqrt_nonneg c)) (boundedFockSector_norm r hr (Real.sqrt c)⁻¹
      (inv_nonneg.mpr (Real.sqrt_nonneg c)) hb hp) f

end Froehlich
