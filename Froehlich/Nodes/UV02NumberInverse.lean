import Froehlich.Nodes.UV02EnergyInverse
import Froehlich.Nodes.EN02Number

/-! The free shifted reciprocal is the same physical vector in the
original energy and number-form norms, with the source c^-1/2 bound. -/
noncomputable section
open MeasureTheory Filter
namespace Froehlich
variable (P : GW.Space) (c : ℝ) (hc : 1 ≤ c)

theorem freeShiftEnergyInverse_coordinates (f : GW.Fock.Carrier) :
    energyCoordinates P (freeShiftEnergyInverse P c hc f)=freeShiftEnergyAction P c hc f := by
  change energyCoordinates P ((energyCoordinates P).symm _) = _
  exact (energyCoordinates P).apply_symm_apply _

theorem freeShiftEnergyAction_ae (f : GW.Fock.Carrier) (n : ℕ) :
    (fun K => (comparisonRatio (energyWeight P) (freeShiftWeight P c) (Real.sqrt c)⁻¹ n K : ℂ) •
      physicalSector n (f n) K) =ᵐ[GW.Fock.sectorMeasure n] physicalSector n (freeShiftEnergyAction P c hc f n) :=
  boundedFockAction_ae _
    (comparisonRatio_measurable _ _ (energyWeight_measurable P) (freeShiftWeight_measurable P c) _)
    (Real.sqrt c)⁻¹ (inv_nonneg.mpr (Real.sqrt_nonneg c))
    (comparisonRatio_bound _ _ (energyWeight_ge_one P) (freeShiftWeight_lower P c hc) _ (inv_nonneg.mpr (Real.sqrt_nonneg c)))
    (comparisonRatio_permutation _ _ (energyWeight_permutation P) (freeShiftWeight_permutation P c) _) f n

include hc in
theorem freeShiftComparisonRatio_literal (n : ℕ) (K : GW.Fock.Coordinates n) :
    comparisonRatio (energyWeight P) (freeShiftWeight P c) (Real.sqrt c)⁻¹ n K =
      energyWeight P n K/freeShiftWeight P c n K := by
  unfold comparisonRatio
  exact min_eq_right (freeShift_energy_ratio P c hc n K)

theorem freeShiftEnergyInverse_physical (f : GW.Fock.Carrier) :
    energyEmbedding P (freeShiftEnergyInverse P c hc f)=freeShiftInverse P c hc f := by
  apply lp.ext
  funext n
  apply (physicalSector n).injective
  apply Lp.ext
  have ht := energyEmbedding_weighted_ae P (freeShiftEnergyInverse P c hc f) n
  rw [freeShiftEnergyInverse_coordinates] at ht
  have ha := freeShiftEnergyAction_ae P c hc f n
  have hw := freeShiftInverse_weighted_ae P c hc f n
  filter_upwards [ht,ha,hw] with K ht ha hw
  simp only [smul_eq_mul] at ht ha
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (zero_lt_one.trans_le (energyWeight_ge_one P n K))))
  rw [ht,←ha,freeShiftComparisonRatio_literal P c hc n K,←hw,Complex.ofReal_div]
  have hW : (freeShiftWeight P c n K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (zero_lt_one.trans_le (freeShiftWeight_lower P c hc n K)))
  field_simp [hW]

def freeShiftNumberInverse : GW.Fock.Carrier →L[ℂ] NumberFormSpace :=
  (energyNumberCoordinates P).comp (freeShiftEnergyInverse P c hc)

theorem freeShiftNumberInverse_physical (f : GW.Fock.Carrier) :
    numberFormEmbedding (freeShiftNumberInverse P c hc f)=freeShiftInverse P c hc f := by
  change numberFormEmbedding (energyNumberCoordinates P (freeShiftEnergyInverse P c hc f))=_
  rw [energyNumberCoordinates_intertwines,freeShiftEnergyInverse_physical]

theorem freeShiftNumberInverse_norm_le (f : GW.Fock.Carrier) :
    ‖freeShiftNumberInverse P c hc f‖ ≤ (Real.sqrt c)⁻¹*‖f‖ :=
  (energyNumberCoordinates_norm_le P (freeShiftEnergyInverse P c hc f)).trans
    (freeShiftEnergyInverse_norm_le P c hc f)

end Froehlich
