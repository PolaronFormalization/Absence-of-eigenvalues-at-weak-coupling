import Froehlich.Nodes.EN02
import Froehlich.Nodes.GW03

/-! EN02's norm-one map from energy coordinates to number-form coordinates. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich


def sectorEnergyNumberMap (P : GW.Space) (n : ℕ) : GW.Fock.Sector n →L[ℂ] GW.Fock.Sector n :=
  (Real.sqrt ((n : ℝ)+1) : ℂ) • sectorEnergyEmbedding P n

theorem sectorEnergyNumberMap_bound (P : GW.Space) (n : ℕ) (u : GW.Fock.Sector n) :
    ‖sectorEnergyNumberMap P n u‖ ≤ ‖u‖ := by
  rw [← (physicalSector n).norm_map (sectorEnergyNumberMap P n u),
    ← (physicalSector n).norm_map u]
  apply Lp.norm_le_norm_of_ae_le
  have hsm := Lp.coeFn_smul (Real.sqrt ((n : ℝ)+1) : ℂ)
    (physicalSector n (sectorEnergyEmbedding P n u))
  filter_upwards [sectorEnergyEmbedding_weighted_ae P n u, hsm] with k hk hsm
  change ‖physicalSector n ((Real.sqrt ((n : ℝ)+1) : ℂ) • sectorEnergyEmbedding P n u) k‖ ≤ _
  rw [map_smul, hsm, Pi.smul_apply, ← hk, norm_smul, norm_smul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (zero_le_one.trans (energyWeight_ge_one P n k))]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  unfold energyWeight freeSymbol
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg ‖totalMomentum n k - P‖]

theorem sectorEnergyNumberMap_norm (P : GW.Space) (n : ℕ) : ‖sectorEnergyNumberMap P n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using sectorEnergyNumberMap_bound P n u

/-- This map preserves the physical vector and changes its Hilbert graph norm. -/
def energyNumberCoordinates (P : GW.Space) : EnergySpace P →L[ℂ] NumberFormSpace :=
  (GW.Spaces.diagonalMap (sectorEnergyNumberMap P) zero_le_one (sectorEnergyNumberMap_norm P)).comp
    (energyCoordinates P).toLinearIsometry.toContinuousLinearMap

theorem energyNumberCoordinates_norm_le (P : GW.Space) (x : EnergySpace P) :
    ‖energyNumberCoordinates P x‖ ≤ ‖x‖ := by
  have h := GW.Spaces.diagonal_norm_bound (sectorEnergyNumberMap P) zero_le_one
    (sectorEnergyNumberMap_norm P) (energyCoordinates P x)
  rw [one_mul, (energyCoordinates P).norm_map x] at h
  exact h

theorem energyNumberCoordinates_intertwines (P : GW.Space) (x : EnergySpace P) :
    numberFormEmbedding (energyNumberCoordinates P x) = energyEmbedding P x := by
  apply lp.ext
  funext n
  rw [numberFormEmbedding_sqrt_apply, energyEmbedding_apply]
  change (((Real.sqrt ((n : ℝ)+1))⁻¹ : ℝ) : ℂ) •
    ((Real.sqrt ((n : ℝ)+1) : ℂ) • sectorEnergyEmbedding P n (energyCoordinates P x n)) = _
  rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (by positivity)))]
  simp only [Complex.ofReal_one, one_smul]

end Froehlich
