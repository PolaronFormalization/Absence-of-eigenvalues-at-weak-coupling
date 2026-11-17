import Froehlich.Nodes.RS01EnergyEquivalence
import Froehlich.Nodes.FD02FreeForm

/-! Exact auxiliary weighted norm identity on the full actual domain.
The multiplier extension contributes zero below the supported sectors. -/
noncomputable section
open MeasureTheory Filter
namespace Froehlich

variable (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)

include hn in
theorem auxiliaryWeighted_sector_norm_identity (u : AuxiliaryEnergySpace n e p he.2) (m : ℕ) :
    (∫ K, (auxiliaryWeight n e p m K)^2 *
      ‖physicalSector m (energyEmbedding (-p) (auxiliaryToEnergy n e p he.2 u) m) K‖^2
        ∂GW.Fock.sectorMeasure m) =
      freeSectorEnergy (-p) m (energyEmbedding (-p) (auxiliaryToEnergy n e p he.2 u) m) +
      (1-(n : ℝ)-e)*‖energyEmbedding (-p) (auxiliaryToEnergy n e p he.2 u) m‖^2 := by
  let x := auxiliaryToEnergy n e p he.2 u
  let v : GW.Fock.Carrier := energyEmbedding (-p) x
  change (∫ K, (auxiliaryWeight n e p m K)^2 * ‖physicalSector m (v m) K‖^2
    ∂GW.Fock.sectorMeasure m) = freeSectorEnergy (-p) m (v m) + (1-(n : ℝ)-e)*‖v m‖^2
  have hf := freeSectorEnergy_integrable (-p) x m
  have hp := (Lp.memLp (physicalSector m (v m))).integrable_norm_pow
    (p := 2) (by norm_num)
  have hae : (fun K => (auxiliaryWeight n e p m K)^2 * ‖physicalSector m (v m) K‖^2)
      =ᵐ[GW.Fock.sectorMeasure m]
      (fun K => freeSymbol (-p) m K * ‖physicalSector m (v m) K‖^2 +
        (1-(n : ℝ)-e)*‖physicalSector m (v m) K‖^2) := by
    by_cases hnm : n ≤ m
    · apply Eventually.of_forall
      intro K
      change (auxiliaryWeight n e p m K)^2 * ‖physicalSector m (v m) K‖^2 =
        freeSymbol (-p) m K * ‖physicalSector m (v m) K‖^2 +
        (1-(n : ℝ)-e)*‖physicalSector m (v m) K‖^2
      rw [auxiliaryWeight_sq n m e p he.2 hnm]
      ring
    · have hz : physicalSector m (v m) = (0 : GW.Fock.AmbientSector m) := by
        change physicalSector m (energyEmbedding (-p) (auxiliaryToEnergy n e p he.2 u) m) = _
        rw [auxiliaryToEnergy_physical n e p hn he,
          auxiliaryPhysical_below n m e p he.2 u (Nat.lt_of_not_ge hnm),map_zero]
      rw [hz]
      filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := GW.Fock.sectorMeasure m)] with K hK
      simp only [hK,Pi.zero_apply,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,add_zero]
  rw [integral_congr_ae hae,integral_add hf (hp.const_mul (1-(n : ℝ)-e)),integral_const_mul]
  change freeSectorEnergy (-p) m (energyEmbedding (-p) x m) +
    (1-(n : ℝ)-e)*(∫ K, ‖physicalSector m (v m) K‖^2 ∂GW.Fock.sectorMeasure m) = _
  rw [← GW.Analysis.l2_norm_sq (𝕜 := ℂ),LinearIsometry.norm_map]

include hn in
theorem auxiliaryWeighted_norm_identity (u : AuxiliaryEnergySpace n e p he.2) :
    ‖u‖^2 = freeEnergy (-p) (auxiliaryFullEmbedding n e p he.2 (u : AuxiliaryFullEnergy n e p he.2)) +
      (1-(n : ℝ)-e)*‖auxiliaryFullEmbedding n e p he.2 (u : AuxiliaryFullEnergy n e p he.2)‖^2 := by
  let x := auxiliaryToEnergy n e p he.2 u
  have hnorm := fockWeighted_norm_sq (auxiliaryWeight n e p) (auxiliaryWeight_measurable n e p)
    (fun m K => auxiliaryWeight_ge_one n m e p he.2 K)
    (fun m tau K => auxiliaryWeight_permutation n m e p tau K) (u : AuxiliaryFullEnergy n e p he.2)
  have hi := fockWeightedInclusion_apply (auxiliaryWeight n e p) (auxiliaryWeight_measurable n e p)
    (fun m K => auxiliaryWeight_ge_one n m e p he.2 K)
    (fun m tau K => auxiliaryWeight_permutation n m e p tau K) (u : AuxiliaryFullEnergy n e p he.2)
  have hval : weightedFockValue (auxiliaryWeight n e p) (auxiliaryWeight_measurable n e p)
      (fun m K => auxiliaryWeight_ge_one n m e p he.2 K)
      (fun m tau K => auxiliaryWeight_permutation n m e p tau K) (u : AuxiliaryFullEnergy n e p he.2) =
      energyEmbedding (-p) x := hi.symm.trans (auxiliaryToEnergy_physical n e p hn he u).symm
  rw [hval] at hnorm
  have hfs := freeSectorEnergy_summable (-p) x
  have hps := (GW.Analysis.memℓp_two_iff_sq _).mp (energyEmbedding (-p) x).property
  have hsum : (∑' m, ∫ K, (auxiliaryWeight n e p m K)^2 *
      ‖physicalSector m (energyEmbedding (-p) x m) K‖^2 ∂GW.Fock.sectorMeasure m) =
      ∑' m, (freeSectorEnergy (-p) m (energyEmbedding (-p) x m) +
        (1-(n : ℝ)-e)*‖energyEmbedding (-p) x m‖^2) :=
    tsum_congr (auxiliaryWeighted_sector_norm_identity n e p hn he u)
  rw [hsum, Summable.tsum_add hfs (hps.mul_left (1-(n : ℝ)-e)),tsum_mul_left,
    ← GW.Fock.carrier_norm_sq] at hnorm
  rw [← auxiliaryToEnergy_physical n e p hn he u]
  exact hnorm

end Froehlich
