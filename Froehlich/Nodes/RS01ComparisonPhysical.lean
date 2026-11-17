import Froehlich.Nodes.RS01ComparisonMap
import Froehlich.Nodes.RS01WeightedSupport

/-! The clipped comparison is exactly the physical identity on the
supported weighted domain. No global comparison is asserted below n. -/
noncomputable section
open MeasureTheory Filter
namespace Froehlich

theorem auxiliaryToEnergy_coordinates (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (u : AuxiliaryEnergySpace n e p he) :
    energyCoordinates (-p) (auxiliaryToEnergy n e p he u) =
      auxiliaryComparisonAction n e p he
        (auxiliaryWeightedCoordinates n e p he (u : AuxiliaryFullEnergy n e p he)) := by
  change energyCoordinates (-p) ((energyCoordinates (-p)).symm _) = _
  exact (energyCoordinates (-p)).apply_symm_apply _

theorem auxiliaryComparisonAction_ae (n m : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (u : GW.Fock.Carrier) :
    (fun K => (comparisonRatio (energyWeight (-p)) (auxiliaryWeight n e p) (Real.sqrt 3) m K : ℂ) •
      physicalSector m (u m) K) =ᵐ[GW.Fock.sectorMeasure m]
      physicalSector m (auxiliaryComparisonAction n e p he u m) :=
  boundedFockAction_ae _
    (comparisonRatio_measurable _ _ (energyWeight_measurable (-p))
      (auxiliaryWeight_measurable n e p) (Real.sqrt 3))
    (Real.sqrt 3) (Real.sqrt_nonneg 3)
    (comparisonRatio_bound _ _ (energyWeight_ge_one (-p))
      (fun m K => auxiliaryWeight_ge_one n m e p he K) (Real.sqrt 3) (Real.sqrt_nonneg 3))
    (comparisonRatio_permutation _ _ (energyWeight_permutation (-p))
      (fun m tau K => auxiliaryWeight_permutation n m e p tau K) (Real.sqrt 3)) u m

theorem auxiliaryComparisonRatio_of_ge (n m : ℕ) (e : ℝ) (p : GW.Space)
    (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hnm : n ≤ m) (K : GW.Fock.Coordinates m) :
    comparisonRatio (energyWeight (-p)) (auxiliaryWeight n e p) (Real.sqrt 3) m K =
      energyWeight (-p) m K / auxiliaryWeight n e p m K := by
  unfold comparisonRatio
  apply min_eq_right
  exact (div_le_iff₀ (zero_lt_one.trans_le (auxiliaryWeight_ge_one n m e p he.2 K))).mpr
    (energyWeight_le_auxiliaryWeight n m e p hn he hnm K)

theorem auxiliaryToEnergy_physical (n : ℕ) (e : ℝ) (p : GW.Space)
    (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (u : AuxiliaryEnergySpace n e p he.2) :
    energyEmbedding (-p) (auxiliaryToEnergy n e p he.2 u) =
      auxiliaryFullEmbedding n e p he.2 (u : AuxiliaryFullEnergy n e p he.2) := by
  apply lp.ext
  funext m
  apply (physicalSector m).injective
  apply Lp.ext
  have ht := energyEmbedding_weighted_ae (-p) (auxiliaryToEnergy n e p he.2 u) m
  rw [auxiliaryToEnergy_coordinates] at ht
  have hu := auxiliaryWeightedCoordinates_physical n m e p he.2 u
  have ha := auxiliaryComparisonAction_ae n m e p he.2
    (auxiliaryWeightedCoordinates n e p he.2 (u : AuxiliaryFullEnergy n e p he.2))
  by_cases hnm : n ≤ m
  · filter_upwards [ht,hu,ha] with K ht hu ha
    simp only [smul_eq_mul] at ht ha
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (zero_lt_one.trans_le (energyWeight_ge_one (-p) m K))))
    rw [ht,← ha,auxiliaryComparisonRatio_of_ge n m e p hn he hnm,← hu,Complex.ofReal_div]
    have hW : (auxiliaryWeight n e p m K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (ne_of_gt (zero_lt_one.trans_le (auxiliaryWeight_ge_one n m e p he.2 K)))
    field_simp [hW]
  · have hmn : m < n := Nat.lt_of_not_ge hnm
    have hz : (fun K => physicalSector m
        (auxiliaryFullEmbedding n e p he.2 (u : AuxiliaryFullEnergy n e p he.2) m) K) =ᵐ[GW.Fock.sectorMeasure m]
        (fun _ => (0 : ℂ)) := by
      rw [auxiliaryPhysical_below n m e p he.2 u hmn,map_zero]
      exact Lp.coeFn_zero (E := ℂ) (p := 2) (μ := GW.Fock.sectorMeasure m)
    filter_upwards [ht,hu,ha,hz] with K ht hu ha hz
    simp only [smul_eq_mul] at ht ha
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (zero_lt_one.trans_le (energyWeight_ge_one (-p) m K))))
    rw [ht,← ha,← hu]
    simp only [hz,mul_zero]

end Froehlich
