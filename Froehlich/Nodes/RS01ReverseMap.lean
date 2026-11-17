import Froehlich.Nodes.RS01ComparisonPhysical
import Froehlich.Nodes.RS01ReverseWeights

/-! Reverse bounded comparison on the complete original energy domain.
Its global weight bound avoids any restriction of the eventual weak tests. -/
noncomputable section
open MeasureTheory Filter
namespace Froehlich

def auxiliaryReverseAction (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  boundedFockAction (comparisonRatio (auxiliaryWeight n e p) (energyWeight (-p)) (Real.sqrt (5/4 : ℝ)))
    (comparisonRatio_measurable _ _ (auxiliaryWeight_measurable n e p)
      (energyWeight_measurable (-p)) (Real.sqrt (5/4 : ℝ)))
    (Real.sqrt (5/4 : ℝ)) (Real.sqrt_nonneg _)
    (comparisonRatio_bound _ _ (fun m K => auxiliaryWeight_ge_one n m e p he K)
      (energyWeight_ge_one (-p)) (Real.sqrt (5/4 : ℝ)) (Real.sqrt_nonneg _))
    (comparisonRatio_permutation _ _ (fun m tau K => auxiliaryWeight_permutation n m e p tau K)
      (energyWeight_permutation (-p)) (Real.sqrt (5/4 : ℝ)))

def auxiliaryFromEnergyFull (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    EnergySpace (-p) →L[ℂ] AuxiliaryFullEnergy n e p he :=
  (auxiliaryWeightedCoordinates n e p he).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((auxiliaryReverseAction n e p he).comp (energyCoordinates (-p)).toLinearIsometry.toContinuousLinearMap)

theorem auxiliaryFromEnergyFull_norm_le (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (u : EnergySpace (-p)) :
    ‖auxiliaryFromEnergyFull n e p he u‖ ≤ Real.sqrt (5/4 : ℝ) * ‖u‖ := by
  let r := comparisonRatio (auxiliaryWeight n e p) (energyWeight (-p)) (Real.sqrt (5/4 : ℝ))
  let hr := comparisonRatio_measurable _ _ (auxiliaryWeight_measurable n e p)
    (energyWeight_measurable (-p)) (Real.sqrt (5/4 : ℝ))
  let hb := comparisonRatio_bound _ _ (fun m K => auxiliaryWeight_ge_one n m e p he K)
    (energyWeight_ge_one (-p)) (Real.sqrt (5/4 : ℝ)) (Real.sqrt_nonneg (5/4 : ℝ))
  let hp := comparisonRatio_permutation _ _ (fun m tau K => auxiliaryWeight_permutation n m e p tau K)
    (energyWeight_permutation (-p)) (Real.sqrt (5/4 : ℝ))
  have h := GW.Spaces.diagonal_norm_bound (boundedFockSector r hr (Real.sqrt (5/4 : ℝ)) hb hp)
    (Real.sqrt_nonneg (5/4 : ℝ))
    (boundedFockSector_norm r hr (Real.sqrt (5/4 : ℝ)) (Real.sqrt_nonneg _) hb hp)
    (energyCoordinates (-p) u)
  change ‖(auxiliaryWeightedCoordinates n e p he).symm
    (auxiliaryReverseAction n e p he (energyCoordinates (-p) u))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact h.trans_eq (congrArg (fun a : ℝ => Real.sqrt (5/4 : ℝ)*a) ((energyCoordinates (-p)).norm_map u))

theorem auxiliaryFullWeightedCoordinates_physical (n m : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (u : AuxiliaryFullEnergy n e p he) :
    (fun K => (auxiliaryWeight n e p m K : ℂ) * physicalSector m
      (auxiliaryFullEmbedding n e p he u m) K) =ᵐ[GW.Fock.sectorMeasure m]
      physicalSector m (auxiliaryWeightedCoordinates n e p he u m) := by
  have h := fockWeightedCoordinates_physical (auxiliaryWeight n e p)
    (auxiliaryWeight_measurable n e p) (fun m K => auxiliaryWeight_ge_one n m e p he K)
    (fun m tau K => auxiliaryWeight_permutation n m e p tau K) u m
  have hi := fockWeightedInclusion_apply (auxiliaryWeight n e p)
    (auxiliaryWeight_measurable n e p) (fun m K => auxiliaryWeight_ge_one n m e p he K)
    (fun m tau K => auxiliaryWeight_permutation n m e p tau K) u
  change auxiliaryFullEmbedding n e p he u = _ at hi
  rw [hi]
  exact h

theorem auxiliaryReverseAction_ae (n m : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (u : GW.Fock.Carrier) :
    (fun K => (comparisonRatio (auxiliaryWeight n e p) (energyWeight (-p)) (Real.sqrt (5/4 : ℝ)) m K : ℂ) •
      physicalSector m (u m) K) =ᵐ[GW.Fock.sectorMeasure m]
      physicalSector m (auxiliaryReverseAction n e p he u m) :=
  boundedFockAction_ae _
    (comparisonRatio_measurable _ _ (auxiliaryWeight_measurable n e p)
      (energyWeight_measurable (-p)) (Real.sqrt (5/4 : ℝ)))
    (Real.sqrt (5/4 : ℝ)) (Real.sqrt_nonneg _)
    (comparisonRatio_bound _ _ (fun m K => auxiliaryWeight_ge_one n m e p he K)
      (energyWeight_ge_one (-p)) (Real.sqrt (5/4 : ℝ)) (Real.sqrt_nonneg _))
    (comparisonRatio_permutation _ _ (fun m tau K => auxiliaryWeight_permutation n m e p tau K)
      (energyWeight_permutation (-p)) (Real.sqrt (5/4 : ℝ))) u m

theorem auxiliaryFromEnergyFull_physical (n : ℕ) (e : ℝ) (p : GW.Space)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (u : EnergySpace (-p)) :
    auxiliaryFullEmbedding n e p he.2 (auxiliaryFromEnergyFull n e p he.2 u) = energyEmbedding (-p) u := by
  apply lp.ext
  funext m
  apply (physicalSector m).injective
  apply Lp.ext
  have ht := auxiliaryFullWeightedCoordinates_physical n m e p he.2
    (auxiliaryFromEnergyFull n e p he.2 u)
  have hc : auxiliaryWeightedCoordinates n e p he.2 (auxiliaryFromEnergyFull n e p he.2 u) =
      auxiliaryReverseAction n e p he.2 (energyCoordinates (-p) u) := by
    change auxiliaryWeightedCoordinates n e p he.2
      ((auxiliaryWeightedCoordinates n e p he.2).symm _) = _
    exact (auxiliaryWeightedCoordinates n e p he.2).apply_symm_apply _
  rw [hc] at ht
  have hu := energyEmbedding_weighted_ae (-p) u m
  have ha := auxiliaryReverseAction_ae n m e p he.2 (energyCoordinates (-p) u)
  filter_upwards [ht,hu,ha] with K ht hu ha
  simp only [smul_eq_mul] at hu ha
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (zero_lt_one.trans_le (auxiliaryWeight_ge_one n m e p he.2 K))))
  have hr : comparisonRatio (auxiliaryWeight n e p) (energyWeight (-p)) (Real.sqrt (5/4 : ℝ)) m K =
      auxiliaryWeight n e p m K / energyWeight (-p) m K :=
    min_eq_right ((div_le_iff₀ (zero_lt_one.trans_le (energyWeight_ge_one (-p) m K))).mpr
      (auxiliaryWeight_le_energyWeight n m e p he K))
  rw [ht,← ha,hr,← hu,Complex.ofReal_div]
  have hW : (energyWeight (-p) m K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (zero_lt_one.trans_le (energyWeight_ge_one (-p) m K)))
  field_simp [hW]

end Froehlich
