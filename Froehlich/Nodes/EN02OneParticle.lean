import Froehlich.Nodes.EN02

/-! The isolated and inherited one-particle graph norms in EN02. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Froehlich

def oneParticleInheritedWeight (P k : GW.Space) : ℝ := Real.sqrt (2 + ‖k-P‖^2)

theorem oneParticleInheritedWeight_measurable (P : GW.Space) :
    Measurable (oneParticleInheritedWeight P) := by unfold oneParticleInheritedWeight; fun_prop

theorem oneParticleWeight_comparison (P k : GW.Space) :
    oneParticleEnergyWeight P k ≤ oneParticleInheritedWeight P k ∧
      oneParticleInheritedWeight P k ≤ Real.sqrt 2 * oneParticleEnergyWeight P k := by
  constructor
  · unfold oneParticleEnergyWeight oneParticleInheritedWeight
    apply Real.sqrt_le_sqrt
    linarith
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg ‖k-P‖]

theorem oneParticleInheritedWeight_ge_one (P k : GW.Space) : 1 ≤ oneParticleInheritedWeight P k :=
  (oneParticleEnergyWeight_ge_one P k).trans (oneParticleWeight_comparison P k).1

abbrev OneParticleInheritedSpace (P : GW.Space) :=
  GW.Spaces.WeightedL2 ℂ (oneParticleInheritedWeight P) (volume : Measure GW.Space)

def oneParticleInheritedEmbedding (P : GW.Space) : OneParticleInheritedSpace P →L[ℂ] GW.OnePhonon :=
  GW.Spaces.WeightedL2.embed (oneParticleInheritedWeight_measurable P) (oneParticleInheritedWeight_ge_one P)

/-- Bounded scalar weighted-coordinate change on the actual one-particle L² space. -/
def oneParticleWeightedChange (w v : GW.Space → ℝ) (hw : Measurable w) (hv : Measurable v)
    (hw1 : ∀ k, 1 ≤ w k) (hv1 : ∀ k, 1 ≤ v k)
    {C : ℝ} (hb : ∀ k, w k / v k ≤ C) :
    GW.Spaces.WeightedL2 ℂ v volume →L[ℂ] GW.Spaces.WeightedL2 ℂ w volume :=
  GW.Analysis.boundedMultiplier (fun k => ((w k / v k : ℝ) : ℂ))
    (Complex.continuous_ofReal.measurable.comp (hw.div hv))
    (Eventually.of_forall (fun k => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg
        (zero_le_one.trans (hw1 k)) (zero_le_one.trans (hv1 k)))]
      exact hb k))

theorem oneParticleWeightedChange_intertwines
    (w v : GW.Space → ℝ) (hw : Measurable w) (hv : Measurable v)
    (hw1 : ∀ k, 1 ≤ w k) (hv1 : ∀ k, 1 ≤ v k)
    {C : ℝ} (hb : ∀ k, w k / v k ≤ C) (x : GW.Spaces.WeightedL2 ℂ v volume) :
    GW.Spaces.WeightedL2.embed hw hw1 (oneParticleWeightedChange w v hw hv hw1 hv1 hb x) =
      GW.Spaces.WeightedL2.embed hv hv1 x := by
  apply Lp.ext
  have hi := GW.Analysis.boundedMultiplier_ae (fun k => ((w k / v k : ℝ) : ℂ))
    (Complex.continuous_ofReal.measurable.comp (hw.div hv))
    (Eventually.of_forall (fun k => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg
        (zero_le_one.trans (hw1 k)) (zero_le_one.trans (hv1 k)))]
      exact hb k)) x
  filter_upwards [GW.Spaces.WeightedL2.weighted_embed_ae hw hw1
    (oneParticleWeightedChange w v hw hv hw1 hv1 hb x),
    GW.Spaces.WeightedL2.weighted_embed_ae hv hv1 x, hi] with k hk hl hi
  change (w k : ℂ) * _ = _ at hk
  change (v k : ℂ) * _ = _ at hl
  change ((w k / v k : ℝ) : ℂ) * (GW.Spaces.WeightedL2.coordinates x) k =
    (GW.Spaces.WeightedL2.coordinates (oneParticleWeightedChange w v hw hv hw1 hv1 hb x)) k at hi
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans_le (hw1 k))))
  rw [hk]
  change (GW.Spaces.WeightedL2.coordinates (oneParticleWeightedChange w v hw hv hw1 hv1 hb x)) k = _
  rw [← hi, ← hl]
  push_cast
  field_simp [ne_of_gt (zero_lt_one.trans_le (hv1 k))]


theorem oneParticleWeightedChange_norm
    (w v : GW.Space → ℝ) (hw : Measurable w) (hv : Measurable v)
    (hw1 : ∀ k, 1 ≤ w k) (hv1 : ∀ k, 1 ≤ v k)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ k, w k / v k ≤ C) :
    ‖oneParticleWeightedChange w v hw hv hw1 hv1 hb‖ ≤ C := by
  exact GW.Analysis.boundedMultiplier_opNorm_le
    (fun k => ((w k / v k : ℝ) : ℂ))
    (Complex.continuous_ofReal.measurable.comp (hw.div hv)) hC
    (Eventually.of_forall (fun k => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg
        (zero_le_one.trans (hw1 k)) (zero_le_one.trans (hv1 k)))]
      exact hb k))

theorem isolatedToInherited_ratio (P k : GW.Space) :
    oneParticleInheritedWeight P k / oneParticleEnergyWeight P k ≤ Real.sqrt 2 :=
  (div_le_iff₀ (zero_lt_one.trans_le (oneParticleEnergyWeight_ge_one P k))).mpr
    (oneParticleWeight_comparison P k).2

theorem inheritedToIsolated_ratio (P k : GW.Space) :
    oneParticleEnergyWeight P k / oneParticleInheritedWeight P k ≤ 1 :=
  (div_le_one (zero_lt_one.trans_le (oneParticleInheritedWeight_ge_one P k))).mpr
    (oneParticleWeight_comparison P k).1

def isolatedToInherited (P : GW.Space) : OneParticleEnergySpace P →L[ℂ] OneParticleInheritedSpace P :=
  oneParticleWeightedChange _ _ (oneParticleInheritedWeight_measurable P)
    (oneParticleEnergyWeight_measurable P) (oneParticleInheritedWeight_ge_one P)
    (oneParticleEnergyWeight_ge_one P) (isolatedToInherited_ratio P)

def inheritedToIsolated (P : GW.Space) : OneParticleInheritedSpace P →L[ℂ] OneParticleEnergySpace P :=
  oneParticleWeightedChange _ _ (oneParticleEnergyWeight_measurable P)
    (oneParticleInheritedWeight_measurable P) (oneParticleEnergyWeight_ge_one P)
    (oneParticleInheritedWeight_ge_one P) (inheritedToIsolated_ratio P)

theorem isolatedToInherited_intertwines (P : GW.Space) (f : OneParticleEnergySpace P) :
    oneParticleInheritedEmbedding P (isolatedToInherited P f) = oneParticleEnergyEmbedding P f :=
  oneParticleWeightedChange_intertwines _ _ _ _ _ _ _ f

theorem inheritedToIsolated_intertwines (P : GW.Space) (f : OneParticleInheritedSpace P) :
    oneParticleEnergyEmbedding P (inheritedToIsolated P f) = oneParticleInheritedEmbedding P f :=
  oneParticleWeightedChange_intertwines _ _ _ _ _ _ _ f

theorem oneParticleWeightChange_inverse (P : GW.Space) :
    (inheritedToIsolated P).comp (isolatedToInherited P) = .id ℂ (OneParticleEnergySpace P) ∧
    (isolatedToInherited P).comp (inheritedToIsolated P) = .id ℂ (OneParticleInheritedSpace P) := by
  constructor
  · apply ContinuousLinearMap.ext
    intro f
    apply oneParticleEnergyEmbedding_injective P
    change oneParticleEnergyEmbedding P (inheritedToIsolated P (isolatedToInherited P f)) = _
    rw [inheritedToIsolated_intertwines, isolatedToInherited_intertwines]
    rfl
  · apply ContinuousLinearMap.ext
    intro f
    apply GW.Spaces.WeightedL2.embed_injective (oneParticleInheritedWeight_measurable P)
      (oneParticleInheritedWeight_ge_one P)
    change oneParticleInheritedEmbedding P (isolatedToInherited P (inheritedToIsolated P f)) = _
    rw [isolatedToInherited_intertwines, inheritedToIsolated_intertwines]
    rfl

theorem oneParticleEnergyEmbedding_ranges_eq (P : GW.Space) :
    Set.range (oneParticleEnergyEmbedding P) = Set.range (oneParticleInheritedEmbedding P) := by
  ext f
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨isolatedToInherited P x, isolatedToInherited_intertwines P x⟩
  · rintro ⟨x, rfl⟩
    exact ⟨inheritedToIsolated P x, inheritedToIsolated_intertwines P x⟩

theorem isolatedToInherited_norm (P : GW.Space) : ‖isolatedToInherited P‖ ≤ Real.sqrt 2 :=
  oneParticleWeightedChange_norm _ _ _ _ _ _ (Real.sqrt_nonneg _) _

theorem inheritedToIsolated_norm (P : GW.Space) : ‖inheritedToIsolated P‖ ≤ 1 :=
  oneParticleWeightedChange_norm _ _ _ _ _ _ zero_le_one _

theorem oneParticleNorm_comparison (P : GW.Space) (f : OneParticleEnergySpace P) :
    ‖f‖^2 ≤ ‖isolatedToInherited P f‖^2 ∧ ‖isolatedToInherited P f‖^2 ≤ 2 * ‖f‖^2 := by
  have hi := congrArg (fun L : OneParticleEnergySpace P →L[ℂ] OneParticleEnergySpace P => L f)
    (oneParticleWeightChange_inverse P).1
  have hl : ‖f‖ ≤ ‖isolatedToInherited P f‖ := by
    calc
      _ = ‖inheritedToIsolated P (isolatedToInherited P f)‖ := congrArg norm hi.symm
      _ ≤ ‖inheritedToIsolated P‖ * ‖isolatedToInherited P f‖ := (inheritedToIsolated P).le_opNorm _
      _ ≤ 1 * ‖isolatedToInherited P f‖ :=
        mul_le_mul_of_nonneg_right (inheritedToIsolated_norm P) (norm_nonneg _)
      _ = _ := one_mul _
  have hu : ‖isolatedToInherited P f‖ ≤ Real.sqrt 2 * ‖f‖ :=
    ((isolatedToInherited P).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (isolatedToInherited_norm P) (norm_nonneg _))
  constructor
  · exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hl
  · have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg f))).mpr hu
    simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using hs

theorem energyWeight_one (P : GW.Space) (k : GW.Fock.Coordinates 1) :
    energyWeight P 1 k = oneParticleInheritedWeight P (k 0) := by
  unfold energyWeight freeSymbol totalMomentum oneParticleInheritedWeight
  simp only [Fin.sum_univ_one, Nat.cast_one]
  congr 1
  ring


/-- The inherited one-particle embedding is the actual sector-one restriction
of the full energy embedding, in the prescribed GW one-particle coordinates. -/
theorem sectorEnergyEmbedding_oneParticle (P : GW.Space) (f : OneParticleInheritedSpace P) :
    sectorEnergyEmbedding P 1 (oneParticleCoordinate (GW.Spaces.WeightedL2.coordinates f)) =
      oneParticleCoordinate (oneParticleInheritedEmbedding P f) := by
  apply (physicalSector 1).injective
  apply Lp.ext
  have hf : physicalSector 1 (oneParticleCoordinate (GW.Spaces.WeightedL2.coordinates f)) =ᵐ[GW.Fock.sectorMeasure 1]
      (fun K => GW.Spaces.WeightedL2.coordinates f (K 0)) := by
    change GW.Fock.sectorInclusion 0 (oneParticleCoordinate (GW.Spaces.WeightedL2.coordinates f)) =ᵐ[_] _
    rw [oneParticleCoordinate_representative]
    exact Lp.coeFn_compMeasurePreserving _ GW.Fock.oneBosonCoordinate_preserving
  have hg : physicalSector 1 (oneParticleCoordinate (oneParticleInheritedEmbedding P f)) =ᵐ[GW.Fock.sectorMeasure 1]
      (fun K => oneParticleInheritedEmbedding P f (K 0)) := by
    change GW.Fock.sectorInclusion 0 (oneParticleCoordinate (oneParticleInheritedEmbedding P f)) =ᵐ[_] _
    rw [oneParticleCoordinate_representative]
    exact Lp.coeFn_compMeasurePreserving _ GW.Fock.oneBosonCoordinate_preserving
  have hw := GW.Fock.oneBosonCoordinate_preserving.quasiMeasurePreserving.ae
    (GW.Spaces.WeightedL2.weighted_embed_ae (oneParticleInheritedWeight_measurable P)
      (oneParticleInheritedWeight_ge_one P) f)
  filter_upwards [sectorEnergyEmbedding_weighted_ae P 1 (oneParticleCoordinate (GW.Spaces.WeightedL2.coordinates f)),
    hf, hg, hw] with K he hf hg hw
  simp only [smul_eq_mul] at he hw
  rw [energyWeight_one] at he
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (zero_lt_one.trans_le (oneParticleInheritedWeight_ge_one P (K 0)))))
  calc
    _ = physicalSector 1 (oneParticleCoordinate (GW.Spaces.WeightedL2.coordinates f)) K := he
    _ = GW.Spaces.WeightedL2.coordinates f (K 0) := hf
    _ = (oneParticleInheritedWeight P (K 0) : ℂ) * oneParticleInheritedEmbedding P f (K 0) := hw.symm
    _ = _ := congrArg ((oneParticleInheritedWeight P (K 0) : ℂ) * ·) hg.symm

def oneParticleInheritedFockLift (P : GW.Space) : OneParticleInheritedSpace P →L[ℂ] EnergySpace P :=
  (energyCoordinates P).symm.toLinearIsometry.toContinuousLinearMap.comp
    (oneParticleInclusion.comp GW.Spaces.WeightedL2.coordinates.toLinearIsometry.toContinuousLinearMap)

theorem oneParticleInheritedFockLift_norm (P : GW.Space) (f : OneParticleInheritedSpace P) :
    ‖oneParticleInheritedFockLift P f‖ = ‖f‖ := by
  change ‖(energyCoordinates P).symm (oneParticleInclusion (GW.Spaces.WeightedL2.coordinates f))‖ = _
  rw [LinearIsometryEquiv.norm_map, oneParticleInclusion_norm, LinearIsometryEquiv.norm_map]

theorem oneParticleInheritedFockLift_intertwines (P : GW.Space) (f : OneParticleInheritedSpace P) :
    energyEmbedding P (oneParticleInheritedFockLift P f) =
      oneParticleInclusion (oneParticleInheritedEmbedding P f) := by
  apply lp.ext
  funext n
  rw [energyEmbedding_apply]
  change sectorEnergyEmbedding P n (oneParticleInclusion (GW.Spaces.WeightedL2.coordinates f) n) = _
  rw [oneParticleInclusion_apply, oneParticleInclusion_apply]
  by_cases h : n = 1
  · subst n
    rw [lp.single_apply_self, lp.single_apply_self]
    exact sectorEnergyEmbedding_oneParticle P f
  · rw [lp.single_apply_ne _ _ _ h, lp.single_apply_ne _ _ _ h, map_zero]


/-- The inherited energy coordinate of the actual one-particle projection. -/
def oneParticleInheritedExtraction (P : GW.Space) : EnergySpace P →L[ℂ] OneParticleInheritedSpace P :=
  GW.Spaces.WeightedL2.coordinates.symm.toLinearIsometry.toContinuousLinearMap.comp
    (oneParticleExtraction.comp (energyCoordinates P).toLinearIsometry.toContinuousLinearMap)

theorem oneParticleInheritedExtraction_norm_le (P : GW.Space) (x : EnergySpace P) :
    ‖oneParticleInheritedExtraction P x‖ ≤ ‖x‖ := by
  change ‖GW.Spaces.WeightedL2.coordinates.symm
    (oneParticleCoordinate.symm (energyCoordinates P x 1))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  exact (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (energyCoordinates P x) 1).trans_eq
    ((energyCoordinates P).norm_map x)

def oneParticleEnergyProjection (P : GW.Space) : EnergySpace P →L[ℂ] OneParticleEnergySpace P :=
  (inheritedToIsolated P).comp (oneParticleInheritedExtraction P)

theorem oneParticleEnergyProjection_norm_le (P : GW.Space) (x : EnergySpace P) :
    ‖oneParticleEnergyProjection P x‖ ≤ ‖x‖ := by
  change ‖inheritedToIsolated P (oneParticleInheritedExtraction P x)‖ ≤ _
  calc
    _ ≤ ‖inheritedToIsolated P‖ * ‖oneParticleInheritedExtraction P x‖ := (inheritedToIsolated P).le_opNorm _
    _ ≤ 1 * ‖oneParticleInheritedExtraction P x‖ :=
      mul_le_mul_of_nonneg_right (inheritedToIsolated_norm P) (norm_nonneg _)
    _ ≤ ‖x‖ := by simpa only [one_mul] using oneParticleInheritedExtraction_norm_le P x

theorem oneParticleEnergyProjection_intertwines (P : GW.Space) (x : EnergySpace P) :
    oneParticleEnergyEmbedding P (oneParticleEnergyProjection P x) =
      oneParticleExtraction (energyEmbedding P x) := by
  change oneParticleEnergyEmbedding P (inheritedToIsolated P (oneParticleInheritedExtraction P x)) = _
  rw [inheritedToIsolated_intertwines]
  apply oneParticleCoordinate.injective
  rw [oneParticleExtraction_apply, LinearIsometryEquiv.apply_symm_apply,
    ← sectorEnergyEmbedding_oneParticle]
  change sectorEnergyEmbedding P 1
    (oneParticleCoordinate (oneParticleCoordinate.symm (energyCoordinates P x 1))) = energyEmbedding P x 1
  rw [LinearIsometryEquiv.apply_symm_apply, energyEmbedding_apply]

end Froehlich
