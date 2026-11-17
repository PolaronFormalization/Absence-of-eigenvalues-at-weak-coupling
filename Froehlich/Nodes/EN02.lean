import Froehlich.Nodes.EN01
import Froehlich.Nodes.BA01

/-! EN02: canonical momentum-change bounds and isolated one-particle coordinates.
The bounded coordinate-change construction and number-form comparison are still
being integrated; no pending proposition is installed as a hypothesis. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

def momentumChangeConstant (P Q : GW.Space) : ℝ := Real.sqrt (2 * (1 + ‖P - Q‖ ^ 2))

theorem energyWeight_change_sq (P Q : GW.Space) (n : ℕ) (k : GW.Fock.Coordinates n) :
    energyWeight P n k ^ 2 ≤ 2 * (1 + ‖P - Q‖ ^ 2) * energyWeight Q n k ^ 2 := by
  have ht : ‖totalMomentum n k - P‖ ≤ ‖totalMomentum n k - Q‖ + ‖P - Q‖ := by
    have h := norm_sub_le (totalMomentum n k - Q) (P - Q)
    have he : totalMomentum n k - Q - (P - Q) = totalMomentum n k - P := by module
    rwa [he] at h
  have hs : ‖totalMomentum n k - P‖ ^ 2 ≤
      2 * ‖totalMomentum n k - Q‖ ^ 2 + 2 * ‖P - Q‖ ^ 2 := by
    nlinarith [norm_nonneg (totalMomentum n k - P), norm_nonneg (totalMomentum n k - Q),
      norm_nonneg (P - Q), sq_nonneg (‖totalMomentum n k - Q‖ - ‖P - Q‖)]
  rw [energyWeight_sq, energyWeight_sq]
  unfold freeSymbol
  nlinarith [Nat.cast_nonneg (α := ℝ) n,
    mul_nonneg (sq_nonneg ‖P - Q‖) (freeSymbol_nonneg Q n k)]

def energyWeightRatio (P Q : GW.Space) (n : ℕ) (k : GW.Fock.Coordinates n) : ℝ :=
  energyWeight P n k / energyWeight Q n k

theorem energyWeightRatio_measurable (P Q : GW.Space) (n : ℕ) :
    Measurable (energyWeightRatio P Q n) :=
  (energyWeight_measurable P n).div (energyWeight_measurable Q n)

theorem energyWeightRatio_nonneg (P Q : GW.Space) (n : ℕ) (k : GW.Fock.Coordinates n) :
    0 ≤ energyWeightRatio P Q n k :=
  div_nonneg (zero_le_one.trans (energyWeight_ge_one P n k))
    (zero_le_one.trans (energyWeight_ge_one Q n k))

theorem energyWeightRatio_bound (P Q : GW.Space) (n : ℕ) (k : GW.Fock.Coordinates n) :
    energyWeightRatio P Q n k ≤ momentumChangeConstant P Q := by
  have hw : 0 < energyWeight Q n k := zero_lt_one.trans_le (energyWeight_ge_one Q n k)
  have hc : 0 ≤ momentumChangeConstant P Q := Real.sqrt_nonneg _
  have hcs : momentumChangeConstant P Q ^ 2 = 2 * (1 + ‖P - Q‖ ^ 2) :=
    Real.sq_sqrt (by positivity)
  unfold energyWeightRatio
  apply (div_le_iff₀ hw).mpr
  apply (sq_le_sq₀ (zero_le_one.trans (energyWeight_ge_one P n k)) (mul_nonneg hc hw.le)).mp
  rw [mul_pow, hcs]
  exact energyWeight_change_sq P Q n k

theorem energyWeightRatio_permutation (P Q : GW.Space) (n : ℕ)
    (τ : Equiv.Perm (Fin n)) (k : GW.Fock.Coordinates n) :
    energyWeightRatio P Q n (fun i => k (τ i)) = energyWeightRatio P Q n k := by
  simp only [energyWeightRatio, energyWeight_permutation]

/-- Isolated one-particle graph weight; the inherited full Fock weight has an
additional one. These spaces must not share Riesz representatives by fiat. -/
def oneParticleEnergyWeight (P k : GW.Space) : ℝ := Real.sqrt (1 + ‖k - P‖ ^ 2)

theorem oneParticleEnergyWeight_measurable (P : GW.Space) :
    Measurable (oneParticleEnergyWeight P) := by unfold oneParticleEnergyWeight; fun_prop

theorem oneParticleEnergyWeight_ge_one (P k : GW.Space) : 1 ≤ oneParticleEnergyWeight P k := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg ‖k - P‖]

abbrev OneParticleEnergySpace (P : GW.Space) :=
  GW.Spaces.WeightedL2 ℂ (oneParticleEnergyWeight P) (volume : Measure GW.Space)

def oneParticleEnergyEmbedding (P : GW.Space) : OneParticleEnergySpace P →L[ℂ] GW.OnePhonon :=
  GW.Spaces.WeightedL2.embed (oneParticleEnergyWeight_measurable P) (oneParticleEnergyWeight_ge_one P)

theorem oneParticleEnergyEmbedding_injective (P : GW.Space) :
    Function.Injective (oneParticleEnergyEmbedding P) :=
  GW.Spaces.WeightedL2.embed_injective (oneParticleEnergyWeight_measurable P) (oneParticleEnergyWeight_ge_one P)

theorem oneParticleEnergyEmbedding_norm_le (P : GW.Space) (f : OneParticleEnergySpace P) :
    ‖oneParticleEnergyEmbedding P f‖ ≤ ‖f‖ :=
  GW.Spaces.WeightedL2.embed_norm_le (oneParticleEnergyWeight_measurable P) (oneParticleEnergyWeight_ge_one P) f
/-- Restrict the retained bounded multiplier to the actual symmetric sector. -/
def boundedSymmetricMultiplier (n : ℕ) (m : GW.Fock.Coordinates n → ℂ)
    (hm : Measurable m) {C : ℝ} (hb : ∀ k, ‖m k‖ ≤ C)
    (hp : ∀ (τ : Equiv.Perm (Fin n)) k, m (fun i => k (τ i)) = m k) :
    GW.Fock.symmetricSector n →L[ℂ] GW.Fock.symmetricSector n := by
  let L := (GW.Analysis.boundedMultiplier m hm (Eventually.of_forall hb)).comp
    (GW.Fock.symmetricInclusion n).toContinuousLinearMap
  apply L.codRestrict (GW.Fock.symmetricSector n).toSubmodule
  intro u
  apply (GW.Fock.symmetricSector_mem_iff n _).mpr
  intro τ
  have hs := (GW.Fock.symmetricSector_mem_iff n _).mp u.property τ
  have he := GW.Analysis.boundedMultiplier_ae m hm (Eventually.of_forall hb)
    ((GW.Fock.symmetricInclusion n) u)
  filter_upwards [he, (GW.Fock.coordinatePermutation_preserving n τ).quasiMeasurePreserving.ae he, hs]
    with k hout hin hs
  simp only [GW.Fock.coordinatePermutation_eq] at hin
  change L u (fun i => k (τ i)) = L u k
  simp only [L, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  rw [← hin, ← hout, hp τ k]
  change (m k) • (u : GW.Fock.AmbientSector n) (fun i => k (τ i)) =
    (m k) • (u : GW.Fock.AmbientSector n) k
  rw [hs]

theorem boundedSymmetricMultiplier_norm (n : ℕ) (m : GW.Fock.Coordinates n → ℂ)
    (hm : Measurable m) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ k, ‖m k‖ ≤ C)
    (hp : ∀ (τ : Equiv.Perm (Fin n)) k, m (fun i => k (τ i)) = m k) :
    ‖boundedSymmetricMultiplier n m hm hb hp‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro u
  change ‖GW.Analysis.boundedMultiplier m hm (Eventually.of_forall hb)
    ((GW.Fock.symmetricInclusion n) u)‖ ≤ C * ‖u‖
  have h := (GW.Analysis.boundedMultiplier m hm (Eventually.of_forall hb)).le_opNorm
    ((GW.Fock.symmetricInclusion n) u)
  exact h.trans (by
    rw [LinearIsometry.norm_map]
    exact mul_le_mul_of_nonneg_right
      (GW.Analysis.boundedMultiplier_opNorm_le m hm hC (Eventually.of_forall hb)) (norm_nonneg _))

theorem energyWeightRatio_complex_bound (P Q : GW.Space) (n : ℕ) (k : GW.Fock.Coordinates n) :
    ‖(energyWeightRatio P Q n k : ℂ)‖ ≤ momentumChangeConstant P Q := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (energyWeightRatio_nonneg P Q n k)]
  exact energyWeightRatio_bound P Q n k

def sectorEnergyChange (P Q : GW.Space) : ∀ n, GW.Fock.Sector n →L[ℂ] GW.Fock.Sector n
  | 0 => (energyWeightRatio P Q 0 0 : ℂ) • ContinuousLinearMap.id ℂ ℂ
  | n+1 => boundedSymmetricMultiplier (n+1) (fun k => (energyWeightRatio P Q (n+1) k : ℂ))
      (Complex.continuous_ofReal.measurable.comp (energyWeightRatio_measurable P Q (n+1)))
      (energyWeightRatio_complex_bound P Q (n+1))
      (fun τ k => congrArg Complex.ofReal (energyWeightRatio_permutation P Q (n+1) τ k))

theorem sectorEnergyChange_norm (P Q : GW.Space) (n : ℕ) :
    ‖sectorEnergyChange P Q n‖ ≤ momentumChangeConstant P Q := by
  cases n with
  | zero =>
    change ‖(energyWeightRatio P Q 0 0 : ℂ) • ContinuousLinearMap.id ℂ ℂ‖ ≤ _
    rw [norm_smul, ContinuousLinearMap.norm_id, mul_one]
    exact energyWeightRatio_complex_bound P Q 0 0
  | succ n =>
    exact boundedSymmetricMultiplier_norm (n+1) (fun k => (energyWeightRatio P Q (n+1) k : ℂ))
      (Complex.continuous_ofReal.measurable.comp (energyWeightRatio_measurable P Q (n+1)))
      (Real.sqrt_nonneg _) (energyWeightRatio_complex_bound P Q (n+1))
      (fun τ k => congrArg Complex.ofReal (energyWeightRatio_permutation P Q (n+1) τ k))

/-- Coordinates preserving the physical vector: target momentum P, source Q. -/
def energyCoordinateChange (P Q : GW.Space) : EnergySpace Q →L[ℂ] EnergySpace P :=
  (energyCoordinates P).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((GW.Spaces.diagonalMap (sectorEnergyChange P Q) (Real.sqrt_nonneg _) (sectorEnergyChange_norm P Q)).comp
      (energyCoordinates Q).toLinearIsometry.toContinuousLinearMap)

theorem energyCoordinateChange_norm_le (P Q : GW.Space) :
    ‖energyCoordinateChange P Q‖ ≤ momentumChangeConstant P Q := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  change ‖(energyCoordinates P).symm (GW.Spaces.diagonalMap (sectorEnergyChange P Q)
    (Real.sqrt_nonneg _) (sectorEnergyChange_norm P Q) (energyCoordinates Q x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  change ‖GW.Spaces.diagonalLinear (sectorEnergyChange P Q)
    (sectorEnergyChange_norm P Q) (energyCoordinates Q x)‖ ≤ _
  have h := GW.Spaces.diagonal_norm_bound (sectorEnergyChange P Q) (Real.sqrt_nonneg _)
    (sectorEnergyChange_norm P Q) (energyCoordinates Q x)
  rw [(energyCoordinates Q).norm_map x] at h
  exact h

theorem boundedSymmetricMultiplier_ae (n : ℕ) (m : GW.Fock.Coordinates n → ℂ)
    (hm : Measurable m) {C : ℝ} (hb : ∀ k, ‖m k‖ ≤ C)
    (hp : ∀ (τ : Equiv.Perm (Fin n)) k, m (fun i => k (τ i)) = m k)
    (u : GW.Fock.symmetricSector n) :
    (fun k => m k • (u : GW.Fock.AmbientSector n) k) =ᵐ[GW.Fock.sectorMeasure n]
      (boundedSymmetricMultiplier n m hm hb hp u : GW.Fock.AmbientSector n) := by
  have h := GW.Analysis.boundedMultiplier_ae m hm (Eventually.of_forall hb)
    ((GW.Fock.symmetricInclusion n) u)
  change (fun k => m k • ((GW.Fock.symmetricInclusion n) u) k) =ᵐ[GW.Fock.sectorMeasure n]
    GW.Analysis.boundedMultiplier m hm (Eventually.of_forall hb) ((GW.Fock.symmetricInclusion n) u)
  exact h

theorem sectorEnergyChange_ae (P Q : GW.Space) (n : ℕ) (u : GW.Fock.Sector n) :
    (fun k => (energyWeightRatio P Q n k : ℂ) • physicalSector n u k) =ᵐ[GW.Fock.sectorMeasure n]
      physicalSector n (sectorEnergyChange P Q n u) := by
  cases n with
  | zero =>
    filter_upwards [GW.Fock.vacuumAdapter_ae u,
      GW.Fock.vacuumAdapter_ae (sectorEnergyChange P Q 0 u)] with k hu hv
    change (energyWeightRatio P Q 0 k : ℂ) * GW.Fock.vacuumAdapterIsometry u k =
      GW.Fock.vacuumAdapterIsometry (sectorEnergyChange P Q 0 u) k
    rw [hu, hv, show k = 0 from Subsingleton.elim _ _]
    rfl
  | succ n =>
    exact boundedSymmetricMultiplier_ae (n+1) (fun k => (energyWeightRatio P Q (n+1) k : ℂ))
      (Complex.continuous_ofReal.measurable.comp (energyWeightRatio_measurable P Q (n+1)))
      (energyWeightRatio_complex_bound P Q (n+1))
      (fun τ k => congrArg Complex.ofReal (energyWeightRatio_permutation P Q (n+1) τ k)) u

theorem energyCoordinateChange_apply (P Q : GW.Space) (x : EnergySpace Q) (n : ℕ) :
    energyCoordinates P (energyCoordinateChange P Q x) n =
      sectorEnergyChange P Q n (energyCoordinates Q x n) := by
  change energyCoordinates P ((energyCoordinates P).symm
    (GW.Spaces.diagonalMap (sectorEnergyChange P Q) (Real.sqrt_nonneg _)
      (sectorEnergyChange_norm P Q) (energyCoordinates Q x))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem energyCoordinateChange_intertwines (P Q : GW.Space) (x : EnergySpace Q) :
    energyEmbedding P (energyCoordinateChange P Q x) = energyEmbedding Q x := by
  apply lp.ext
  funext n
  apply (physicalSector n).injective
  apply Lp.ext
  have hp := energyEmbedding_weighted_ae P (energyCoordinateChange P Q x) n
  rw [energyCoordinateChange_apply] at hp
  filter_upwards [hp, energyEmbedding_weighted_ae Q x n,
    sectorEnergyChange_ae P Q n (energyCoordinates Q x n)] with k hp hq hi
  simp only [smul_eq_mul] at hp hq hi
  have hn : energyWeight Q n k ≠ 0 := ne_of_gt (zero_lt_one.trans_le (energyWeight_ge_one Q n k))
  have hr : energyWeightRatio P Q n k * energyWeight Q n k = energyWeight P n k := by
    unfold energyWeightRatio
    exact div_mul_cancel₀ _ hn
  have hw : (energyWeight P n k : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans_le (energyWeight_ge_one P n k)))
  apply mul_left_cancel₀ hw
  calc
    (energyWeight P n k : ℂ) * physicalSector n (energyEmbedding P (energyCoordinateChange P Q x) n) k =
        physicalSector n (sectorEnergyChange P Q n (energyCoordinates Q x n)) k := hp
    _ = (energyWeightRatio P Q n k : ℂ) * physicalSector n (energyCoordinates Q x n) k := hi.symm
    _ = ((energyWeightRatio P Q n k : ℂ) * (energyWeight Q n k : ℂ)) *
        physicalSector n (energyEmbedding Q x n) k := by rw [← hq, mul_assoc]
    _ = (energyWeight P n k : ℂ) * physicalSector n (energyEmbedding Q x n) k := by
      rw [← Complex.ofReal_mul, hr]

theorem energyCoordinateChange_inverse (P Q : GW.Space) :
    (energyCoordinateChange Q P).comp (energyCoordinateChange P Q) = .id ℂ (EnergySpace Q) := by
  apply ContinuousLinearMap.ext
  intro x
  apply (energyEmbedding_injective Q)
  change energyEmbedding Q (energyCoordinateChange Q P (energyCoordinateChange P Q x)) = energyEmbedding Q x
  rw [energyCoordinateChange_intertwines, energyCoordinateChange_intertwines]

theorem energyEmbedding_ranges_eq (P Q : GW.Space) :
    Set.range (energyEmbedding P) = Set.range (energyEmbedding Q) := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨energyCoordinateChange Q P x, energyCoordinateChange_intertwines Q P x⟩
  · rintro ⟨x, rfl⟩
    exact ⟨energyCoordinateChange P Q x, energyCoordinateChange_intertwines P Q x⟩

theorem energyCoordinateChange_norm_sq (P Q : GW.Space) :
    ‖energyCoordinateChange P Q‖ ^ 2 ≤ 2 * (1 + ‖P - Q‖ ^ 2) := by
  have h := (sq_le_sq₀ (norm_nonneg (energyCoordinateChange P Q))
    (Real.sqrt_nonneg (2 * (1 + ‖P - Q‖ ^ 2)))).mpr (energyCoordinateChange_norm_le P Q)
  exact h.trans_eq (Real.sq_sqrt (by positivity))


/-- Particle selection on weighted coordinates, preserving exactly that selection physically. -/
def energySectorProjection (P : GW.Space) (m : ℕ) : EnergySpace P →L[ℂ] EnergySpace P :=
  (energyCoordinates P).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((sectorProjection m).comp (energyCoordinates P).toLinearIsometry.toContinuousLinearMap)

theorem energySectorProjection_apply (P : GW.Space) (m n : ℕ) (x : EnergySpace P) :
    energyCoordinates P (energySectorProjection P m x) n =
      if n = m then energyCoordinates P x n else 0 := by
  change (lp.single 2 m (energyCoordinates P x m)) n = _
  by_cases h : n = m
  · subst n
    simp
  · simp [lp.single_apply, h, Ne.symm h]

theorem energySectorProjection_norm_le (P : GW.Space) (m : ℕ) (x : EnergySpace P) :
    ‖energySectorProjection P m x‖ ≤ ‖x‖ := by
  change ‖sectorProjection m (energyCoordinates P x)‖ ≤ ‖x‖
  exact (sectorProjection_norm_le m _).trans_eq ((energyCoordinates P).norm_map x)

theorem energySectorProjection_intertwines (P : GW.Space) (m : ℕ) (x : EnergySpace P) :
    energyEmbedding P (energySectorProjection P m x) = sectorProjection m (energyEmbedding P x) := by
  apply lp.ext
  funext n
  rw [energyEmbedding_apply, energySectorProjection_apply]
  change sectorEnergyEmbedding P n (if n = m then energyCoordinates P x n else 0) =
    (lp.single 2 m (energyEmbedding P x m)) n
  by_cases h : n = m
  · subst n
    simp only [ite_true, lp.single_apply, Pi.single_eq_same, energyEmbedding_apply]
  · simp [h, Ne.symm h, lp.single_apply]

def energyLowProjection (P : GW.Space) (m : ℕ) : EnergySpace P →L[ℂ] EnergySpace P :=
  (energyCoordinates P).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((lowSectorProjection m).comp (energyCoordinates P).toLinearIsometry.toContinuousLinearMap)

theorem energyLowProjection_apply (P : GW.Space) (m n : ℕ) (x : EnergySpace P) :
    energyCoordinates P (energyLowProjection P m x) n =
      if n ≤ m then energyCoordinates P x n else 0 :=
  GW.Fock.cutoff_apply GW.Fock.Sector m (energyCoordinates P x) n

theorem energyLowProjection_norm_le (P : GW.Space) (m : ℕ) (x : EnergySpace P) :
    ‖energyLowProjection P m x‖ ≤ ‖x‖ := by
  change ‖lowSectorProjection m (energyCoordinates P x)‖ ≤ ‖x‖
  exact (lowSectorProjection_norm_le m _).trans_eq ((energyCoordinates P).norm_map x)

theorem energyLowProjection_intertwines (P : GW.Space) (m : ℕ) (x : EnergySpace P) :
    energyEmbedding P (energyLowProjection P m x) = lowSectorProjection m (energyEmbedding P x) := by
  apply lp.ext
  funext n
  rw [energyEmbedding_apply, energyLowProjection_apply]
  change sectorEnergyEmbedding P n (if n ≤ m then energyCoordinates P x n else 0) =
    GW.Fock.cutoff GW.Fock.Sector m (energyEmbedding P x) n
  rw [GW.Fock.cutoff_apply]
  split_ifs <;> simp only [map_zero, energyEmbedding_apply]

def energyHighProjection (P : GW.Space) (m : ℕ) : EnergySpace P →L[ℂ] EnergySpace P :=
  (energyCoordinates P).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((highSectorProjection m).comp (energyCoordinates P).toLinearIsometry.toContinuousLinearMap)

theorem energyHighProjection_apply (P : GW.Space) (m n : ℕ) (x : EnergySpace P) :
    energyCoordinates P (energyHighProjection P m x) n =
      if m ≤ n then energyCoordinates P x n else 0 :=
  highSectorProjection_apply m (energyCoordinates P x) n

theorem energyHighProjection_norm_le (P : GW.Space) (m : ℕ) (x : EnergySpace P) :
    ‖energyHighProjection P m x‖ ≤ ‖x‖ := by
  change ‖highSectorProjection m (energyCoordinates P x)‖ ≤ ‖x‖
  exact (highSectorProjection_norm_le m _).trans_eq ((energyCoordinates P).norm_map x)

theorem energyHighProjection_intertwines (P : GW.Space) (m : ℕ) (x : EnergySpace P) :
    energyEmbedding P (energyHighProjection P m x) = highSectorProjection m (energyEmbedding P x) := by
  apply lp.ext
  funext n
  rw [energyEmbedding_apply, energyHighProjection_apply, highSectorProjection_apply]
  split_ifs <;> simp only [map_zero, energyEmbedding_apply]

theorem sectorEnergyEmbedding_weighted_ae (P : GW.Space) (n : ℕ) (u : GW.Fock.Sector n) :
    (fun k => (energyWeight P n k : ℂ) • physicalSector n (sectorEnergyEmbedding P n u) k)
      =ᵐ[GW.Fock.sectorMeasure n] physicalSector n u := by
  have h := energyEmbedding_weighted_ae P
    ((energyCoordinates P).symm (lp.single 2 n u)) n
  simpa only [energyEmbedding_apply, LinearIsometryEquiv.apply_symm_apply, lp.single_apply,
    Pi.single_eq_same] using h


theorem energySectorProjection_pairing (P : GW.Space) (m : ℕ) (x y : EnergySpace P) :
    ⟪energySectorProjection P m x, y⟫_ℂ = ⟪x, energySectorProjection P m y⟫_ℂ :=
  sectorProjection_pairing m (energyCoordinates P x) (energyCoordinates P y)

theorem energyLowProjection_pairing (P : GW.Space) (m : ℕ) (x y : EnergySpace P) :
    ⟪energyLowProjection P m x, y⟫_ℂ = ⟪x, energyLowProjection P m y⟫_ℂ :=
  lowSectorProjection_pairing m (energyCoordinates P x) (energyCoordinates P y)

theorem energyHighProjection_pairing (P : GW.Space) (m : ℕ) (x y : EnergySpace P) :
    ⟪energyHighProjection P m x, y⟫_ℂ = ⟪x, energyHighProjection P m y⟫_ℂ :=
  highSectorProjection_pairing m (energyCoordinates P x) (energyCoordinates P y)

theorem energySectorProjection_adjoint (P : GW.Space) (m : ℕ) :
    (energySectorProjection P m).adjoint = energySectorProjection P m := by
  apply Eq.symm
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr (energySectorProjection_pairing P m)

theorem energyLowProjection_adjoint (P : GW.Space) (m : ℕ) :
    (energyLowProjection P m).adjoint = energyLowProjection P m := by
  apply Eq.symm
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr (energyLowProjection_pairing P m)

theorem energyHighProjection_adjoint (P : GW.Space) (m : ℕ) :
    (energyHighProjection P m).adjoint = energyHighProjection P m := by
  apply Eq.symm
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr (energyHighProjection_pairing P m)

end Froehlich
