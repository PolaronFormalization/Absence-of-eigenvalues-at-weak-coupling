import Froehlich.Nodes.GW01
import GW.Spaces.WeightedCarrier

/-! EN01: actual fiber weights and their bounded reciprocal maps.
The carrier is a named copy of the canonical GW Hilbert sum. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal

namespace Froehlich

def totalMomentum (n : ℕ) (k : GW.Fock.Coordinates n) : GW.Space := ∑ i, k i

def freeSymbol (P : GW.Space) (n : ℕ) (k : GW.Fock.Coordinates n) : ℝ :=
  ‖totalMomentum n k - P‖ ^ 2 + (n : ℝ)

def energyWeight (P : GW.Space) (n : ℕ) (k : GW.Fock.Coordinates n) : ℝ :=
  Real.sqrt (1 + freeSymbol P n k)

def operatorGraphWeight (P : GW.Space) (n : ℕ) (k : GW.Fock.Coordinates n) : ℝ :=
  Real.sqrt (1 + freeSymbol P n k ^ 2)

theorem totalMomentum_permutation (n : ℕ) (τ : Equiv.Perm (Fin n))
    (k : GW.Fock.Coordinates n) : totalMomentum n (fun i => k (τ i)) = totalMomentum n k := by
  exact Equiv.sum_comp τ k

theorem totalMomentum_measurable (n : ℕ) : Measurable (totalMomentum n) := by
  unfold totalMomentum
  fun_prop

theorem freeSymbol_measurable (P : GW.Space) (n : ℕ) : Measurable (freeSymbol P n) :=
  (((totalMomentum_measurable n).sub measurable_const).norm.pow_const 2).add measurable_const

theorem freeSymbol_nonneg (P : GW.Space) (n : ℕ) (k : GW.Fock.Coordinates n) :
    0 ≤ freeSymbol P n k := by unfold freeSymbol; positivity

theorem energyWeight_measurable (P : GW.Space) (n : ℕ) : Measurable (energyWeight P n) :=
  (measurable_const.add (freeSymbol_measurable P n)).sqrt

theorem operatorGraphWeight_measurable (P : GW.Space) (n : ℕ) :
    Measurable (operatorGraphWeight P n) :=
  (measurable_const.add ((freeSymbol_measurable P n).pow_const 2)).sqrt

theorem energyWeight_ge_one (P : GW.Space) (n : ℕ) (k : GW.Fock.Coordinates n) :
    1 ≤ energyWeight P n k := by
  apply Real.le_sqrt_of_sq_le
  have h := freeSymbol_nonneg P n k
  linarith

theorem operatorGraphWeight_ge_one (P : GW.Space) (n : ℕ) (k : GW.Fock.Coordinates n) :
    1 ≤ operatorGraphWeight P n k := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (freeSymbol P n k)]

theorem energyWeight_sq (P : GW.Space) (n : ℕ) (k : GW.Fock.Coordinates n) :
    energyWeight P n k ^ 2 = 1 + freeSymbol P n k :=
  Real.sq_sqrt (by linarith [freeSymbol_nonneg P n k])

theorem freeSymbol_permutation (P : GW.Space) (n : ℕ) (τ : Equiv.Perm (Fin n))
    (k : GW.Fock.Coordinates n) : freeSymbol P n (fun i => k (τ i)) = freeSymbol P n k := by
  simp only [freeSymbol, totalMomentum_permutation]

theorem energyWeight_permutation (P : GW.Space) (n : ℕ) (τ : Equiv.Perm (Fin n))
    (k : GW.Fock.Coordinates n) : energyWeight P n (fun i => k (τ i)) = energyWeight P n k := by
  simp only [energyWeight, freeSymbol_permutation]

/-- A symmetric weight preserves the actual GW symmetric subspace under all bounded
Borel functions of that weight. This instantiates the retained weighted-space API. -/
theorem symmetricWeight_functionalInvariant (n : ℕ) {w : GW.Fock.Coordinates n → ℝ}
    (hw : Measurable w)
    (hp : ∀ (τ : Equiv.Perm (Fin n)) k, w (fun i => k (τ i)) = w k) :
    GW.Spaces.FunctionalWeightInvariant (GW.Fock.symmetricSector n) hw := by
  intro a ha c hc u
  apply (GW.Fock.symmetricSector_mem_iff n _).mpr
  intro τ
  have hsymm := (GW.Fock.symmetricSector_mem_iff n _).mp u.property τ
  have hm := GW.Analysis.boundedMultiplier_ae (a ∘ w) (ha.comp hw)
    (Eventually.of_forall (fun k => hc (w k))) (u : GW.Fock.AmbientSector n)
  filter_upwards [hm,
    (GW.Fock.coordinatePermutation_preserving n τ).quasiMeasurePreserving.ae hm,
    hsymm] with k hout hin hs
  simp only [GW.Fock.coordinatePermutation_eq] at hin
  change _ = _
  rw [← hin, ← hout]
  simp only [Function.comp_apply]
  rw [hp τ k, hs]

def energyWeightInvariant (P : GW.Space) (n : ℕ) :
    GW.Spaces.WeightInvariant (GW.Fock.symmetricSector n)
      (energyWeight_measurable P n) (energyWeight_ge_one P n) :=
  GW.Spaces.weightInvariant_of_functional (energyWeight_ge_one P n)
    (symmetricWeight_functionalInvariant n (energyWeight_measurable P n)
      (fun τ k => energyWeight_permutation P n τ k))

/-- Reciprocal weight on each original GW sector, with the scalar vacuum explicit. -/
def sectorEnergyEmbedding (P : GW.Space) : ∀ n, GW.Fock.Sector n →L[ℂ] GW.Fock.Sector n
  | 0 => (((Real.sqrt (1 + ‖P‖ ^ 2))⁻¹ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ ℂ
  | n + 1 => GW.Spaces.restrictedReciprocal (energyWeightInvariant P (n+1))

theorem sectorEnergyEmbedding_norm (P : GW.Space) (n : ℕ) :
    ‖sectorEnergyEmbedding P n‖ ≤ 1 := by
  cases n with
  | zero =>
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖(((Real.sqrt (1 + ‖P‖ ^ 2))⁻¹ : ℝ) : ℂ) • z‖ ≤ 1 * ‖z‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
    apply inv_le_one_of_one_le₀
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg ‖P‖]
  | succ n => exact GW.Spaces.restrictedWeightEmbedding_norm (energyWeightInvariant P (n+1))

/-- Complete graph coordinates; this is never the ambient-norm domain subtype. -/
def EnergySpace (_P : GW.Space) := GW.Fock.Carrier

instance (P : GW.Space) : NormedAddCommGroup (EnergySpace P) :=
  inferInstanceAs (NormedAddCommGroup GW.Fock.Carrier)
instance (P : GW.Space) : InnerProductSpace ℂ (EnergySpace P) :=
  inferInstanceAs (InnerProductSpace ℂ GW.Fock.Carrier)
instance (P : GW.Space) : CompleteSpace (EnergySpace P) :=
  inferInstanceAs (CompleteSpace GW.Fock.Carrier)

def energyCoordinates (P : GW.Space) : EnergySpace P ≃ₗᵢ[ℂ] GW.Fock.Carrier :=
  LinearIsometryEquiv.refl ℂ GW.Fock.Carrier

def energyEmbedding (P : GW.Space) : EnergySpace P →L[ℂ] GW.Fock.Carrier :=
  (GW.Spaces.diagonalMap (sectorEnergyEmbedding P) zero_le_one
    (sectorEnergyEmbedding_norm P)).comp
      (energyCoordinates P).toLinearIsometry.toContinuousLinearMap

theorem energyEmbedding_apply (P : GW.Space) (x : EnergySpace P) (n : ℕ) :
    energyEmbedding P x n = sectorEnergyEmbedding P n (energyCoordinates P x n) := rfl

theorem energyEmbedding_opNorm (P : GW.Space) : ‖energyEmbedding P‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖GW.Spaces.diagonalMap (sectorEnergyEmbedding P) zero_le_one
    (sectorEnergyEmbedding_norm P) (energyCoordinates P x)‖ ≤ 1 * ‖x‖
  have h := GW.Spaces.diagonal_norm_bound (sectorEnergyEmbedding P) zero_le_one
    (sectorEnergyEmbedding_norm P) (energyCoordinates P x)
  change ‖GW.Spaces.diagonalLinear (sectorEnergyEmbedding P)
    (sectorEnergyEmbedding_norm P) (energyCoordinates P x)‖ ≤ 1 * ‖x‖
  simpa only [LinearIsometryEquiv.norm_map] using h

theorem vacuumEnergyWeight_ne_zero (P : GW.Space) : Real.sqrt (1 + ‖P‖ ^ 2) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (by positivity))

theorem sectorEnergyEmbedding_injective (P : GW.Space) (n : ℕ) :
    Function.Injective (sectorEnergyEmbedding P n) := by
  cases n with
  | zero =>
    change Function.Injective (fun z : ℂ =>
      (((Real.sqrt (1 + ‖P‖ ^ 2))⁻¹ : ℝ) : ℂ) * z)
    intro x y h
    exact mul_left_cancel₀ (by exact_mod_cast inv_ne_zero (vacuumEnergyWeight_ne_zero P)) h
  | succ n => exact GW.Spaces.restrictedWeightEmbedding_injective (energyWeightInvariant P (n+1))

theorem energyEmbedding_injective (P : GW.Space) : Function.Injective (energyEmbedding P) := by
  intro x y h
  apply (energyCoordinates P).injective
  apply lp.ext
  funext n
  apply sectorEnergyEmbedding_injective P n
  exact congrArg (fun u : GW.Fock.Carrier => u n) h

/-- Maximal sector multiplication by the actual energy weight. -/
def sectorEnergyWeightOperator (P : GW.Space) :
    ∀ n, GW.Fock.Sector n →ₗ.[ℂ] GW.Fock.Sector n
  | 0 => (((Real.sqrt (1 + ‖P‖ ^ 2) : ℝ) : ℂ) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)).toPMap ⊤
  | n+1 =>
    { domain := GW.Spaces.restrictedWeightDomain (GW.Fock.symmetricSector (n+1))
        (energyWeight P (n+1))
      toFun := GW.Spaces.restrictedWeightProduct (energyWeightInvariant P (n+1)) }

def sectorEnergyEmbeddingInput (P : GW.Space) (n : ℕ) (x : GW.Fock.Sector n) :
    (sectorEnergyWeightOperator P n).domain := by
  cases n with
  | zero =>
    change ℂ at x
    change (⊤ : Submodule ℂ ℂ)
    exact ⟨sectorEnergyEmbedding P 0 x, Submodule.mem_top⟩
  | succ n => exact ⟨sectorEnergyEmbedding P (n+1) x,
      GW.Spaces.restrictedWeightEmbedding_mem (energyWeightInvariant P (n+1)) x⟩

theorem sectorEnergyEmbeddingInput_coe (P : GW.Space) (n : ℕ) (x : GW.Fock.Sector n) :
    (sectorEnergyEmbeddingInput P n x : GW.Fock.Sector n) = sectorEnergyEmbedding P n x := by
  cases n <;> rfl

theorem sectorEnergyWeight_embedding (P : GW.Space) (n : ℕ) (x : GW.Fock.Sector n) :
    sectorEnergyWeightOperator P n (sectorEnergyEmbeddingInput P n x) = x := by
  cases n with
  | zero =>
    change ℂ at x
    change (Real.sqrt (1 + ‖P‖ ^ 2) : ℂ) *
      ((((Real.sqrt (1 + ‖P‖ ^ 2))⁻¹ : ℝ) : ℂ) * x) = x
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (vacuumEnergyWeight_ne_zero P)]
    simp
  | succ n => exact GW.Spaces.restricted_product_embedding (energyWeightInvariant P (n+1)) x

theorem sectorEnergyEmbedding_weight (P : GW.Space) (n : ℕ)
    (u : (sectorEnergyWeightOperator P n).domain) :
    sectorEnergyEmbedding P n (sectorEnergyWeightOperator P n u) = (u : GW.Fock.Sector n) := by
  cases n with
  | zero =>
    let z : ℂ := (u : GW.Fock.Sector 0)
    change (((Real.sqrt (1 + ‖P‖ ^ 2))⁻¹ : ℝ) : ℂ) *
      ((Real.sqrt (1 + ‖P‖ ^ 2) : ℂ) * z) = z
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (vacuumEnergyWeight_ne_zero P)]
    simp
  | succ n => exact GW.Spaces.restricted_embedding_product (energyWeightInvariant P (n+1)) u

/-- The joint maximal weighted domain requires a square-summable weighted output. -/
def energyWeightOperator (P : GW.Space) : GW.Fock.Carrier →ₗ.[ℂ] GW.Fock.Carrier :=
  GW.Fock.operatorSum GW.Fock.Sector (sectorEnergyWeightOperator P)

theorem energyEmbedding_mem_domain (P : GW.Space) (x : EnergySpace P) :
    energyEmbedding P x ∈ (energyWeightOperator P).domain := by
  apply (energyWeightOperator P).mem_domain_of_mem_graph (y := energyCoordinates P x)
  change (energyEmbedding P x, energyCoordinates P x) ∈
    (GW.Fock.operatorSum GW.Fock.Sector (sectorEnergyWeightOperator P)).graph
  rw [GW.Fock.operatorSum_graph_iff]
  intro n
  have h := (sectorEnergyWeightOperator P n).mem_graph
    (sectorEnergyEmbeddingInput P n (energyCoordinates P x n))
  rw [sectorEnergyWeight_embedding] at h
  simpa only [sectorEnergyEmbeddingInput_coe, energyEmbedding_apply] using h

theorem energyEmbedding_range (P : GW.Space) : Set.range (energyEmbedding P) =
    ((energyWeightOperator P).domain : Set GW.Fock.Carrier) := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    exact energyEmbedding_mem_domain P x
  · intro hu
    let z := (energyWeightOperator P) ⟨u, hu⟩
    refine ⟨(energyCoordinates P).symm z, ?_⟩
    apply lp.ext
    funext n
    change sectorEnergyEmbedding P n (energyCoordinates P ((energyCoordinates P).symm z) n) = u n
    rw [LinearIsometryEquiv.apply_symm_apply]
    have he := GW.Fock.operatorSum_apply_component GW.Fock.Sector
      (sectorEnergyWeightOperator P) ⟨u, hu⟩ n
    change sectorEnergyWeightOperator P n
      (GW.Fock.operatorSumInput GW.Fock.Sector (sectorEnergyWeightOperator P) ⟨u,hu⟩ n) = z n at he
    rw [← he]
    exact sectorEnergyEmbedding_weight P n _

theorem sectorEnergyWeight_domain_dense (P : GW.Space) (n : ℕ) :
    Dense ((sectorEnergyWeightOperator P n).domain : Set (GW.Fock.Sector n)) := by
  cases n with
  | zero =>
    change Dense ((⊤ : Submodule ℂ ℂ) : Set ℂ)
    simp
  | succ n =>
    have h := GW.Spaces.restrictedWeightEmbedding_dense (energyWeightInvariant P (n+1))
    change Dense (Set.range (GW.Spaces.restrictedWeightEmbedding
      (energyWeightInvariant P (n+1)))) at h
    rw [GW.Spaces.restrictedWeightEmbedding_range] at h
    exact h

theorem energyEmbedding_dense (P : GW.Space) : DenseRange (energyEmbedding P) := by
  change Dense (Set.range (energyEmbedding P))
  rw [energyEmbedding_range]
  exact GW.Fock.operatorSum_dense GW.Fock.Sector (sectorEnergyWeightOperator P)
    (sectorEnergyWeight_domain_dense P)

/-- Physical representatives always use the existing vacuum/positive-sector maps. -/
def physicalSector : ∀ n, GW.Fock.Sector n →ₗᵢ[ℂ] GW.Fock.AmbientSector n
  | 0 => GW.Fock.vacuumAdapter.toLinearIsometry
  | n+1 => GW.Fock.sectorInclusion n

theorem energyWeight_zero (P : GW.Space) (k : GW.Fock.Coordinates 0) :
    energyWeight P 0 k = Real.sqrt (1 + ‖P‖ ^ 2) := by
  simp [energyWeight, freeSymbol, totalMomentum]

/-- Exact recovery of the weighted physical representative, including the scalar vacuum. -/
theorem energyEmbedding_weighted_ae (P : GW.Space) (x : EnergySpace P) (n : ℕ) :
    (fun k => (energyWeight P n k : ℂ) • physicalSector n (energyEmbedding P x n) k) =ᵐ[GW.Fock.sectorMeasure n]
      physicalSector n (energyCoordinates P x n) := by
  cases n with
  | zero =>
    filter_upwards [GW.Fock.vacuumAdapter_ae (energyEmbedding P x 0),
      GW.Fock.vacuumAdapter_ae (energyCoordinates P x 0)] with k hu hv
    change (energyWeight P 0 k : ℂ) *
      GW.Fock.vacuumAdapterIsometry (energyEmbedding P x 0) k =
      GW.Fock.vacuumAdapterIsometry (energyCoordinates P x 0) k
    rw [hu, hv, energyWeight_zero]
    let z : ℂ := energyCoordinates P x 0
    change (Real.sqrt (1 + ‖P‖ ^ 2) : ℂ) *
      ((((Real.sqrt (1 + ‖P‖ ^ 2))⁻¹ : ℝ) : ℂ) * z) = z
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (vacuumEnergyWeight_ne_zero P)]
    simp
  | succ n =>
    exact GW.Spaces.reciprocalMap_weighted_ae (energyWeight_measurable P (n+1))
      (energyWeight_ge_one P (n+1)) (physicalSector (n+1) (energyCoordinates P x (n+1)))

/-- The literal free fiber expectation on each physical sector. -/
def freeSectorEnergy (P : GW.Space) (n : ℕ) (u : GW.Fock.Sector n) : ℝ :=
  ∫ k, freeSymbol P n k * ‖physicalSector n u k‖ ^ 2 ∂GW.Fock.sectorMeasure n

def freeEnergy (P : GW.Space) (u : GW.Fock.Carrier) : ℝ :=
  ∑' n, freeSectorEnergy P n (u n)

theorem freeSectorEnergy_integrable (P : GW.Space) (x : EnergySpace P) (n : ℕ) :
    Integrable (fun k => freeSymbol P n k *
      ‖physicalSector n (energyEmbedding P x n) k‖ ^ 2) (GW.Fock.sectorMeasure n) := by
  have hv := (Lp.memLp (physicalSector n (energyCoordinates P x n))).integrable_norm_pow
    (p := 2) (by norm_num)
  have hu := (Lp.memLp (physicalSector n (energyEmbedding P x n))).integrable_norm_pow
    (p := 2) (by norm_num)
  apply (hv.sub hu).congr
  filter_upwards [energyEmbedding_weighted_ae P x n] with k hk
  simp only [Pi.sub_apply]
  rw [← hk, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    energyWeight_sq]
  ring

theorem freeSectorEnergy_embedding (P : GW.Space) (x : EnergySpace P) (n : ℕ) :
    freeSectorEnergy P n (energyEmbedding P x n) =
      ‖energyCoordinates P x n‖ ^ 2 - ‖energyEmbedding P x n‖ ^ 2 := by
  let v := physicalSector n (energyCoordinates P x n)
  let u := physicalSector n (energyEmbedding P x n)
  have hv := (Lp.memLp v).integrable_norm_pow (p := 2) (by norm_num)
  have hu := (Lp.memLp u).integrable_norm_pow (p := 2) (by norm_num)
  have he : (fun k => ‖v k‖ ^ 2 - ‖u k‖ ^ 2) =ᵐ[GW.Fock.sectorMeasure n]
      (fun k => freeSymbol P n k * ‖u k‖ ^ 2) := by
    filter_upwards [energyEmbedding_weighted_ae P x n] with k hk
    change (energyWeight P n k : ℂ) • u k = v k at hk
    rw [← hk, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      energyWeight_sq]
    ring
  have h := integral_congr_ae he
  rw [integral_sub hv hu, ← GW.Analysis.l2_norm_sq (𝕜 := ℂ),
    ← GW.Analysis.l2_norm_sq (𝕜 := ℂ)] at h
  change ‖physicalSector n (energyCoordinates P x n)‖ ^ 2 -
    ‖physicalSector n (energyEmbedding P x n)‖ ^ 2 = freeSectorEnergy P n (energyEmbedding P x n) at h
  simpa only [LinearIsometry.norm_map] using h.symm

theorem freeSectorEnergy_summable (P : GW.Space) (x : EnergySpace P) :
    Summable (fun n => freeSectorEnergy P n (energyEmbedding P x n)) := by
  simp_rw [freeSectorEnergy_embedding]
  exact ((GW.Analysis.memℓp_two_iff_sq _).mp (energyCoordinates P x).property).sub
    ((GW.Analysis.memℓp_two_iff_sq _).mp (energyEmbedding P x).property)

theorem energyEmbedding_norm_identity (P : GW.Space) (x : EnergySpace P) :
    ‖x‖ ^ 2 = ‖energyEmbedding P x‖ ^ 2 + freeEnergy P (energyEmbedding P x) := by
  have hx := (GW.Analysis.memℓp_two_iff_sq _).mp (energyCoordinates P x).property
  have hu := (GW.Analysis.memℓp_two_iff_sq _).mp (energyEmbedding P x).property
  have he : freeEnergy P (energyEmbedding P x) =
      ‖energyCoordinates P x‖ ^ 2 - ‖energyEmbedding P x‖ ^ 2 := by
    unfold freeEnergy
    simp_rw [freeSectorEnergy_embedding]
    rw [Summable.tsum_sub hx hu, ← GW.Fock.carrier_norm_sq, ← GW.Fock.carrier_norm_sq]
  rw [he, LinearIsometryEquiv.norm_map]
  ring

end Froehlich
