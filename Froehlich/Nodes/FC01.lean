import Froehlich.Nodes.FD02Weights
import Froehlich.Nodes.FD02FreeForm
import Froehlich.Nodes.FD02Multipliers
import Froehlich.Nodes.GW04

/-! FC01: the source's finite-particle, bounded-individual-momentum cutoffs.
Only these bounded-support core operations are used for unbounded multipliers;
no universal weighted-domain invariance is asserted. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

def configurationBall (n : ℕ) (R : ℝ) : Set (GW.Fock.Coordinates n) :=
  {k | ∀ i, ‖k i‖ ≤ R}

theorem configurationBall_measurable (n : ℕ) (R : ℝ) : MeasurableSet (configurationBall n R) := by
  have he : configurationBall n R = ⋂ i : Fin n, {k : GW.Fock.Coordinates n | ‖k i‖ ≤ R} := by
    ext k
    simp only [configurationBall, Set.mem_setOf_eq, Set.mem_iInter]
  rw [he]
  exact MeasurableSet.iInter (fun i => measurableSet_le (measurable_pi_apply i).norm measurable_const)

theorem configurationBall_permutation (n : ℕ) (R : ℝ) (τ : Equiv.Perm (Fin n))
    (k : GW.Fock.Coordinates n) :
    (fun i => k (τ i)) ∈ configurationBall n R ↔ k ∈ configurationBall n R := by
  constructor
  · intro h i
    have hi := h (τ.symm i)
    simpa only [Equiv.apply_symm_apply] using hi
  · intro h i
    exact h (τ i)

def configurationIndicator (n : ℕ) (R : ℝ) : GW.Fock.Coordinates n → ℂ :=
  (configurationBall n R).indicator (fun _ => 1)

theorem configurationIndicator_measurable (n : ℕ) (R : ℝ) : Measurable (configurationIndicator n R) :=
  measurable_const.indicator (configurationBall_measurable n R)

theorem configurationIndicator_bound (n : ℕ) (R : ℝ) (k : GW.Fock.Coordinates n) :
    ‖configurationIndicator n R k‖ ≤ 1 := by
  by_cases h : k ∈ configurationBall n R <;> simp [configurationIndicator, h]

theorem configurationIndicator_permutation (n : ℕ) (R : ℝ) (τ : Equiv.Perm (Fin n))
    (k : GW.Fock.Coordinates n) :
    configurationIndicator n R (fun i => k (τ i)) = configurationIndicator n R k := by
  by_cases h : k ∈ configurationBall n R
  · have ht := (configurationBall_permutation n R τ k).mpr h
    simp [configurationIndicator, h, ht]
  · have ht : (fun i => k (τ i)) ∉ configurationBall n R :=
      fun ht => h ((configurationBall_permutation n R τ k).mp ht)
    simp [configurationIndicator, h, ht]

theorem configurationIndicator_zero (R : ℝ) (k : GW.Fock.Coordinates 0) :
    configurationIndicator 0 R k = 1 := by simp [configurationIndicator, configurationBall]

def sectorMomentumCutoff (R : ℝ) : ∀ n, GW.Fock.Sector n →L[ℂ] GW.Fock.Sector n
  | 0 => ContinuousLinearMap.id ℂ ℂ
  | n+1 => boundedSymmetricMultiplier (n+1) (configurationIndicator (n+1) R)
      (configurationIndicator_measurable (n+1) R) (configurationIndicator_bound (n+1) R)
      (configurationIndicator_permutation (n+1) R)

theorem sectorMomentumCutoff_norm (R : ℝ) (n : ℕ) : ‖sectorMomentumCutoff R n‖ ≤ 1 := by
  cases n with
  | zero =>
    change ‖ContinuousLinearMap.id ℂ ℂ‖ ≤ 1
    exact le_of_eq ContinuousLinearMap.norm_id
  | succ n =>
    exact boundedSymmetricMultiplier_norm (n+1) (configurationIndicator (n+1) R)
      (configurationIndicator_measurable (n+1) R) zero_le_one (configurationIndicator_bound (n+1) R)
      (configurationIndicator_permutation (n+1) R)

theorem sectorMomentumCutoff_ae (R : ℝ) (n : ℕ) (u : GW.Fock.Sector n) :
    (fun k => configurationIndicator n R k • physicalSector n u k) =ᵐ[GW.Fock.sectorMeasure n]
      physicalSector n (sectorMomentumCutoff R n u) := by
  cases n with
  | zero =>
    change ℂ at u
    filter_upwards [GW.Fock.vacuumAdapter_ae u,
      GW.Fock.vacuumAdapter_ae (sectorMomentumCutoff R 0 u)] with k hu hv
    change configurationIndicator 0 R k * GW.Fock.vacuumAdapterIsometry u k =
      GW.Fock.vacuumAdapterIsometry (sectorMomentumCutoff R 0 u) k
    rw [hu, hv, configurationIndicator_zero]
    change (1 : ℂ) * (u : ℂ) = (u : ℂ)
    exact one_mul _
  | succ n =>
    exact boundedSymmetricMultiplier_ae (n+1) (configurationIndicator (n+1) R)
      (configurationIndicator_measurable (n+1) R) (configurationIndicator_bound (n+1) R)
      (configurationIndicator_permutation (n+1) R) u

def momentumCutoff (R : ℝ) : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  GW.Spaces.diagonalMap (sectorMomentumCutoff R) zero_le_one (sectorMomentumCutoff_norm R)

def boundedMomentumProjection (M R : ℕ) : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  (lowSectorProjection M).comp (momentumCutoff (R : ℝ))

theorem boundedMomentumProjection_apply (M R n : ℕ) (u : GW.Fock.Carrier) :
    boundedMomentumProjection M R u n = if n ≤ M then sectorMomentumCutoff (R : ℝ) n (u n) else 0 :=
  GW.Fock.cutoff_apply GW.Fock.Sector M (momentumCutoff (R : ℝ) u) n

theorem momentumCutoff_norm_le (R : ℝ) (u : GW.Fock.Carrier) : ‖momentumCutoff R u‖ ≤ ‖u‖ := by
  have h := GW.Spaces.diagonal_norm_bound (sectorMomentumCutoff R) zero_le_one (sectorMomentumCutoff_norm R) u
  change ‖GW.Spaces.diagonalLinear (sectorMomentumCutoff R) (sectorMomentumCutoff_norm R) u‖ ≤ ‖u‖
  simpa only [one_mul] using h

theorem boundedMomentumProjection_norm_le (M R : ℕ) (u : GW.Fock.Carrier) :
    ‖boundedMomentumProjection M R u‖ ≤ ‖u‖ :=
  (lowSectorProjection_norm_le M (momentumCutoff (R : ℝ) u)).trans (momentumCutoff_norm_le _ u)


theorem configurationBall_mono (n : ℕ) {R S : ℝ} (h : R ≤ S) :
    configurationBall n R ⊆ configurationBall n S := fun _ hk i => (hk i).trans h

theorem configurationIndicator_absorbs (n : ℕ) {R S : ℝ} (h : R ≤ S) (k : GW.Fock.Coordinates n) :
    configurationIndicator n S k * configurationIndicator n R k = configurationIndicator n R k := by
  by_cases hk : k ∈ configurationBall n R
  · have hs := configurationBall_mono n h hk
    simp [configurationIndicator, hk, hs]
  · simp [configurationIndicator, hk]

theorem sectorMomentumCutoff_absorbs {R S : ℝ} (h : R ≤ S) (n : ℕ) (u : GW.Fock.Sector n) :
    sectorMomentumCutoff S n (sectorMomentumCutoff R n u) = sectorMomentumCutoff R n u := by
  apply (physicalSector n).injective
  apply Lp.ext
  filter_upwards [sectorMomentumCutoff_ae S n (sectorMomentumCutoff R n u),
    sectorMomentumCutoff_ae R n u] with k hs hr
  simp only [smul_eq_mul] at hs hr
  calc
    _ = configurationIndicator n S k * physicalSector n (sectorMomentumCutoff R n u) k := hs.symm
    _ = configurationIndicator n S k * (configurationIndicator n R k * physicalSector n u k) := by rw [← hr]
    _ = (configurationIndicator n S k * configurationIndicator n R k) * physicalSector n u k :=
      (mul_assoc _ _ _).symm
    _ = configurationIndicator n R k * physicalSector n u k := by rw [configurationIndicator_absorbs n h k]
    _ = _ := hr

theorem boundedMomentumProjection_absorbs (M R N S : ℕ) (hM : M ≤ N) (hR : R ≤ S)
    (u : GW.Fock.Carrier) :
    boundedMomentumProjection N S (boundedMomentumProjection M R u) = boundedMomentumProjection M R u := by
  apply lp.ext
  funext n
  simp only [boundedMomentumProjection_apply]
  by_cases hn : n ≤ M
  · have hn' : n ≤ N := hn.trans hM
    simp only [if_pos hn, if_pos hn']
    exact sectorMomentumCutoff_absorbs (by exact_mod_cast hR) n (u n)
  · by_cases hn' : n ≤ N
    · simp only [if_pos hn', if_neg hn, map_zero]
    · simp only [if_neg hn', if_neg hn]

theorem boundedMomentumProjection_idempotent (M R : ℕ) (u : GW.Fock.Carrier) :
    boundedMomentumProjection M R (boundedMomentumProjection M R u) = boundedMomentumProjection M R u :=
  boundedMomentumProjection_absorbs M R M R le_rfl le_rfl u

/-- Exactly the union of the source's positive integer cutoff ranges. -/
def boundedMomentumCore : Submodule ℂ GW.Fock.Carrier where
  carrier := {u | ∃ M R : ℕ, 1 ≤ M ∧ 1 ≤ R ∧ boundedMomentumProjection M R u = u}
  zero_mem' := ⟨1,1,le_rfl,le_rfl,map_zero _⟩
  add_mem' := by
    rintro u v ⟨M,R,hM,hR,hu⟩ ⟨N,S,hN,hS,hv⟩
    refine ⟨max M N,max R S,hM.trans (le_max_left _ _),hR.trans (le_max_left _ _),?_⟩
    have hU := boundedMomentumProjection_absorbs M R (max M N) (max R S)
      (le_max_left _ _) (le_max_left _ _) u
    have hV := boundedMomentumProjection_absorbs N S (max M N) (max R S)
      (le_max_right _ _) (le_max_right _ _) v
    rw [hu] at hU
    rw [hv] at hV
    rw [map_add, hU, hV]
  smul_mem' := by
    rintro c u ⟨M,R,hM,hR,hu⟩
    refine ⟨M,R,hM,hR,?_⟩
    rw [map_smul, hu]

theorem boundedMomentumCore_mem_iff_range (u : GW.Fock.Carrier) :
    u ∈ boundedMomentumCore ↔
      ∃ M R : ℕ, 1 ≤ M ∧ 1 ≤ R ∧ u ∈ Set.range (boundedMomentumProjection M R) := by
  constructor
  · rintro ⟨M,R,hM,hR,hu⟩
    exact ⟨M,R,hM,hR,u,hu⟩
  · rintro ⟨M,R,hM,hR,v,hv⟩
    refine ⟨M,R,hM,hR,?_⟩
    have h := boundedMomentumProjection_idempotent M R v
    rwa [hv] at h


theorem boundedMomentumCore_le_finiteSector :
    boundedMomentumCore ≤ GW.Fock.finiteSectorDomain GW.Fock.Sector := by
  intro u hu
  obtain ⟨M,R,hM,hR,hfix⟩ := hu
  rw [← hfix]
  exact GW.Fock.cutoff_mem_finiteSectorDomain GW.Fock.Sector M (momentumCutoff (R : ℝ) u)

theorem boundedMomentumCore_le_numberGraph : boundedMomentumCore ≤ numberFormGraph.domain := by
  intro u hu
  exact GW.Fock.finiteSectorDomain_le GW.Fock.Sector (fun n => ((n : ℝ)+1)^(1/2 : ℝ))
    (boundedMomentumCore_le_finiteSector hu)

/-- Algebraic core lift with the true number graph norm. It is not asserted
continuous for the ambient norm on the unbounded union of cutoff ranges. -/
def coreNumberLift : boundedMomentumCore →ₗ[ℂ] NumberFormSpace :=
  numberFormGraph.product.comp (Submodule.inclusion boundedMomentumCore_le_numberGraph)

theorem coreNumberLift_embedding (u : boundedMomentumCore) :
    numberFormEmbedding (coreNumberLift u) = (u : GW.Fock.Carrier) :=
  numberFormGraph.embedding_product (Submodule.inclusion boundedMomentumCore_le_numberGraph u)

theorem boundedMomentumCore_support (u : boundedMomentumCore) :
    ∃ M R : ℕ, 1 ≤ M ∧ 1 ≤ R ∧
      (∀ n : ℕ, M < n → (u : GW.Fock.Carrier) n = 0) ∧
      (∀ n : ℕ, ∀ᵐ k ∂GW.Fock.sectorMeasure n,
        k ∉ configurationBall n (R : ℝ) → physicalSector n ((u : GW.Fock.Carrier) n) k = 0) := by
  obtain ⟨M,R,hM,hR,hfix⟩ := u.property
  have hfinite : ∀ n : ℕ, M < n → (u : GW.Fock.Carrier) n = 0 := by
    intro n hn
    have he := congrArg (fun v : GW.Fock.Carrier => v n) hfix
    rw [boundedMomentumProjection_apply, if_neg (not_le.mpr hn)] at he
    exact he.symm
  refine ⟨M,R,hM,hR,hfinite,?_⟩
  intro n
  by_cases hn : n ≤ M
  · have he := congrArg (fun v : GW.Fock.Carrier => v n) hfix
    rw [boundedMomentumProjection_apply, if_pos hn] at he
    have hs := sectorMomentumCutoff_ae (R : ℝ) n ((u : GW.Fock.Carrier) n)
    rw [he] at hs
    filter_upwards [hs] with k hk
    intro hout
    have hi : configurationIndicator n (R : ℝ) k = 0 := by simp [configurationIndicator, hout]
    rw [hi, zero_smul] at hk
    exact hk.symm
  · have hu := hfinite n (lt_of_not_ge hn)
    have he : physicalSector n ((u : GW.Fock.Carrier) n) = 0 := by rw [hu, map_zero]
    rw [he]
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := GW.Fock.sectorMeasure n)] with k hk
    intro _
    simpa only [Pi.zero_apply] using hk

theorem boundedMomentumCore_mem_of_support (M R : ℕ) (hM : 1 ≤ M) (hR : 1 ≤ R)
    (u : GW.Fock.Carrier) (hfinite : ∀ n : ℕ, M < n → u n = 0)
    (hsupport : ∀ n : ℕ, ∀ᵐ k ∂GW.Fock.sectorMeasure n,
      k ∉ configurationBall n (R : ℝ) → physicalSector n (u n) k = 0) :
    u ∈ boundedMomentumCore := by
  refine ⟨M,R,hM,hR,?_⟩
  apply lp.ext
  funext n
  rw [boundedMomentumProjection_apply]
  by_cases hn : n ≤ M
  · rw [if_pos hn]
    apply (physicalSector n).injective
    apply Lp.ext
    filter_upwards [sectorMomentumCutoff_ae (R : ℝ) n (u n), hsupport n] with k hk hs
    by_cases hmem : k ∈ configurationBall n (R : ℝ)
    · have hi : configurationIndicator n (R : ℝ) k = 1 := by simp [configurationIndicator, hmem]
      simpa only [hi, one_smul] using hk.symm
    · have hi : configurationIndicator n (R : ℝ) k = 0 := by simp [configurationIndicator, hmem]
      rw [hi, zero_smul] at hk
      exact hk.symm.trans (hs hmem).symm
  · rw [if_neg hn]
    exact (hfinite n (lt_of_not_ge hn)).symm

end Froehlich
