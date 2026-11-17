import Froehlich.Nodes.FD02Weights

/-! FD02's maximal real multiplication graph on the canonical symmetric Fock
carrier, assembled by preimages of the retained scalar multiplier graphs. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

def physicalSectorMap (n : ℕ) : GW.Fock.Carrier →L[ℂ] GW.Fock.AmbientSector n :=
  (physicalSector n).toContinuousLinearMap.comp (lp.evalCLM ℂ GW.Fock.Sector 2 n)

def fockMultiplierGraph (m : ∀ n, GW.Fock.Coordinates n → ℝ) :
    Submodule ℂ (GW.Fock.Carrier × GW.Fock.Carrier) :=
  ⨅ n, ((GW.Analysis.realMultiplier (H := ℂ) (m n) (GW.Fock.sectorMeasure n)).graph).comap
    ((physicalSectorMap n).toLinearMap.prodMap (physicalSectorMap n).toLinearMap)

theorem fockMultiplierGraph_iff (m : ∀ n, GW.Fock.Coordinates n → ℝ)
    (u v : GW.Fock.Carrier) :
    (u,v) ∈ fockMultiplierGraph m ↔
      ∀ n, (fun k => (m n k : ℂ) • physicalSector n (u n) k) =ᵐ[GW.Fock.sectorMeasure n]
        physicalSector n (v n) := by
  simp only [fockMultiplierGraph, Submodule.mem_iInf, Submodule.mem_comap]
  exact forall_congr' (fun n => realMultiplier_graph_ae_iff _ _ _)

theorem fockMultiplierGraph_single_valued (m : ∀ n, GW.Fock.Coordinates n → ℝ)
    (p : GW.Fock.Carrier × GW.Fock.Carrier) (hp : p ∈ fockMultiplierGraph m) (h0 : p.1 = 0) : p.2 = 0 := by
  have h := (fockMultiplierGraph_iff m p.1 p.2).mp hp
  apply lp.ext
  funext n
  change p.2 n = (0 : GW.Fock.Sector n)
  apply (physicalSector n).injective
  apply Lp.ext
  have hz := Lp.coeFn_zero (E := ℂ) (p := 2) (μ := GW.Fock.sectorMeasure n)
  have he : physicalSector n (p.1 n) = 0 := by rw [h0]; exact map_zero (physicalSector n)
  have hout : physicalSector n (0 : GW.Fock.Sector n) = 0 := map_zero _
  have hn := h n
  rw [he] at hn
  rw [hout]
  filter_upwards [hn, hz] with k hk hz
  simp only [Pi.zero_apply] at hz
  rw [hz, smul_zero] at hk
  rw [hz]
  exact hk.symm

def fockRealMultiplier (m : ∀ n, GW.Fock.Coordinates n → ℝ) :
    GW.Fock.Carrier →ₗ.[ℂ] GW.Fock.Carrier :=
  (fockMultiplierGraph m).toLinearPMap

theorem fockRealMultiplier_graph (m : ∀ n, GW.Fock.Coordinates n → ℝ) :
    (fockRealMultiplier m).graph = fockMultiplierGraph m :=
  Submodule.toLinearPMap_graph_eq _ (fockMultiplierGraph_single_valued m)


theorem fockRealMultiplier_graph_ae_iff (m : ∀ n, GW.Fock.Coordinates n → ℝ)
    (u v : GW.Fock.Carrier) :
    (u,v) ∈ (fockRealMultiplier m).graph ↔
      ∀ n, (fun k => (m n k : ℂ) • physicalSector n (u n) k) =ᵐ[GW.Fock.sectorMeasure n]
        physicalSector n (v n) := by
  rw [fockRealMultiplier_graph]
  exact fockMultiplierGraph_iff m u v

theorem fockRealMultiplier_domain_iff (m : ∀ n, GW.Fock.Coordinates n → ℝ) (u : GW.Fock.Carrier) :
    u ∈ (fockRealMultiplier m).domain ↔ ∃ v : GW.Fock.Carrier,
      ∀ n, (fun k => (m n k : ℂ) • physicalSector n (u n) k) =ᵐ[GW.Fock.sectorMeasure n]
        physicalSector n (v n) := by
  rw [LinearPMap.mem_domain_iff]
  exact exists_congr (fun v => fockRealMultiplier_graph_ae_iff m u v)

theorem fockRealMultiplier_closed (m : ∀ n, GW.Fock.Coordinates n → ℝ)
    (hm : ∀ n, Measurable (m n)) : (fockRealMultiplier m).IsClosed := by
  change IsClosed ((fockRealMultiplier m).graph : Set (GW.Fock.Carrier × GW.Fock.Carrier))
  have he : ((fockRealMultiplier m).graph : Set (GW.Fock.Carrier × GW.Fock.Carrier)) =
      ⋂ n, (fun p : GW.Fock.Carrier × GW.Fock.Carrier =>
        (physicalSectorMap n p.1, physicalSectorMap n p.2)) ⁻¹'
          ((GW.Analysis.realMultiplier (H := ℂ) (m n) (GW.Fock.sectorMeasure n)).graph :
            Set (GW.Fock.AmbientSector n × GW.Fock.AmbientSector n)) := by
    ext p
    rcases p with ⟨u,v⟩
    simp only [Set.mem_iInter, Set.mem_preimage]
    exact (fockRealMultiplier_graph_ae_iff m u v).trans
      (forall_congr' (fun n => (realMultiplier_graph_ae_iff _ _ _).symm))
  rw [he]
  apply isClosed_iInter
  intro n
  exact (GW.Analysis.realMultiplier_closed (H := ℂ) (μ := GW.Fock.sectorMeasure n) (hm n)).preimage
    (((physicalSectorMap n).continuous.comp continuous_fst).prodMk
      ((physicalSectorMap n).continuous.comp continuous_snd))


section SymmetricSymbols
variable (m : ∀ n, GW.Fock.Coordinates n → ℝ)
  (hm : ∀ n, Measurable (m n))
  (hp : ∀ n (τ : Equiv.Perm (Fin n)) k, m n (fun i => k (τ i)) = m n k)

def fockGraphSymbolWeight (n : ℕ) : GW.Fock.Coordinates n → ℝ :=
  GW.Spaces.multiplierGraphWeight (m n)

include hm in
theorem fockGraphSymbolWeight_measurable (n : ℕ) : Measurable (fockGraphSymbolWeight m n) :=
  GW.Spaces.multiplierGraphWeight_measurable (hm n)

theorem fockGraphSymbolWeight_lower (n : ℕ) (k : GW.Fock.Coordinates n) :
    1 ≤ fockGraphSymbolWeight m n k := GW.Spaces.multiplierGraphWeight_lower (m n) k

include hp in
theorem fockGraphSymbolWeight_permutation (n : ℕ) (τ : Equiv.Perm (Fin n)) (k : GW.Fock.Coordinates n) :
    fockGraphSymbolWeight m n (fun i => k (τ i)) = fockGraphSymbolWeight m n k := by
  unfold fockGraphSymbolWeight GW.Spaces.multiplierGraphWeight
  rw [hp n τ k]

def fockSymbolWeightedGraph : GW.Spaces.WeightedGraph GW.Fock.Carrier GW.Fock.Carrier :=
  fockWeightedGraph (fockGraphSymbolWeight m) (fockGraphSymbolWeight_measurable m hm)
    (fockGraphSymbolWeight_lower m) (fockGraphSymbolWeight_permutation m hp)

def sectorNormalizedSymbol : ∀ n, GW.Fock.Sector n →L[ℂ] GW.Fock.Sector n
  | 0 => normalizedFreeFunction (m 0 0) • ContinuousLinearMap.id ℂ ℂ
  | n+1 => boundedSymmetricMultiplier (n+1) (normalizedFreeFunction ∘ m (n+1))
      (normalizedFreeFunction_measurable.comp (hm (n+1)))
      (fun k => normalizedFreeFunction_bound (m (n+1) k))
      (fun τ k => congrArg normalizedFreeFunction (hp (n+1) τ k))

theorem sectorNormalizedSymbol_norm (n : ℕ) : ‖sectorNormalizedSymbol m hm hp n‖ ≤ 1 := by
  cases n with
  | zero =>
    change ‖normalizedFreeFunction (m 0 0) • ContinuousLinearMap.id ℂ ℂ‖ ≤ _
    rw [norm_smul, ContinuousLinearMap.norm_id, mul_one]
    exact normalizedFreeFunction_bound _
  | succ n =>
    exact boundedSymmetricMultiplier_norm (n+1) (normalizedFreeFunction ∘ m (n+1))
      (normalizedFreeFunction_measurable.comp (hm (n+1))) zero_le_one
      (fun k => normalizedFreeFunction_bound (m (n+1) k))
      (fun τ k => congrArg normalizedFreeFunction (hp (n+1) τ k))

theorem sectorNormalizedSymbol_ae (n : ℕ) (u : GW.Fock.Sector n) :
    (fun k => normalizedFreeFunction (m n k) • physicalSector n u k) =ᵐ[GW.Fock.sectorMeasure n]
      physicalSector n (sectorNormalizedSymbol m hm hp n u) := by
  cases n with
  | zero =>
    filter_upwards [GW.Fock.vacuumAdapter_ae u,
      GW.Fock.vacuumAdapter_ae (sectorNormalizedSymbol m hm hp 0 u)] with k hu hv
    change normalizedFreeFunction (m 0 k) * GW.Fock.vacuumAdapterIsometry u k =
      GW.Fock.vacuumAdapterIsometry (sectorNormalizedSymbol m hm hp 0 u) k
    rw [hu, hv, show k = 0 from Subsingleton.elim _ _]
    rfl
  | succ n =>
    exact boundedSymmetricMultiplier_ae (n+1) (normalizedFreeFunction ∘ m (n+1))
      (normalizedFreeFunction_measurable.comp (hm (n+1)))
      (fun k => normalizedFreeFunction_bound (m (n+1) k))
      (fun τ k => congrArg normalizedFreeFunction (hp (n+1) τ k)) u

def fockNormalizedAction : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  GW.Spaces.diagonalMap (sectorNormalizedSymbol m hm hp) zero_le_one (sectorNormalizedSymbol_norm m hm hp)

theorem fockRealMultiplier_contains_graphWeight
    (u : (fockSymbolWeightedGraph m hm hp).domain) :
    (u : GW.Fock.Carrier) ∈ (fockRealMultiplier m).domain := by
  obtain ⟨z,hz⟩ := (fockWeightedDomain_iff (fockGraphSymbolWeight m)
    (fockGraphSymbolWeight_measurable m hm) (fockGraphSymbolWeight_lower m)
    (fockGraphSymbolWeight_permutation m hp) (u : GW.Fock.Carrier)).mp u.property
  apply (fockRealMultiplier m).mem_domain_of_mem_graph (y := fockNormalizedAction m hm hp z)
  apply (fockRealMultiplier_graph_ae_iff m _ _).mpr
  intro n
  change (fun k => (m n k : ℂ) • physicalSector n ((u : GW.Fock.Carrier) n) k) =ᵐ[GW.Fock.sectorMeasure n]
    physicalSector n (sectorNormalizedSymbol m hm hp n (z n))
  filter_upwards [hz n, sectorNormalizedSymbol_ae m hm hp n (z n)] with k hu hv
  simp only [smul_eq_mul] at hu hv
  rw [← hv, ← hu]
  have hne : fockGraphSymbolWeight m n k ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (fockGraphSymbolWeight_lower m n k))
  have hn : normalizedFreeFunction (m n k) * (fockGraphSymbolWeight m n k : ℂ) = (m n k : ℂ) := by
    change ((m n k / fockGraphSymbolWeight m n k : ℝ) : ℂ) *
      (fockGraphSymbolWeight m n k : ℂ) = (m n k : ℂ)
    rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hne]
  rw [← mul_assoc, hn]
  simp only [smul_eq_mul]

include hm hp in
theorem fockRealMultiplier_dense : Dense ((fockRealMultiplier m).domain : Set GW.Fock.Carrier) := by
  let G := fockSymbolWeightedGraph m hm hp
  have hr : Set.range G.embedding = (G.domain : Set GW.Fock.Carrier) := by
    ext u
    constructor
    · rintro ⟨x,rfl⟩
      exact G.embedding_mem x
    · intro hu
      exact ⟨G.product ⟨u,hu⟩,G.embedding_product _⟩
  have hd := G.embedding_dense
  change Dense (Set.range G.embedding) at hd
  rw [hr] at hd
  have hsub : (G.domain : Set GW.Fock.Carrier) ⊆ ((fockRealMultiplier m).domain : Set GW.Fock.Carrier) :=
    fun u hu => fockRealMultiplier_contains_graphWeight m hm hp ⟨u,hu⟩
  exact hd.mono hsub


end SymmetricSymbols

/-- The earlier free construction is exactly this same maximal multiplication
operator, not a second domain or normalization. -/
theorem freeFiberOperator_eq_fockRealMultiplier (P : GW.Space) :
    freeFiberOperator P = fockRealMultiplier (freeSymbol P) := by
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    rintro ⟨u,v⟩ h
    exact (fockRealMultiplier_graph_ae_iff _ u v).mpr ((freeFiberOperator_graph_ae_iff P u v).mp h)
  · apply LinearPMap.le_of_le_graph
    rintro ⟨u,v⟩ h
    exact (freeFiberOperator_graph_ae_iff P u v).mpr ((fockRealMultiplier_graph_ae_iff _ u v).mp h)

end Froehlich
