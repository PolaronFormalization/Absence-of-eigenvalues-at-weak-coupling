import Froehlich.Nodes.EN01Graph
import Froehlich.Nodes.EN02Number
import Froehlich.Nodes.EN02OneParticle

/-! FD02: assemble retained weighted-graph records on the canonical Hilbert
sum. The general maximal-multiplier and free weak-domain clauses are added
below as their precise source applications are integrated. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich
section WeightedSum
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
  (G : ∀ n, GW.Spaces.WeightedGraph (E n) (E n))

/-- Exact weighted-domain record, using the retained maximal partial direct sum. -/
def sumWeightedGraph : GW.Spaces.WeightedGraph (lp E 2) (lp E 2) where
  domain := (GW.Fock.operatorSum E (sectorWeightPartial G)).domain
  embedding := sumGraphEmbedding G
  embedding_injective := sumGraphEmbedding_injective G
  embedding_norm_le := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖GW.Spaces.diagonalLinear (fun n => (G n).embedding)
      (fun n => (G n).embedding_norm_le) x‖ ≤ 1 * ‖x‖
    exact GW.Spaces.diagonal_norm_bound (fun n => (G n).embedding) zero_le_one
      (fun n => (G n).embedding_norm_le) x
  embedding_dense := sumGraphEmbedding_dense G
  product := (GW.Fock.operatorSum E (sectorWeightPartial G)).toFun
  embedding_mem := fun x => (sumGraphEmbedding_range G).subset ⟨x, rfl⟩
  product_embedding := by
    intro x
    have hg : (sumGraphEmbedding G x, x) ∈
        (GW.Fock.operatorSum E (sectorWeightPartial G)).graph := by
      rw [GW.Fock.operatorSum_graph_iff]
      intro n
      have h := (sectorWeightPartial G n).mem_graph
        ⟨(G n).embedding (x n), (G n).embedding_mem (x n)⟩
      rw [sectorWeight_embedding] at h
      exact h
    exact (GW.Fock.operatorSum E (sectorWeightPartial G)).mem_graph_snd_inj
      ((GW.Fock.operatorSum E (sectorWeightPartial G)).mem_graph _) hg rfl
  embedding_product := by
    intro u
    apply lp.ext
    funext n
    change (G n).embedding (GW.Fock.operatorSum E (sectorWeightPartial G) u n) = (u : lp E 2) n
    rw [← GW.Fock.operatorSum_apply_component]
    exact (G n).embedding_product _

/-- The physical weighted domain carries the product norm, inherited through
an actual onto isometry, rather than the ambient subtype norm. -/
def weightedSumCoordinates :
    GW.Spaces.WeightedDomain (sumWeightedGraph G) ≃ₗᵢ[ℂ] lp E 2 :=
  GW.Spaces.weightedDomainIsometry (sumWeightedGraph G)

example [∀ n, CompleteSpace (E n)] :
    CompleteSpace (GW.Spaces.WeightedDomain (sumWeightedGraph G)) := inferInstance

theorem weightedSum_norm_sq (u : GW.Spaces.WeightedDomain (sumWeightedGraph G)) :
    ‖u‖ ^ 2 = ∑' n, ‖GW.Fock.operatorSum E (sectorWeightPartial G)
      (show (sumWeightedGraph G).domain from u) n‖ ^ 2 := by
  rw [GW.Spaces.weightedDomain_norm]
  exact GW.Analysis.lp_norm_sq _
end WeightedSum

theorem energyEmbedding_product (P : GW.Space) (u : (energyWeightOperator P).domain) :
    energyEmbedding P ((energyCoordinates P).symm (energyWeightOperator P u)) = (u : GW.Fock.Carrier) := by
  apply lp.ext
  funext n
  change sectorEnergyEmbedding P n
    (energyCoordinates P ((energyCoordinates P).symm (energyWeightOperator P u)) n) = (u : GW.Fock.Carrier) n
  rw [LinearIsometryEquiv.apply_symm_apply]
  have he := GW.Fock.operatorSum_apply_component GW.Fock.Sector (sectorEnergyWeightOperator P) u n
  change sectorEnergyWeightOperator P n
    (GW.Fock.operatorSumInput GW.Fock.Sector (sectorEnergyWeightOperator P) u n) = energyWeightOperator P u n at he
  rw [← he]
  exact sectorEnergyEmbedding_weight P n _

/-- The accepted energy construction is a complete physical weighted domain
with its actual maximal weight-multiplication operator. -/
def energyWeightedGraph (P : GW.Space) : GW.Spaces.WeightedGraph GW.Fock.Carrier (EnergySpace P) where
  domain := (energyWeightOperator P).domain
  embedding := energyEmbedding P
  embedding_injective := energyEmbedding_injective P
  embedding_norm_le := energyEmbedding_opNorm P
  embedding_dense := energyEmbedding_dense P
  product := (energyCoordinates P).symm.toLinearMap.comp (energyWeightOperator P).toFun
  embedding_mem := energyEmbedding_mem_domain P
  product_embedding := by
    intro x
    apply energyEmbedding_injective P
    change energyEmbedding P ((energyCoordinates P).symm
      (energyWeightOperator P ⟨energyEmbedding P x, energyEmbedding_mem_domain P x⟩)) = energyEmbedding P x
    exact energyEmbedding_product P _
  embedding_product := energyEmbedding_product P


section MaximalMultiplication
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem realMultiplier_graph_ae_iff (m : X → ℝ) (u v : Lp ℂ 2 μ) :
    (u,v) ∈ (GW.Analysis.realMultiplier m μ).graph ↔
      (fun x => (m x : ℂ) • u x) =ᵐ[μ] v := by
  constructor
  · intro h
    obtain ⟨w, hw, hv⟩ := (GW.Analysis.realMultiplier m μ).mem_graph_iff.mp h
    simpa only [hw, hv] using GW.Analysis.realMultiplier_ae m w
  · intro h
    let w : (GW.Analysis.realMultiplier m μ).domain := ⟨u, ⟨v,h⟩⟩
    apply (GW.Analysis.realMultiplier m μ).mem_graph_iff.mpr
    refine ⟨w, rfl, ?_⟩
    apply Lp.ext
    exact (GW.Analysis.realMultiplier_ae m w).symm.trans h
end MaximalMultiplication

theorem freeFiberOperator_graph_ae_iff (P : GW.Space) (u v : GW.Fock.Carrier) :
    (u,v) ∈ (freeFiberOperator P).graph ↔
      ∀ n, (fun k => (freeSymbol P n k : ℂ) • physicalSector n (u n) k) =ᵐ[GW.Fock.sectorMeasure n]
        physicalSector n (v n) := by
  constructor
  · intro h
    obtain ⟨w, hw, hv⟩ := (freeFiberOperator P).mem_graph_iff.mp h
    simpa only [hw, hv] using freeFiberOperator_ae P w
  · intro h
    obtain ⟨hu, hv⟩ := (freeFiberOperator_domain_action_iff P u v).mpr h
    exact (freeFiberOperator P).mem_graph_iff.mpr ⟨⟨u,hu⟩, rfl, hv⟩

theorem freeFiberOperator_closed (P : GW.Space) : (freeFiberOperator P).IsClosed := by
  change IsClosed ((freeFiberOperator P).graph : Set (GW.Fock.Carrier × GW.Fock.Carrier))
  have he : ((freeFiberOperator P).graph : Set (GW.Fock.Carrier × GW.Fock.Carrier)) =
      ⋂ n, (fun p : GW.Fock.Carrier × GW.Fock.Carrier =>
        (physicalSector n (p.1 n), physicalSector n (p.2 n))) ⁻¹'
          ((GW.Analysis.realMultiplier (H := ℂ) (freeSymbol P n) (GW.Fock.sectorMeasure n)).graph :
            Set (GW.Fock.AmbientSector n × GW.Fock.AmbientSector n)) := by
    ext p
    rcases p with ⟨u,v⟩
    simp only [Set.mem_iInter, Set.mem_preimage]
    exact (freeFiberOperator_graph_ae_iff P u v).trans
      (forall_congr' (fun n => (realMultiplier_graph_ae_iff _ _ _).symm))
  rw [he]
  apply isClosed_iInter
  intro n
  have hc : Continuous (fun p : GW.Fock.Carrier × GW.Fock.Carrier =>
      (physicalSector n (p.1 n), physicalSector n (p.2 n))) :=
    ((physicalSector n).continuous.comp
      ((lp.evalCLM ℂ GW.Fock.Sector 2 n).continuous.comp continuous_fst)).prodMk
        ((physicalSector n).continuous.comp
          ((lp.evalCLM ℂ GW.Fock.Sector 2 n).continuous.comp continuous_snd))
  exact (GW.Analysis.realMultiplier_closed (μ := GW.Fock.sectorMeasure n)
    (H := ℂ) (freeSymbol_measurable P n)).preimage hc

theorem freeFiberOperator_dense (P : GW.Space) :
    Dense ((freeFiberOperator P).domain : Set GW.Fock.Carrier) := by
  change Dense ((graphWeightOperator P).domain : Set GW.Fock.Carrier)
  rw [← graphEmbedding_range P]
  exact graphEmbedding_dense P

end Froehlich
