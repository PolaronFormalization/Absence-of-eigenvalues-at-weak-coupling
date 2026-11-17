import Froehlich.Nodes.FC07CutoffCore
import Froehlich.Nodes.FC07CreationComm
import Froehlich.Nodes.FC07Interpretation

/-! Actual uncompressed finite-cutoff moving-Hamiltonian pullthrough. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

theorem creationRestriction_core_graph (f : GW.OnePhonon) (u : boundedMomentumCore) :
    ((u : GW.Fock.Carrier),creationRestriction f (coreNumberLift u)) ∈ (GW.Fock.ordinaryCreation f).graph := by
  have h := (GW.Fock.ordinaryCreation f).mem_graph
    (GW.Fock.ordinaryCreationRootInput f (numberFormRootInput (coreNumberLift u)))
  change (numberFormEmbedding (coreNumberLift u),creationRestriction f (coreNumberLift u)) ∈ _ at h
  rwa [coreNumberLift_embedding] at h

theorem annihilationRestriction_core_graph (f : GW.OnePhonon) (u : boundedMomentumCore) :
    ((u : GW.Fock.Carrier),annihilationRestriction f (coreNumberLift u)) ∈ (GW.Fock.ordinaryAnnihilation f).graph := by
  have h := (GW.Fock.ordinaryAnnihilation f).mem_graph
    (GW.Fock.ordinaryAnnihilationRootInput f (numberFormRootInput (coreNumberLift u)))
  change (numberFormEmbedding (coreNumberLift u),annihilationRestriction f (coreNumberLift u)) ∈ _ at h
  rwa [coreNumberLift_embedding] at h

theorem core_field_creation_CCR (S : ℕ) (hS : 1 ≤ S) (f : GW.OnePhonon)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), (S : ℝ) < ‖k‖ → f k = 0)
    (u : boundedMomentumCore) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∀ q : boundedMomentumCore,
      (q : GW.Fock.Carrier) = annihilationField (coreNumberLift u) k →
      annihilationField (coreNumberLift (coreCreationAction S hS f hf u)) k =
        creationRestriction f (coreNumberLift q) + f k • (u : GW.Fock.Carrier) := by
  obtain ⟨M,R,hM,hR,hfinite,hsupport⟩ := boundedMomentumCore_support u
  have hcut : lowSectorProjection M (u : GW.Fock.Carrier) = (u : GW.Fock.Carrier) :=
    lowSectorProjection_eq_of_bound M _ hfinite
  have hbase : finiteRootLift M (u : GW.Fock.Carrier) = coreNumberLift u := by
    apply numberFormEmbedding_injective
    rw [finiteRootLift_embedding,coreNumberLift_embedding]
    exact hcut
  have hcreate : finiteCreationMap M f (u : GW.Fock.Carrier) = creationRestriction f (coreNumberLift u) := by
    change creationRestriction f (finiteRootLift M (u : GW.Fock.Carrier)) = _
    rw [hbase]
  have houtput : finiteRootLift (M+1) (finiteCreationMap M f (u : GW.Fock.Carrier)) =
      coreNumberLift (coreCreationAction S hS f hf u) := by
    apply numberFormEmbedding_injective
    rw [finiteRootLift_embedding,coreNumberLift_embedding]
    change lowSectorProjection (M+1) (finiteCreationMap M f (u : GW.Fock.Carrier)) =
      creationRestriction f (coreNumberLift u)
    rw [← hcreate]
    exact finiteCreationMap_cutoff M f (u : GW.Fock.Carrier)
  have h := finite_field_creation_actual_CCR M f (u : GW.Fock.Carrier)
  rw [hbase,houtput,hcut] at h
  filter_upwards [h] with k hk
  intro q hq
  have he := (GW.Fock.ordinaryCreation f).mem_graph_snd_inj hk.1
    (creationRestriction_core_graph f q) hq.symm
  exact hk.2.trans (congrArg (fun z : GW.Fock.Carrier => z + f k • (u : GW.Fock.Carrier)) he)

theorem core_field_annihilation_CCR (f : GW.OnePhonon) (u : boundedMomentumCore) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∀ q : boundedMomentumCore,
      (q : GW.Fock.Carrier) = annihilationField (coreNumberLift u) k →
      annihilationField (coreNumberLift (coreAnnihilationAction f u)) k =
        annihilationRestriction f (coreNumberLift q) := by
  obtain ⟨M,R,hM,hR,hfinite,hsupport⟩ := boundedMomentumCore_support u
  have hbase : finiteRootLift M (u : GW.Fock.Carrier) = coreNumberLift u := by
    apply numberFormEmbedding_injective
    rw [finiteRootLift_embedding,coreNumberLift_embedding]
    exact lowSectorProjection_eq_of_bound M _ hfinite
  have hannihilate : finiteAnnihilationMap M f (u : GW.Fock.Carrier) =
      annihilationRestriction f (coreNumberLift u) := by
    change annihilationRestriction f (finiteRootLift M (u : GW.Fock.Carrier)) = _
    rw [hbase]
  have houtput : finiteRootLift M (finiteAnnihilationMap M f (u : GW.Fock.Carrier)) =
      coreNumberLift (coreAnnihilationAction f u) := by
    apply numberFormEmbedding_injective
    rw [finiteRootLift_embedding,coreNumberLift_embedding]
    change lowSectorProjection M (finiteAnnihilationMap M f (u : GW.Fock.Carrier)) =
      annihilationRestriction f (coreNumberLift u)
    rw [← hannihilate]
    exact finiteAnnihilationMap_cutoff M f (u : GW.Fock.Carrier)
  have h := finite_field_annihilation_actual_CCR M f (u : GW.Fock.Carrier)
  rw [hbase,houtput] at h
  filter_upwards [h] with k hk
  intro q hq
  have he := (GW.Fock.ordinaryAnnihilation f).mem_graph_snd_inj hk.1
    (annihilationRestriction_core_graph f q) hq.symm
  exact hk.2.trans he

end Froehlich
