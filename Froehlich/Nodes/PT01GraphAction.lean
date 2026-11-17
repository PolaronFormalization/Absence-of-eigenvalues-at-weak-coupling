import Froehlich.Nodes.UV02
import Froehlich.Nodes.FC07ProjectedCore
import Froehlich.Nodes.FC04Assembly

set_option autoImplicit false

/-! The finite-cutoff field is a bounded map on the actual free graph.
Consequently the physical shifted outputs, rather than their annihilation
fields, can be passed to the free-graph limit in PT01. -/
noncomputable section
namespace Froehlich

def freeGraphInput (P : GW.Space) (x : OperatorGraphSpace P) : (freeFiberOperator P).domain :=
  ⟨graphEmbedding P x,graphEmbedding_mem_domain P x⟩

theorem freeGraphInput_coordinate (P : GW.Space) (x : OperatorGraphSpace P) :
    (graphCoordinates P).symm (graphWeightOperator P (freeGraphInput P x)) = x := by
  apply graphEmbedding_injective P
  exact graphEmbedding_product P (freeGraphInput P x)

theorem freeGraphInput_action (P : GW.Space) (x : OperatorGraphSpace P) :
    freeFiberOperator P (freeGraphInput P x) = freeActionOnGraph P x := by
  change freeActionOnGraph P
    ((graphCoordinates P).symm (graphWeightOperator P (freeGraphInput P x))) = _
  rw [freeGraphInput_coordinate]

theorem freeGraphNumberCoordinates_freeEnergy (P : GW.Space) (x : OperatorGraphSpace P) :
    freeGraphNumberCoordinates P x = energyNumberCoordinates P
      (freeDomainEnergyCoordinate P (freeGraphInput P x)) := by
  apply numberFormEmbedding_injective
  rw [freeGraphNumberCoordinates_embedding,energyNumberCoordinates_intertwines,
    freeDomainEnergyCoordinate_physical]
  rfl

def cutoffFreeGraphAction (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) :
    OperatorGraphSpace P →L[ℂ] GW.Fock.Carrier :=
  freeActionOnGraph P + (fieldRestriction (cutoffFormFactorL2 g Λ.val Λ.property)).comp
    (freeGraphNumberCoordinates P)

theorem cutoffFreeGraphAction_actual (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (x : OperatorGraphSpace P) :
    cutoffHamiltonian g P Λ
      ⟨graphEmbedding P x,freeDomain_subset_cutoffDomain g P Λ (freeGraphInput P x).property⟩ =
        cutoffFreeGraphAction g P Λ x := by
  have h := cutoff_freeDomain_action g P Λ (freeGraphInput P x)
  rw [freeGraphInput_action] at h
  change _ = freeActionOnGraph P x + fieldRestriction (cutoffFormFactorL2 g Λ.val Λ.property)
    (freeGraphNumberCoordinates P x)
  rw [freeGraphNumberCoordinates_freeEnergy]
  exact h

theorem cutoffFreeGraphAction_core (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (u : boundedMomentumCore) :
    cutoffFreeGraphAction g P Λ (coreFreeGraphLift P u) = coreCutoffAction g P Λ u := by
  have h := cutoffFreeGraphAction_actual g P Λ (coreFreeGraphLift P u)
  have hg := (cutoffHamiltonian g P Λ).mem_graph
    ⟨graphEmbedding P (coreFreeGraphLift P u),
      freeDomain_subset_cutoffDomain g P Λ (freeGraphInput P (coreFreeGraphLift P u)).property⟩
  rw [h] at hg
  change (graphEmbedding P (coreFreeGraphLift P u),
    cutoffFreeGraphAction g P Λ (coreFreeGraphLift P u)) ∈ (cutoffHamiltonian g P Λ).graph at hg
  rw [coreFreeGraphLift_embedding] at hg
  exact (cutoffHamiltonian g P Λ).mem_graph_snd_inj hg (cutoffHamiltonian_core_graph g P Λ u) rfl

def cutoffShiftFreeGraphAction (g : ℝ) (P : GW.Space) (n : ℕ)
    (Λ : GW.Operators.PositiveCutoff) (e : ℝ) : OperatorGraphSpace P →L[ℂ] GW.Fock.Carrier :=
  (highSectorProjection n).comp (cutoffFreeGraphAction g P Λ) -
    ((e-1+(n : ℝ) : ℝ) : ℂ) • graphEmbedding P

theorem cutoffShiftFreeGraphAction_core (g : ℝ) (P : GW.Space) (n : ℕ)
    (Λ : GW.Operators.PositiveCutoff) (e : ℝ) (u : boundedMomentumCore) :
    cutoffShiftFreeGraphAction g P n Λ e (coreFreeGraphLift P u) =
      (coreProjectedCutoffShiftAction g P n Λ e u : GW.Fock.Carrier) := by
  change highSectorProjection n (cutoffFreeGraphAction g P Λ (coreFreeGraphLift P u)) -
    ((e-1+(n : ℝ) : ℝ) : ℂ) • graphEmbedding P (coreFreeGraphLift P u) = _
  rw [cutoffFreeGraphAction_core,coreFreeGraphLift_embedding]
  rfl

end Froehlich
