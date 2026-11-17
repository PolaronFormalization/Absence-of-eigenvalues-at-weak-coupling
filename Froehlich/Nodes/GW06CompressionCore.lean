import Froehlich.Nodes.GW06CompressionAction
import Froehlich.Nodes.FC07CutoffAction

/-! Finite-cutoff core vectors belong to the actual compressed operator
with the projected full cutoff action. No arbitrary compression assertion. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def coreHighEnergyLift (P : GW.Space) (n : ℕ) (u : boundedMomentumCore)
    (hu : (u : GW.Fock.Carrier) ∈ HighSectorSpace n) : HighEnergySpace P n :=
  ⟨coreEnergyLift P u, (highEnergy_mem_iff P n _).mpr (by
    apply energyEmbedding_injective P
    rw [energyHighProjection_intertwines, coreEnergyLift_embedding]
    exact (highSector_mem_iff n u).mp hu)⟩

theorem coreHighEnergyLift_embedding (P : GW.Space) (n : ℕ) (u : boundedMomentumCore)
    (hu : (u : GW.Fock.Carrier) ∈ HighSectorSpace n) :
    highEnergyEmbedding P n (coreHighEnergyLift P n u hu) = ⟨(u : GW.Fock.Carrier),hu⟩ := by
  apply Subtype.ext
  exact coreEnergyLift_embedding P u

theorem compressedCutoff_core_weak (g : ℝ) (P : GW.Space) (n : ℕ)
    (Λ : GW.Operators.PositiveCutoff) (u : boundedMomentumCore)
    (hu : (u : GW.Fock.Carrier) ∈ HighSectorSpace n) (w : HighEnergySpace P n) :
    (fiberFormData g P (some Λ)).form w (coreHighEnergyLift P n u hu) =
      ⟪highEnergyEmbedding P n w,highSectorProject n (coreCutoffAction g P Λ u)⟫_ℂ := by
  change (fiberFormData g P (some Λ)).form (w : EnergySpace P) (coreEnergyLift P u) =
    ⟪energyEmbedding P w,highSectorProjection n (coreCutoffAction g P Λ u)⟫_ℂ
  have hp : highSectorProjection n (energyEmbedding P w) = energyEmbedding P w :=
    (highSector_mem_iff n _).mp (highEnergyEmbedding P n w).property
  have hi := highSectorProjection_pairing n (energyEmbedding P w) (coreCutoffAction g P Λ u)
  rw [hp] at hi
  exact (coreCutoffAction_weak g P Λ u w).trans hi

theorem compressedCutoff_core_graph (g : ℝ) (P : GW.Space) (n : ℕ)
    (Λ : GW.Operators.PositiveCutoff) (u : boundedMomentumCore)
    (hu : (u : GW.Fock.Carrier) ∈ HighSectorSpace n) :
    ((⟨(u : GW.Fock.Carrier),hu⟩ : HighSectorSpace n),
      highSectorProject n (coreCutoffAction g P Λ u)) ∈ (compressedHamiltonian g P n (some Λ)).graph := by
  obtain ⟨hm,hv⟩ := compressedHamiltonian_domain_of_equation g P n (some Λ)
    (coreHighEnergyLift P n u hu) (highSectorProject n (coreCutoffAction g P Λ u))
    (compressedCutoff_core_weak g P n Λ u hu)
  exact (compressedHamiltonian g P n (some Λ)).mem_graph_iff.mpr
    ⟨⟨highEnergyEmbedding P n (coreHighEnergyLift P n u hu),hm⟩,
      coreHighEnergyLift_embedding P n u hu,hv⟩

end Froehlich
