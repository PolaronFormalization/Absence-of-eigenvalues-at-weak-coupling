import Froehlich.Nodes.UV02FreeDomainInclusion
import Froehlich.Nodes.GW06CompressionAction

/-! Full high-energy tests give the literal projected cutoff field action
on every actual high-sector vector in the free maximal domain. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem highEnergy_test_projection_pairing (P : GW.Space) (n : ℕ)
    (w : HighEnergySpace P n) (q : GW.Fock.Carrier) :
    ⟪highEnergyEmbedding P n w,highSectorProject n q⟫_ℂ=
      ⟪energyEmbedding P (w : EnergySpace P),q⟫_ℂ := by
  change ⟪(highEnergyEmbedding P n w : GW.Fock.Carrier),highSectorProjection n q⟫_ℂ=_
  rw [←highSectorProjection_pairing]
  rw [(highSector_mem_iff n (highEnergyEmbedding P n w)).mp (highEnergyEmbedding P n w).property]
  rw [highEnergyEmbedding_apply]

theorem highFreeGraph_cutoffGraph (g : ℝ) (P : GW.Space) (n : ℕ)
    (Λ : GW.Operators.PositiveCutoff) (u f : HighSectorSpace n)
    (hfree : ((u : GW.Fock.Carrier),(f : GW.Fock.Carrier)) ∈ (freeFiberOperator P).graph) :
    ∃ x : HighEnergySpace P n, highEnergyEmbedding P n x=u ∧
      (u,highSectorProject n ((f : GW.Fock.Carrier)+
        energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property) (x : EnergySpace P))) ∈
          (compressedHamiltonian g P n (some Λ)).graph := by
  obtain ⟨x,hx,hweak⟩ := (freeFiberOperator_graph_weak_iff P u f).mp hfree
  have hxh : x ∈ HighEnergySpace P n := by
    apply (highEnergy_mem_iff P n x).mpr
    apply energyEmbedding_injective P
    rw [energyHighProjection_intertwines,hx]
    exact (highSector_mem_iff n u).mp u.property
  let X : HighEnergySpace P n := ⟨x,hxh⟩
  have hX : highEnergyEmbedding P n X=u := by apply Subtype.ext; exact hx
  refine ⟨X,hX,?_⟩
  apply (compressedHamiltonian_graph_iff g P n (some Λ) _ _).mpr
  refine ⟨X,hX,?_⟩
  intro w
  calc
    _ = ⟪energyEmbedding P (w : EnergySpace P),(f : GW.Fock.Carrier)+
        energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property) x⟫_ℂ := by
      rw [fiberFormData_cutoff_apply,hweak (w : EnergySpace P),inner_add_right]
      change ⟪energyEmbedding P (w : EnergySpace P),(f : GW.Fock.Carrier)⟫_ℂ+
        ⟪energyEmbedding P (w : EnergySpace P),energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property) x⟫_ℂ=_
      rfl
    _ = _ := (highEnergy_test_projection_pairing P n w _).symm

end Froehlich
