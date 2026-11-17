import Froehlich.Nodes.UV02HighRelativeField
import Froehlich.Nodes.UV02HighFreeDomainInclusion

/-! The source fixed-cutoff Neumann solver on every compressed sector
lands in the actual full free domain and solves the full associated graph. -/
noncomputable section
namespace Froehlich
variable (g : ℝ) (P : GW.Space) (n : ℕ) (Λ : GW.Operators.PositiveCutoff) (c : ℝ) (hc : 1 ≤ c)
    (hsmall : ‖highShiftRelativeField P c hc n (cutoffFormFactorL2 g Λ.val Λ.property)‖<1/2)
include hsmall

theorem highCutoffShiftSolution_graph (z : HighSectorSpace n) :
    (highCutoffShiftSolution g P n Λ c hc z,z-(c : ℂ) • highCutoffShiftSolution g P n Λ c hc z) ∈
      (compressedHamiltonian g P n (some Λ)).graph := by
  let y := highCutoffShiftFactorInverse g P n Λ c hc z
  let u := freeShiftHighInverse P c hc n y
  have hfree : ((u : GW.Fock.Carrier),((y-(c : ℂ) • u : HighSectorSpace n) : GW.Fock.Carrier)) ∈
      (freeFiberOperator P).graph := freeShiftInverse_free_graph P c hc (y : GW.Fock.Carrier)
  obtain ⟨x,hx,hgraph⟩ := highFreeGraph_cutoffGraph g P n Λ u (y-(c : ℂ) • u) hfree
  have hx' : x=freeShiftHighEnergyInverse P c hc n y := by
    apply highEnergyEmbedding_injective P n
    rw [hx,freeShiftHighEnergyInverse_physical]
  rw [hx'] at hgraph
  have hproj : highSectorProject n (((y-(c : ℂ) • u : HighSectorSpace n) : GW.Fock.Carrier))=
      y-(c : ℂ) • u := by
    apply Subtype.ext
    exact (highSector_mem_iff n (y-(c : ℂ) • u)).mp (y-(c : ℂ) • u).property
  have hfield : highSectorProject n (energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property)
      (freeShiftHighEnergyInverse P c hc n y : EnergySpace P))=
      highShiftRelativeField P c hc n (cutoffFormFactorL2 g Λ.val Λ.property) y := rfl
  have hfactor := congrArg (fun T : HighSectorSpace n →L[ℂ] HighSectorSpace n => T z)
    (highCutoffShiftFactorInverse_right g P n Λ c hc hsmall)
  change y+highShiftRelativeField P c hc n (cutoffFormFactorL2 g Λ.val Λ.property) y=z at hfactor
  have he : highSectorProject n (((y-(c : ℂ) • u : HighSectorSpace n) : GW.Fock.Carrier)+
      energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property)
        (freeShiftHighEnergyInverse P c hc n y : EnergySpace P))=z-(c : ℂ) • u := by
    rw [map_add,hproj,hfield,←hfactor]
    abel
  rw [he] at hgraph
  exact hgraph

theorem highCutoffShiftSolution_mem_cutoff (z : HighSectorSpace n) :
    highCutoffShiftSolution g P n Λ c hc z ∈ (compressedHamiltonian g P n (some Λ)).domain :=
  (compressedHamiltonian g P n (some Λ)).mem_domain_of_mem_graph
    (highCutoffShiftSolution_graph g P n Λ c hc hsmall z)

theorem highCutoffShiftSolution_equation (z : HighSectorSpace n) :
    compressedHamiltonian g P n (some Λ)
      ⟨highCutoffShiftSolution g P n Λ c hc z,highCutoffShiftSolution_mem_cutoff g P n Λ c hc hsmall z⟩+
      (c : ℂ) • highCutoffShiftSolution g P n Λ c hc z=z := by
  have he := (compressedHamiltonian g P n (some Λ)).mem_graph_snd_inj
    ((compressedHamiltonian g P n (some Λ)).mem_graph
      ⟨highCutoffShiftSolution g P n Λ c hc z,highCutoffShiftSolution_mem_cutoff g P n Λ c hc hsmall z⟩)
    (highCutoffShiftSolution_graph g P n Λ c hc hsmall z) rfl
  rw [he,sub_add_cancel]

end Froehlich
