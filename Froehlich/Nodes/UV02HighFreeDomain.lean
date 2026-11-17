import Froehlich.Nodes.UV02HighFreeDomainInclusion

/-! The free domain on a high sector is literally the preimage of the
maximal full free domain. Its output remains in the same closed sector. -/
noncomputable section
open MeasureTheory Filter
namespace Froehlich

def HighFreePhysicalDomain (P : GW.Space) (n : ℕ) : Submodule ℂ (HighSectorSpace n) :=
  (freeFiberOperator P).domain.comap (HighSectorSpace n).subtype

theorem freeGraph_preserves_high (P : GW.Space) (n : ℕ) (u : HighSectorSpace n) (f : GW.Fock.Carrier)
    (hgraph : ((u : GW.Fock.Carrier),f) ∈ (freeFiberOperator P).graph) : f ∈ HighSectorSpace n := by
  apply (highSector_mem_iff n f).mpr
  apply lp.ext
  funext m
  rw [highSectorProjection_apply]
  split_ifs with hnm
  · rfl
  · have hu : (u : GW.Fock.Carrier) m=0 := by
      have h := congrArg (fun v : GW.Fock.Carrier => v m) ((highSector_mem_iff n u).mp u.property)
      rw [highSectorProjection_apply,if_neg hnm] at h
      exact h.symm
    apply (physicalSector m).injective
    apply Lp.ext
    rw [map_zero]
    have hg := (freeFiberOperator_graph_ae_iff P u f).mp hgraph m
    rw [hu,map_zero] at hg
    filter_upwards [hg,Lp.coeFn_zero (E := ℂ) (p := 2) (μ := GW.Fock.sectorMeasure m)] with K hg hz
    simp only [hz,Pi.zero_apply,smul_zero] at hg
    exact hz.trans hg

theorem highFreeDomain_subset_cutoffDomain (g : ℝ) (P : GW.Space) (n : ℕ)
    (Λ : GW.Operators.PositiveCutoff) :
    HighFreePhysicalDomain P n ≤ (compressedHamiltonian g P n (some Λ)).domain := by
  intro u hu
  have hmem : (u : GW.Fock.Carrier) ∈ (freeFiberOperator P).domain := hu
  let f := freeFiberOperator P ⟨u,hmem⟩
  have hgraph : ((u : GW.Fock.Carrier),f) ∈ (freeFiberOperator P).graph :=
    (freeFiberOperator P).mem_graph ⟨u,hmem⟩
  let F : HighSectorSpace n := ⟨f,freeGraph_preserves_high P n u f hgraph⟩
  obtain ⟨x,hx,hcut⟩ := highFreeGraph_cutoffGraph g P n Λ u F hgraph
  exact (compressedHamiltonian g P n (some Λ)).mem_domain_of_mem_graph hcut

end Froehlich
