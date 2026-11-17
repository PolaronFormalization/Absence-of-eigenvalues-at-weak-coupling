import Froehlich.Nodes.GW06Compression

/-! Full weak domains and actions of the actual closed-sector operators. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def compressedFormCoordinate (g : ℝ) (P : GW.Space) (n : ℕ)
    (i : Option GW.Operators.PositiveCutoff) (u : (compressedHamiltonian g P n i).domain) : HighEnergySpace P n :=
  GW.Operators.operatorFormCoordinate (compressedFiberFormData g P n i) u

theorem compressedFormCoordinate_embedding (g : ℝ) (P : GW.Space) (n : ℕ)
    (i : Option GW.Operators.PositiveCutoff) (u : (compressedHamiltonian g P n i).domain) :
    highEnergyEmbedding P n (compressedFormCoordinate g P n i u) = (u : HighSectorSpace n) :=
  GW.Operators.operatorFormCoordinate_embedding (compressedFiberFormData g P n i) u

theorem compressedHamiltonian_form_identity (g : ℝ) (P : GW.Space) (n : ℕ)
    (i : Option GW.Operators.PositiveCutoff) (u : (compressedHamiltonian g P n i).domain)
    (w : HighEnergySpace P n) :
    (fiberFormData g P i).form w (compressedFormCoordinate g P n i u) =
      ⟪highEnergyEmbedding P n w,compressedHamiltonian g P n i u⟫_ℂ :=
  GW.Operators.formOperator_form_identity (compressedFiberFormData g P n i) u w

theorem compressedHamiltonian_domain_of_equation (g : ℝ) (P : GW.Space) (n : ℕ)
    (i : Option GW.Operators.PositiveCutoff) (u : HighEnergySpace P n) (f : HighSectorSpace n)
    (h : ∀ w : HighEnergySpace P n, (fiberFormData g P i).form w u = ⟪highEnergyEmbedding P n w,f⟫_ℂ) :
    ∃ hm : highEnergyEmbedding P n u ∈ (compressedHamiltonian g P n i).domain,
      compressedHamiltonian g P n i ⟨highEnergyEmbedding P n u,hm⟩ = f :=
  GW.Operators.formOperator_domain_of_equation (compressedFiberFormData g P n i) u f h

theorem compressedHamiltonian_graph_iff (g : ℝ) (P : GW.Space) (n : ℕ)
    (i : Option GW.Operators.PositiveCutoff) (u f : HighSectorSpace n) :
    (u,f) ∈ (compressedHamiltonian g P n i).graph ↔
      ∃ x : HighEnergySpace P n, highEnergyEmbedding P n x = u ∧
        ∀ w : HighEnergySpace P n, (fiberFormData g P i).form w x = ⟪highEnergyEmbedding P n w,f⟫_ℂ := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ := (compressedHamiltonian g P n i).mem_graph_iff'.mp h
    refine ⟨compressedFormCoordinate g P n i x, ?_, ?_⟩
    · exact (compressedFormCoordinate_embedding g P n i x).trans (congrArg Prod.fst hx)
    · intro w
      exact (compressedHamiltonian_form_identity g P n i x w).trans
        (congrArg (fun z : HighSectorSpace n => ⟪highEnergyEmbedding P n w,z⟫_ℂ) (congrArg Prod.snd hx))
  · rintro ⟨x,hx,h⟩
    obtain ⟨hm,hv⟩ := compressedHamiltonian_domain_of_equation g P n i x f h
    exact (compressedHamiltonian g P n i).mem_graph_iff.mpr ⟨⟨highEnergyEmbedding P n x,hm⟩,hx,hv⟩

end Froehlich
