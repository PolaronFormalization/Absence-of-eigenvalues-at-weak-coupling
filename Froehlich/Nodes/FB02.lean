import Froehlich.Nodes.FB02Closedness
import Froehlich.Nodes.FB02SmallCoupling
import Froehlich.Nodes.FB02VacuumColumn
import Froehlich.Nodes.FB02SectorSelection
import Froehlich.Nodes.GW06Uniqueness
import Froehlich.Nodes.GW06CompressionAction
import Froehlich.Nodes.SY01IndexedGraph

/-! FB02 (`lem:cutoff`): source-level aggregation of the checked actual
closed fiber forms, associated operators, selection rules and symmetries. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem fb02_shiftedForm_complete (g : ℝ) (P : GW.Space) :
    CompleteSpace (GW.Operators.EnergySpace (fiberFormData g P none)) :=
  fiberShiftedForm_complete g P

theorem fb02_formDomain_unchanged (g : ℝ) (P : GW.Space) :
    Set.range (GW.Operators.completedEnergyEmbedding (fiberFormData g P none)) =
      Set.range (energyEmbedding P) := fiberForm_completion_range g P

theorem fb02_selfadjoint (g : ℝ) (P : GW.Space) :
    GW.IsSelfAdjointOperator (fiberHamiltonian g P) := fiberHamiltonian_selfadjoint g P

theorem fb02_compressed_selfadjoint (g : ℝ) (P : GW.Space) (n : ℕ)
    (i : Option GW.Operators.PositiveCutoff) :
    GW.IsSelfAdjointOperator (compressedHamiltonian g P n i) :=
  compressedHamiltonian_selfadjoint g P n i

theorem fb02_compressed_graph (g : ℝ) (P : GW.Space) (n : ℕ)
    (i : Option GW.Operators.PositiveCutoff) (u f : HighSectorSpace n) :
    (u,f) ∈ (compressedHamiltonian g P n i).graph ↔
      ∃ x : HighEnergySpace P n, highEnergyEmbedding P n x = u ∧
        ∀ w : HighEnergySpace P n, (fiberFormData g P i).form w x = ⟪highEnergyEmbedding P n w,f⟫_ℂ :=
  compressedHamiltonian_graph_iff g P n i u f

theorem fb02_domain (g : ℝ) (P : GW.Space) (u : GW.Fock.Carrier) :
    u ∈ (fiberHamiltonian g P).domain ↔
      ∃ x : EnergySpace P, energyEmbedding P x = u ∧ ∃ f : GW.Fock.Carrier,
        ∀ w : EnergySpace P, freeFiberForm P w x + singularInteraction g P w x =
          ⟪energyEmbedding P w,f⟫_ℂ := fiberHamiltonian_domain g P u

theorem fb02_graph (g : ℝ) (P : GW.Space) (u f : GW.Fock.Carrier) :
    (u,f) ∈ (fiberHamiltonian g P).graph ↔
      ∃ x : EnergySpace P, energyEmbedding P x = u ∧
        ∀ w, freeFiberForm P w x + singularInteraction g P w x = ⟪energyEmbedding P w,f⟫_ℂ :=
  fiberHamiltonian_graph_iff g P u f

theorem fb02_associated_unique (g : ℝ) (P : GW.Space)
    (L : GW.Fock.Carrier →ₗ.[ℂ] GW.Fock.Carrier) (hL : GW.IsSelfAdjointOperator L)
    (hform : ∀ x : L.domain, ∃ u : EnergySpace P, energyEmbedding P u = (x : GW.Fock.Carrier) ∧
      ∀ w, freeFiberForm P w u + singularInteraction g P w u = ⟪energyEmbedding P w,L x⟫_ℂ) :
    L = fiberHamiltonian g P := fiberHamiltonian_unique g P L hL hform

theorem fb02_semibounded (g : ℝ) (P : GW.Space) (x : EnergySpace P) :
    -(lyGlobalRemainder g)*‖energyEmbedding P x‖^2 ≤
      ((fiberFormData g P none).form x x).re := fiberForm_semibounded g P x

theorem fb02_operator_semibounded (g : ℝ) (P : GW.Space) (u : (fiberHamiltonian g P).domain) :
    -(lyGlobalRemainder g)*‖(u : GW.Fock.Carrier)‖^2 ≤
      (⟪(u : GW.Fock.Carrier),fiberHamiltonian g P u⟫_ℂ).re := fiberHamiltonian_semibounded g P u

theorem fb02_tail_mixed (g Λ : ℝ) (hΛ : 1 ≤ Λ) (P : GW.Space) (w u : EnergySpace P) :
    ‖(singularInteraction g P - cutoffInteractionForm g Λ (zero_lt_one.trans_le hΛ) P) w u‖ ≤
      (lyHighConstant*|g|/Real.sqrt Λ)*‖w‖*‖u‖ := singular_cutoff_error g Λ hΛ P w u

theorem fb02_tail_diagonal (g Λ : ℝ) (hΛ : 1 ≤ Λ) (P : GW.Space) (u : EnergySpace P) :
    ‖(singularInteraction g P - cutoffInteractionForm g Λ (zero_lt_one.trans_le hΛ) P) u u‖ ≤
      (lyHighConstant*|g|/Real.sqrt Λ)*‖u‖^2 := by
  exact (fb02_tail_mixed g Λ hΛ P u u).trans_eq (by ring)

theorem fb02_smallCoupling_mixed (g : ℝ) (P : GW.Space) (w u : EnergySpace P) (hg : |g| ≤ 1) :
    ‖singularInteraction g P w u‖ ≤ phiMixedConstant * |g| * ‖w‖ * ‖u‖ :=
  singularInteraction_mixed_small g P w u hg

theorem fb02_cutoff_selection (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space)
    (m n : ℕ) (w u : EnergySpace P) (hnm : n ≠ m+1) (hmn : m ≠ n+1) :
    cutoffInteractionForm g Λ hΛ P (energySectorProjection P n w) (energySectorProjection P m u) = 0 :=
  cutoffInteraction_sector_selection g Λ hΛ P m n w u hnm hmn

theorem fb02_singular_selection (g : ℝ) (P : GW.Space) (m n : ℕ) (w u : EnergySpace P)
    (hnm : n ≠ m+1) (hmn : m ≠ n+1) :
    singularInteraction g P (energySectorProjection P n w) (energySectorProjection P m u) = 0 :=
  singularInteraction_sector_selection g P m n w u hnm hmn

theorem fb02_vacuum_source (g : ℝ) (P : GW.Space) (w : EnergySpace P) :
    singularInteraction g P w (vacuumEnergyLift P) = fiberSourceLoad g P w :=
  singularInteraction_vacuum_column g P w

theorem fb02_form_conjugation (g : ℝ) (P : GW.Space) (w u : EnergySpace P) :
    (fiberFormData g P none).form (energyConjugation P w) (energyConjugation P u) =
      (starRingEnd ℂ) ((fiberFormData g P none).form w u) := fiberTotalForm_conjugation g P w u

theorem fb02_form_reflection (g : ℝ) (P : GW.Space) (w u : EnergySpace P) :
    (fiberFormData g (-P) none).form (energyReflection P w) (energyReflection P u) =
      (fiberFormData g P none).form w u := fiberTotalForm_reflection g P w u

theorem fb02_operator_conjugation (g : ℝ) (P : GW.Space) (u f : GW.Fock.Carrier) :
    (fockConjugation u,fockConjugation f) ∈ (fiberHamiltonian g P).graph ↔
      (u,f) ∈ (fiberHamiltonian g P).graph := indexedHamiltonian_graph_conjugation_iff g P none u f

theorem fb02_operator_reflection (g : ℝ) (P : GW.Space) (u f : GW.Fock.Carrier) :
    (fockReflection u,fockReflection f) ∈ (fiberHamiltonian g (-P)).graph ↔
      (u,f) ∈ (fiberHamiltonian g P).graph := indexedHamiltonian_graph_reflection_iff g P none u f

end Froehlich
