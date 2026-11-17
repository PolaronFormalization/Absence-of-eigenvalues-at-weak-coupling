import Froehlich.Nodes.PT01GraphAction
import Froehlich.Nodes.PT01CutoffGraph

set_option autoImplicit false

/-! The bounded shifted graph action is the actual compressed maximal
operator action, and equals the physical source at its cutoff resolvent. -/
noncomputable section
namespace Froehlich

theorem cutoffShiftFreeGraphAction_high_graph (g : ℝ) (P : GW.Space) (n : ℕ)
    (Λ : GW.Operators.PositiveCutoff) (e : ℝ) (x : OperatorGraphSpace P)
    (hx : graphEmbedding P x ∈ HighSectorSpace n) :
    ∃ r : HighSectorSpace n,
      (r : GW.Fock.Carrier) = cutoffShiftFreeGraphAction g P n Λ e x ∧
      (⟨graphEmbedding P x,hx⟩,r) ∈
        (GW.Operators.complexShift (compressedHamiltonian g P n (some Λ))
          ((e-1+(n : ℝ) : ℝ) : ℂ)).graph := by
  let q : HighSectorSpace n := ⟨graphEmbedding P x,hx⟩
  have hfree : ((q : GW.Fock.Carrier),freeActionOnGraph P x) ∈ (freeFiberOperator P).graph := by
    have h := (freeFiberOperator P).mem_graph (freeGraphInput P x)
    rw [freeGraphInput_action] at h
    exact h
  let f : HighSectorSpace n := ⟨freeActionOnGraph P x,freeGraph_preserves_high P n q _ hfree⟩
  obtain ⟨y,hy,hcut⟩ := highFreeGraph_cutoffGraph g P n Λ q f hfree
  have hyN : energyNumberCoordinates P (y : EnergySpace P) = freeGraphNumberCoordinates P x := by
    apply numberFormEmbedding_injective
    rw [energyNumberCoordinates_intertwines,freeGraphNumberCoordinates_embedding]
    exact congrArg (fun u : HighSectorSpace n => (u : GW.Fock.Carrier)) hy
  let b : HighSectorSpace n := highSectorProject n
    ((f : GW.Fock.Carrier)+energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property) y)
  let c : ℂ := ((e-1+(n : ℝ) : ℝ) : ℂ)
  let r : HighSectorSpace n := b-c • q
  refine ⟨r,?_,?_⟩
  · change highSectorProjection n (freeActionOnGraph P x+
      energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property) y) - c • graphEmbedding P x = _
    change highSectorProjection n (freeActionOnGraph P x+
      fieldRestriction (cutoffFormFactorL2 g Λ.val Λ.property) (energyNumberCoordinates P y)) -
        c • graphEmbedding P x = _
    rw [hyN]
    rfl
  · apply (GW.Operators.complexShift_graph_iff _ _ _).mpr
    change (q,(b-c • q)+c • q) ∈ (compressedHamiltonian g P n (some Λ)).graph
    rw [sub_add_cancel]
    exact hcut

theorem cutoffShiftFreeGraphAction_resolvent (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (Λ : GW.Operators.PositiveCutoff)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (f : HighSectorSpace n) :
    cutoffShiftFreeGraphAction g (-p) n Λ e
      (cutoffAuxiliaryGraphCoordinate n e p hn he Λ g hg hs f) = (f : GW.Fock.Carrier) := by
  let x := cutoffAuxiliaryGraphCoordinate n e p hn he Λ g hg hs f
  have hx : graphEmbedding (-p) x ∈ HighSectorSpace n := by
    rw [cutoffAuxiliaryGraphCoordinate_physical]
    exact (cutoffAuxiliaryResolvent n e p he Λ g hg hs f).property
  obtain ⟨r,hr,hgraph⟩ := cutoffShiftFreeGraphAction_high_graph g (-p) n Λ e x hx
  have hq : (⟨graphEmbedding (-p) x,hx⟩ : HighSectorSpace n) =
      cutoffAuxiliaryResolvent n e p he Λ g hg hs f := by
    apply Subtype.ext
    exact cutoffAuxiliaryGraphCoordinate_physical n e p hn he Λ g hg hs f
  rw [hq] at hgraph
  let hR := cutoffAuxiliaryResolvent_isResolvent n e p hn he Λ g hg hs
  have hF : (cutoffAuxiliaryResolvent n e p he Λ g hg hs f,f) ∈
      (GW.Operators.complexShift (compressedHamiltonian g (-p) n (some Λ))
        ((e-1+(n : ℝ) : ℝ) : ℂ)).graph := by
    exact (GW.Operators.complexShift _ _).mem_graph_iff.mpr
      ⟨hR.input f,rfl,hR.input_action f⟩
  have hrf : r=f := (GW.Operators.complexShift _ _).mem_graph_snd_inj hgraph hF rfl
  exact hr.symm.trans (congrArg (fun u : HighSectorSpace n => (u : GW.Fock.Carrier)) hrf)

end Froehlich
