import Froehlich.Nodes.FC07CutoffShift
import Froehlich.Nodes.FC07CoreSlices

/-! Uncompressed cutoff pullthrough on actual moving operator graphs. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

theorem cutoffCore_decomposition (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (S : ℕ) (hS : 1 ≤ S)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), (S : ℝ) < ‖k‖ → cutoffFormFactorL2 g Λ.val Λ.property k = 0)
    (u : boundedMomentumCore) :
    coreCutoffActionCore g P Λ u = coreFreeActionCore P u +
      coreAnnihilationAction (cutoffFormFactorL2 g Λ.val Λ.property) u +
        coreCreationAction S hS (cutoffFormFactorL2 g Λ.val Λ.property) hf u := by
  apply Subtype.ext
  change coreFreeAction P u +
      (annihilationRestriction (cutoffFormFactorL2 g Λ.val Λ.property) (coreNumberLift u) +
        creationRestriction (cutoffFormFactorL2 g Λ.val Λ.property) (coreNumberLift u)) =
    (coreFreeAction P u + annihilationRestriction (cutoffFormFactorL2 g Λ.val Λ.property) (coreNumberLift u)) +
      creationRestriction (cutoffFormFactorL2 g Λ.val Λ.property) (coreNumberLift u)
  abel

theorem cutoffField_decomposition_ae (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (S : ℕ) (hS : 1 ≤ S)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), (S : ℝ) < ‖k‖ → cutoffFormFactorL2 g Λ.val Λ.property k = 0)
    (u : boundedMomentumCore) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      annihilationField (coreNumberLift (coreCutoffActionCore g P Λ u)) k =
        (annihilationField (coreNumberLift (coreFreeActionCore P u)) k +
          annihilationField (coreNumberLift (coreAnnihilationAction (cutoffFormFactorL2 g Λ.val Λ.property) u)) k) +
          annihilationField (coreNumberLift (coreCreationAction S hS (cutoffFormFactorL2 g Λ.val Λ.property) hf u)) k := by
  have he : annihilationField (coreNumberLift (coreCutoffActionCore g P Λ u)) =
      (annihilationField (coreNumberLift (coreFreeActionCore P u)) +
        annihilationField (coreNumberLift (coreAnnihilationAction (cutoffFormFactorL2 g Λ.val Λ.property) u))) +
        annihilationField (coreNumberLift (coreCreationAction S hS (cutoffFormFactorL2 g Λ.val Λ.property) hf u)) := by
    rw [cutoffCore_decomposition g P Λ S hS hf u]
    simp only [map_add]
  filter_upwards [Lp.coeFn_add
    (annihilationField (coreNumberLift (coreFreeActionCore P u)) +
      annihilationField (coreNumberLift (coreAnnihilationAction (cutoffFormFactorL2 g Λ.val Λ.property) u)))
    (annihilationField (coreNumberLift (coreCreationAction S hS (cutoffFormFactorL2 g Λ.val Λ.property) hf u))),
    Lp.coeFn_add (annihilationField (coreNumberLift (coreFreeActionCore P u)))
      (annihilationField (coreNumberLift (coreAnnihilationAction (cutoffFormFactorL2 g Λ.val Λ.property) u)))]
      with k houter hinner
  have hk := congrArg (fun z : Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) => z k) he
  simp only [Pi.add_apply] at houter hinner
  exact hk.trans (houter.trans (congrArg
    (fun z : GW.Fock.Carrier => z + annihilationField
      (coreNumberLift (coreCreationAction S hS (cutoffFormFactorL2 g Λ.val Λ.property) hf u)) k) hinner))

def cutoffShiftField (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) (u : boundedMomentumCore) :
    Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) :=
  annihilationField (coreNumberLift (coreCutoffActionCore g P Λ u)) - annihilationField (coreNumberLift u) -
    GW.Fock.tensorEmbedding volume (cutoffFormFactorL2 g Λ.val Λ.property) (u : GW.Fock.Carrier)

theorem cutoffShiftField_ae (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) (u : boundedMomentumCore) :
    ∀ᵐ k ∂(volume : Measure GW.Space), cutoffShiftField g P Λ u k =
      annihilationField (coreNumberLift (coreCutoffActionCore g P Λ u)) k -
        annihilationField (coreNumberLift u) k - cutoffFormFactorL2 g Λ.val Λ.property k • (u : GW.Fock.Carrier) := by
  filter_upwards [Lp.coeFn_sub
    (annihilationField (coreNumberLift (coreCutoffActionCore g P Λ u)) - annihilationField (coreNumberLift u))
    (GW.Fock.tensorEmbedding volume (cutoffFormFactorL2 g Λ.val Λ.property) (u : GW.Fock.Carrier)),
    Lp.coeFn_sub (annihilationField (coreNumberLift (coreCutoffActionCore g P Λ u)))
      (annihilationField (coreNumberLift u)),
    GW.Fock.tensorEmbedding_ae volume (cutoffFormFactorL2 g Λ.val Λ.property) (u : GW.Fock.Carrier)]
      with k houter hinner htensor
  have he : cutoffShiftField g P Λ u k =
      (annihilationField (coreNumberLift (coreCutoffActionCore g P Λ u)) - annihilationField (coreNumberLift u)) k -
        GW.Fock.tensorEmbedding volume (cutoffFormFactorL2 g Λ.val Λ.property) (u : GW.Fock.Carrier) k := houter
  simp only [Pi.sub_apply] at hinner
  rw [hinner,htensor] at he
  exact he

theorem cutoffShiftField_graph (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) (u : boundedMomentumCore) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      (annihilationField (coreNumberLift u) k,cutoffShiftField g P Λ u k) ∈
        (cutoffHamiltonian g (P-k) Λ).graph := by
  obtain ⟨S,hS⟩ := exists_nat_ge (max 1 Λ.val)
  have hSpos : 1 ≤ S := by exact_mod_cast ((le_max_left 1 Λ.val).trans hS)
  let f := cutoffFormFactorL2 g Λ.val Λ.property
  have hf : ∀ᵐ k ∂(volume : Measure GW.Space), (S : ℝ) < ‖k‖ → f k = 0 := cutoffFormFactorL2_support_nat g Λ S hS
  filter_upwards [annihilationField_core_ae u,annihilationField_free_graph P u,
    core_field_annihilation_CCR f u,core_field_creation_CCR S hSpos f hf u,
    cutoffField_decomposition_ae g P Λ S hSpos hf u,cutoffShiftField_ae g P Λ u]
      with k hcore hfree hann hcre hdecomp houtput
  let q : boundedMomentumCore := ⟨annihilationField (coreNumberLift u) k,hcore⟩
  have hq : (q : GW.Fock.Carrier) = annihilationField (coreNumberLift u) k := rfl
  have ha := hann q hq
  have hc := hcre q hq
  have hfreeAction := (freeFiberOperator (P-k)).mem_graph_snd_inj hfree
    ((freeFiberOperator (P-k)).mem_graph (coreFreeInput (P-k) q)) hq.symm
  have hout : cutoffShiftField g P Λ u k = coreCutoffAction g (P-k) Λ q := by
    rw [houtput,hdecomp,ha,hc]
    change ((annihilationField (coreNumberLift (coreFreeActionCore P u)) k +
      annihilationRestriction f (coreNumberLift q)) +
        (creationRestriction f (coreNumberLift q) + f k • (u : GW.Fock.Carrier))) -
          annihilationField (coreNumberLift u) k - f k • (u : GW.Fock.Carrier) =
      coreFreeAction (P-k) q + (annihilationRestriction f (coreNumberLift q) + creationRestriction f (coreNumberLift q))
    calc
      _ = (annihilationField (coreNumberLift (coreFreeActionCore P u)) k - annihilationField (coreNumberLift u) k) +
          (annihilationRestriction f (coreNumberLift q) + creationRestriction f (coreNumberLift q)) := by abel
      _ = _ := congrArg (fun z : GW.Fock.Carrier => z +
        (annihilationRestriction f (coreNumberLift q) + creationRestriction f (coreNumberLift q))) hfreeAction
  have hg := cutoffHamiltonian_core_graph g (P-k) Λ q
  rwa [hq,← hout] at hg

theorem annihilationField_movingCutoff_domain (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (u : boundedMomentumCore) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      annihilationField (coreNumberLift u) k ∈ (cutoffHamiltonian g (P-k) Λ).domain := by
  filter_upwards [cutoffShiftField_graph g P Λ u] with k hk
  exact (cutoffHamiltonian g (P-k) Λ).mem_domain_of_mem_graph hk

end Froehlich
