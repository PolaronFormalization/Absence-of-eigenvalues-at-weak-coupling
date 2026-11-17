import Froehlich.Nodes.GW06
import Froehlich.Nodes.FB01CoreForms

/-! The actual finite-cutoff form operator on the bounded-coordinate core.
This makes no operator-domain assertion for the singular Hamiltonian. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

def coreFreeInput (P : GW.Space) (u : boundedMomentumCore) : (freeFiberOperator P).domain :=
  ⟨u,core_mem_freeFiberOperator_domain P u.property⟩

def coreFreeAction (P : GW.Space) (u : boundedMomentumCore) : GW.Fock.Carrier :=
  freeFiberOperator P (coreFreeInput P u)

theorem coreFreeAction_weak (P : GW.Space) (u : boundedMomentumCore) (w : EnergySpace P) :
    freeFiberForm P w (coreEnergyLift P u) = ⟪energyEmbedding P w,coreFreeAction P u⟫_ℂ := by
  obtain ⟨x,hx,hweak⟩ := (freeFiberOperator_graph_weak_iff P _ _).mp
    ((freeFiberOperator P).mem_graph (coreFreeInput P u))
  have he : x = coreEnergyLift P u :=
    energyEmbedding_injective P (hx.trans (coreEnergyLift_embedding P u).symm)
  rw [he] at hweak
  exact hweak w

theorem cutoffInteractionForm_core_second (g : ℝ) (P : GW.Space)
    (Λ : GW.Operators.PositiveCutoff) (u : boundedMomentumCore) (w : EnergySpace P) :
    cutoffInteractionForm g Λ.val Λ.property P w (coreEnergyLift P u) =
      ⟪energyEmbedding P w,fieldRestriction (cutoffFormFactorL2 g Λ.val Λ.property) (coreNumberLift u)⟫_ℂ := by
  rw [cutoffInteractionForm_apply,coreEnergyNumberCoordinates_eq,← fieldRestriction_eq_ordinaryField]

def coreCutoffAction (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (u : boundedMomentumCore) : GW.Fock.Carrier :=
  coreFreeAction P u + fieldRestriction (cutoffFormFactorL2 g Λ.val Λ.property) (coreNumberLift u)

theorem coreCutoffAction_weak (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (u : boundedMomentumCore) (w : EnergySpace P) :
    (fiberFormData g P (some Λ)).form w (coreEnergyLift P u) =
      ⟪energyEmbedding P w,coreCutoffAction g P Λ u⟫_ℂ := by
  rw [fiberFormData_cutoff_apply,coreFreeAction_weak,cutoffInteractionForm_core_second]
  exact (inner_add_right _ _ _).symm

/-- The full energy-test equation constructs actual operator-domain membership
and its action; no core equality is assumed as an interface hypothesis. -/
theorem cutoffHamiltonian_core_graph (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (u : boundedMomentumCore) :
    ((u : GW.Fock.Carrier),coreCutoffAction g P Λ u) ∈ (cutoffHamiltonian g P Λ).graph := by
  obtain ⟨hm,hact⟩ := GW.Operators.formOperator_domain_of_equation
    (fiberFormData g P (some Λ)) (coreEnergyLift P u) (coreCutoffAction g P Λ u)
    (coreCutoffAction_weak g P Λ u)
  apply (cutoffHamiltonian g P Λ).mem_graph_iff.mpr
  exact ⟨⟨energyEmbedding P (coreEnergyLift P u),hm⟩,coreEnergyLift_embedding P u,hact⟩

theorem cutoffHamiltonian_core_domain (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) :
    boundedMomentumCore ≤ (cutoffHamiltonian g P Λ).domain := by
  intro u hu
  exact (cutoffHamiltonian g P Λ).mem_domain_of_mem_graph (cutoffHamiltonian_core_graph g P Λ ⟨u,hu⟩)

def coreCutoffInput (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (u : boundedMomentumCore) : (cutoffHamiltonian g P Λ).domain :=
  ⟨u,cutoffHamiltonian_core_domain g P Λ u.property⟩

theorem cutoffHamiltonian_core_action (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (u : boundedMomentumCore) :
    cutoffHamiltonian g P Λ (coreCutoffInput g P Λ u) =
      freeFiberOperator P (coreFreeInput P u) +
        fieldRestriction (cutoffFormFactorL2 g Λ.val Λ.property) (coreNumberLift u) :=
  (cutoffHamiltonian g P Λ).mem_graph_snd_inj
    ((cutoffHamiltonian g P Λ).mem_graph (coreCutoffInput g P Λ u))
    (cutoffHamiltonian_core_graph g P Λ u) rfl

end Froehlich
