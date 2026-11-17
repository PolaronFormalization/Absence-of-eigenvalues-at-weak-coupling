import Froehlich.Nodes.FC07FreeShift

/-! Only finite cutoffs preserve the bounded-coordinate operator core. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

theorem cutoffFormFactorL2_support_nat (g : ℝ) (Λ : GW.Operators.PositiveCutoff)
    (S : ℕ) (hS : max 1 Λ.val ≤ (S : ℝ)) :
    ∀ᵐ k ∂(volume : Measure GW.Space), (S : ℝ) < ‖k‖ → cutoffFormFactorL2 g Λ.val Λ.property k = 0 := by
  filter_upwards [cutoffFormFactorL2_ae g Λ.val Λ.property] with k hk
  intro hout
  have hΛS : Λ.val ≤ (S : ℝ) := (le_max_right 1 Λ.val).trans hS
  have hn : ¬‖k‖ ≤ Λ.val := not_le.mpr (hΛS.trans_lt hout)
  rw [hk]
  simp only [cutoffFormFactor,if_neg hn,Complex.ofReal_zero]

theorem fieldRestriction_preserves_core (f : GW.OnePhonon) (u : boundedMomentumCore)
    (S : ℕ) (hS : 1 ≤ S)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), (S : ℝ) < ‖k‖ → f k = 0) :
    fieldRestriction f (coreNumberLift u) ∈ boundedMomentumCore := by
  change annihilationRestriction f (coreNumberLift u) + creationRestriction f (coreNumberLift u) ∈ boundedMomentumCore
  exact boundedMomentumCore.add_mem (annihilationRestriction_preserves_core f u)
    (creationRestriction_preserves_core f u S hS hf)

theorem coreCutoffAction_preserves_core (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (u : boundedMomentumCore) : coreCutoffAction g P Λ u ∈ boundedMomentumCore := by
  obtain ⟨S,hS⟩ := exists_nat_ge (max 1 Λ.val)
  have hSpos : 1 ≤ S := by exact_mod_cast ((le_max_left 1 Λ.val).trans hS)
  exact boundedMomentumCore.add_mem (coreFreeActionCore P u).property
    (fieldRestriction_preserves_core (cutoffFormFactorL2 g Λ.val Λ.property) u S hSpos
      (cutoffFormFactorL2_support_nat g Λ S hS))

def coreCutoffActionCore (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (u : boundedMomentumCore) : boundedMomentumCore :=
  ⟨coreCutoffAction g P Λ u,coreCutoffAction_preserves_core g P Λ u⟩

theorem cutoffHamiltonian_core_action_core (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (u : boundedMomentumCore) :
    cutoffHamiltonian g P Λ (coreCutoffInput g P Λ u) = (coreCutoffActionCore g P Λ u : GW.Fock.Carrier) :=
  cutoffHamiltonian_core_action g P Λ u

end Froehlich
