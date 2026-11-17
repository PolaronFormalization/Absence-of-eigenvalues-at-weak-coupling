import Froehlich.Nodes.FB01Forms
import Mathlib.Tactic.Abel

/-! Additivity in an actual L² form factor; no complex linearity is asserted
for annihilation. These are the finite-cutoff form identities used below. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

theorem annihilationRestriction_add_factor (f h : GW.OnePhonon) (u : NumberFormSpace) :
    annihilationRestriction (f+h) u = annihilationRestriction f u + annihilationRestriction h u := by
  calc
    _ = ∫ k, (starRingEnd ℂ) ((f+h) k) • annihilationField u k :=
      annihilationRestriction_integral (f+h) u
    _ = ∫ k, ((starRingEnd ℂ) (f k) • annihilationField u k +
        (starRingEnd ℂ) (h k) • annihilationField u k) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add f h] with k hk
      simp only [Pi.add_apply] at hk
      rw [hk,map_add,add_smul]
    _ = (∫ k, (starRingEnd ℂ) (f k) • annihilationField u k) +
        (∫ k, (starRingEnd ℂ) (h k) • annihilationField u k) :=
      integral_add (annihilationRestriction_integrable f u) (annihilationRestriction_integrable h u)
    _ = _ := congrArg₂ (fun x y : GW.Fock.Carrier => x+y)
      (annihilationRestriction_integral f u).symm (annihilationRestriction_integral h u).symm

theorem creationRestriction_add_factor (f h : GW.OnePhonon) (u : NumberFormSpace) :
    creationRestriction (f+h) u = creationRestriction f u + creationRestriction h u := by
  apply ext_inner_right ℂ
  intro v
  have hL : Continuous (fun v : GW.Fock.Carrier => ⟪creationRestriction (f+h) u,v⟫_ℂ) :=
    continuous_const.inner continuous_id
  have hR : Continuous (fun v : GW.Fock.Carrier =>
      ⟪creationRestriction f u + creationRestriction h u,v⟫_ℂ) :=
    continuous_const.inner continuous_id
  have he := hL.ext_on numberFormEmbedding_dense hR (by
    rintro v ⟨w,rfl⟩
    change ⟪creationRestriction (f+h) u,numberFormEmbedding w⟫_ℂ =
      ⟪creationRestriction f u + creationRestriction h u,numberFormEmbedding w⟫_ℂ
    rw [inner_add_left, smeared_adjoint_pairing (f+h) u w,
      smeared_adjoint_pairing f u w, smeared_adjoint_pairing h u w,
      annihilationRestriction_add_factor, inner_add_right])
  exact congrFun he v

theorem fieldRestriction_add_factor (f h : GW.OnePhonon) (u : NumberFormSpace) :
    fieldRestriction (f+h) u = fieldRestriction f u + fieldRestriction h u := by
  change annihilationRestriction (f+h) u + creationRestriction (f+h) u =
    (annihilationRestriction f u + creationRestriction f u) +
      (annihilationRestriction h u + creationRestriction h u)
  rw [annihilationRestriction_add_factor, creationRestriction_add_factor]
  abel

theorem boundedEnergyInteraction_add_factor (P : GW.Space) (f h : GW.OnePhonon) :
    boundedEnergyInteraction P (f+h) = boundedEnergyInteraction P f + boundedEnergyInteraction P h := by
  ext w u
  change ⟪energyEmbedding P w,fieldRestriction (f+h) (energyNumberCoordinates P u)⟫_ℂ =
    ⟪energyEmbedding P w,fieldRestriction f (energyNumberCoordinates P u)⟫_ℂ +
      ⟪energyEmbedding P w,fieldRestriction h (energyNumberCoordinates P u)⟫_ℂ
  rw [fieldRestriction_add_factor, inner_add_right]

theorem boundedEnergyInteraction_zero_factor (P : GW.Space) : boundedEnergyInteraction P 0 = 0 := by
  ext w u
  change energyInteractionForm P 0 w u = 0
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [norm_zero, mul_zero, zero_mul] using energyInteractionForm_mixed_bound P 0 w u

def energyInteractionAddHom (P : GW.Space) : GW.OnePhonon →+ GW.Analysis.BoundedForm (EnergySpace P) where
  toFun := boundedEnergyInteraction P
  map_zero' := boundedEnergyInteraction_zero_factor P
  map_add' := boundedEnergyInteraction_add_factor P

end Froehlich
