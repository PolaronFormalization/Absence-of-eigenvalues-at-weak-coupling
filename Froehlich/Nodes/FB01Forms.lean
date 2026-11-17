import Froehlich.Nodes.FC03
import Froehlich.Nodes.GW05
import Froehlich.Nodes.EN02Number
import Froehlich.Nodes.BA03

/-! FB01's actual finite-cutoff forms, before the singular interaction exists.
No uncut form factor is treated as a physical vector. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem fieldRestriction_pairing (f : GW.OnePhonon) (w u : NumberFormSpace) :
    ⟪numberFormEmbedding w,fieldRestriction f u⟫_ℂ =
      ⟪fieldRestriction f w,numberFormEmbedding u⟫_ℂ := by
  rw [fieldRestriction_eq_ordinaryField, fieldRestriction_eq_ordinaryField]
  exact (GW.Fock.ordinaryField_symmetric f (numberFormRootInput w) (numberFormRootInput u)).symm

theorem fieldRestriction_bound (f : GW.OnePhonon) (u : NumberFormSpace) :
    ‖fieldRestriction f u‖ ≤ 2 * ‖f‖ * ‖u‖ := by
  have ha : ‖annihilationRestriction f u‖ ≤ ‖f‖ * ‖u‖ :=
    ((annihilationRestriction f).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (annihilationRestriction_opNorm f) (norm_nonneg u))
  have hc : ‖creationRestriction f u‖ ≤ ‖f‖ * ‖u‖ :=
    ((creationRestriction f).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (creationRestriction_opNorm f) (norm_nonneg u))
  change ‖annihilationRestriction f u + creationRestriction f u‖ ≤ _
  exact (norm_add_le _ _).trans ((add_le_add ha hc).trans_eq (by ring))

def energySmearedField (P : GW.Space) (f : GW.OnePhonon) : EnergySpace P →L[ℂ] GW.Fock.Carrier :=
  (fieldRestriction f).comp (energyNumberCoordinates P)

theorem energySmearedField_bound (P : GW.Space) (f : GW.OnePhonon) (u : EnergySpace P) :
    ‖energySmearedField P f u‖ ≤ 2 * ‖f‖ * ‖u‖ :=
  (fieldRestriction_bound f (energyNumberCoordinates P u)).trans
    (mul_le_mul_of_nonneg_left (energyNumberCoordinates_norm_le P u) (by positivity))

def energyInteractionForm (P : GW.Space) (f : GW.OnePhonon) :
    GW.Operators.AlgebraicForm (EnergySpace P) :=
  ((innerₛₗ ℂ).comp (energyEmbedding P).toLinearMap).compl₂ (energySmearedField P f).toLinearMap

theorem energyInteractionForm_apply (P : GW.Space) (f : GW.OnePhonon) (w u : EnergySpace P) :
    energyInteractionForm P f w u = ⟪energyEmbedding P w,energySmearedField P f u⟫_ℂ := rfl

theorem energyInteractionForm_hermitian (P : GW.Space) (f : GW.OnePhonon) (w u : EnergySpace P) :
    energyInteractionForm P f w u = star (energyInteractionForm P f u w) := by
  have h := fieldRestriction_pairing f (energyNumberCoordinates P w) (energyNumberCoordinates P u)
  rw [energyNumberCoordinates_intertwines, energyNumberCoordinates_intertwines] at h
  change ⟪energyEmbedding P w,energySmearedField P f u⟫_ℂ =
    ⟪energySmearedField P f w,energyEmbedding P u⟫_ℂ at h
  change ⟪energyEmbedding P w,energySmearedField P f u⟫_ℂ =
    star ⟪energyEmbedding P u,energySmearedField P f w⟫_ℂ
  exact h.trans (by
    simpa only [Complex.star_def] using
      (inner_conj_symm (energySmearedField P f w) (energyEmbedding P u)).symm)

theorem energyInteractionForm_mixed_bound (P : GW.Space) (f : GW.OnePhonon) (w u : EnergySpace P) :
    ‖energyInteractionForm P f w u‖ ≤ (2 * ‖f‖) * ‖w‖ * ‖u‖ := by
  rw [energyInteractionForm_apply]
  calc
    ‖⟪energyEmbedding P w,energySmearedField P f u⟫_ℂ‖ ≤
      ‖energyEmbedding P w‖ * ‖energySmearedField P f u‖ := norm_inner_le_norm _ _
    _ ≤ ‖w‖ * (2 * ‖f‖ * ‖u‖) := by
      have hj : ‖energyEmbedding P w‖ ≤ ‖w‖ :=
        ((energyEmbedding P).le_opNorm w).trans (by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (energyEmbedding_opNorm P) (norm_nonneg w))
      exact mul_le_mul hj (energySmearedField_bound P f u) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

def boundedEnergyInteraction (P : GW.Space) (f : GW.OnePhonon) :
    GW.Analysis.BoundedForm (EnergySpace P) :=
  GW.Operators.boundedAlgebraicForm (energyInteractionForm P f)
    (by positivity : 0 ≤ 2 * ‖f‖) (energyInteractionForm_mixed_bound P f)

theorem boundedEnergyInteraction_apply (P : GW.Space) (f : GW.OnePhonon) (w u : EnergySpace P) :
    boundedEnergyInteraction P f w u = energyInteractionForm P f w u := rfl

def cutoffInteractionForm (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space) :
    GW.Analysis.BoundedForm (EnergySpace P) :=
  boundedEnergyInteraction P (cutoffFormFactorL2 g Λ hΛ)

theorem cutoffInteractionForm_apply (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space) (w u : EnergySpace P) :
    cutoffInteractionForm g Λ hΛ P w u =
      ⟪energyEmbedding P w, GW.Fock.ordinaryField (cutoffFormFactorL2 g Λ hΛ)
        (numberFormRootInput (energyNumberCoordinates P u))⟫_ℂ := by
  change energyInteractionForm P (cutoffFormFactorL2 g Λ hΛ) w u = _
  rw [energyInteractionForm_apply]
  exact congrArg (fun z => ⟪energyEmbedding P w,z⟫_ℂ)
    (fieldRestriction_eq_ordinaryField _ _)

theorem cutoffInteractionForm_hermitian (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space) (w u : EnergySpace P) :
    cutoffInteractionForm g Λ hΛ P w u = star (cutoffInteractionForm g Λ hΛ P u w) :=
  energyInteractionForm_hermitian P (cutoffFormFactorL2 g Λ hΛ) w u

end Froehlich
