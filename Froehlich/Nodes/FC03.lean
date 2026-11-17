import Froehlich.Nodes.FC06

/-! FC03: the source's smeared operators are exactly the retained restrictions.
The varying-creation expression is a conjugate-dual load. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem smeared_operator_integral (f : GW.OnePhonon) (u : NumberFormSpace) :
    Integrable (fun k => (starRingEnd ℂ) (f k) • annihilationField u k) volume ∧
    annihilationRestriction f u = ∫ k, (starRingEnd ℂ) (f k) • annihilationField u k :=
  ⟨smeared_annihilation_integrable f u, smeared_annihilation_integral f u⟩

theorem smeared_operator_annihilation_bound (f : GW.OnePhonon) (u : NumberFormSpace) :
    ‖annihilationRestriction f u‖ ≤ ‖f‖ *
      ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput u)‖ :=
  annihilationRestriction_sharp_bound f u

theorem smeared_operator_creation_bound (f : GW.OnePhonon) (u : NumberFormSpace) :
    ‖creationRestriction f u‖ ≤ ‖f‖ *
      ‖GW.Fock.shiftedNumberPower GW.Fock.Sector (1/2)
        (GW.Fock.shiftedNumberInput GW.Fock.Sector (1/2) (by positivity) (numberFormRootInput u))‖ :=
  creationRestriction_sharp_bound f u

def varyingCreationLoad (G : Lp GW.Fock.Carrier 2 (volume : Measure GW.Space)) :
    ConjugateLoad NumberFormSpace := (innerSLFlip ℂ G).comp annihilationField

theorem varyingCreationLoad_integrable
    (G : Lp GW.Fock.Carrier 2 (volume : Measure GW.Space)) (w : NumberFormSpace) :
    Integrable (fun k => ⟪annihilationField w k,G k⟫_ℂ) volume :=
  L2.integrable_inner (𝕜 := ℂ) (annihilationField w) G

theorem varyingCreationLoad_integral
    (G : Lp GW.Fock.Carrier 2 (volume : Measure GW.Space)) (w : NumberFormSpace) :
    varyingCreationLoad G w = ∫ k, ⟪annihilationField w k,G k⟫_ℂ := by
  change ⟪annihilationField w,G⟫_ℂ = _
  exact L2.inner_def _ _

theorem varyingCreationLoad_bound
    (G : Lp GW.Fock.Carrier 2 (volume : Measure GW.Space)) (w : NumberFormSpace) :
    ‖varyingCreationLoad G w‖ ≤
      ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput w)‖ * ‖G‖ := by
  have hn : ‖annihilationField w‖ =
      ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput w)‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (annihilationField_norm_sq w)
  change ‖⟪annihilationField w,G⟫_ℂ‖ ≤ _
  exact (norm_inner_le_norm (annihilationField w) G).trans_eq (by rw [hn])

end Froehlich
