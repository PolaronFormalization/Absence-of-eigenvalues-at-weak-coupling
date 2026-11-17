import GW.Operators.Polarization

/-! BA01 (`lem:rieszcoordinates`): the first argument of every load and form
is conjugate-linear. No change of Hilbert norm is implicit in these maps. -/

noncomputable section
open scoped InnerProductSpace

namespace Froehlich

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Actual continuous conjugate-linear loads. -/
abbrev ConjugateLoad (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] :=
  V →L⋆[ℂ] ℂ

/-- Conjugating a load gives an ordinary linear functional, to which the
ordinary (conjugate-linear) Riesz equivalence applies. -/
def linearizedLoad (F : ConjugateLoad V) : V →L[ℂ] ℂ :=
  ({ toFun := fun w => star (F w)
     map_add' := by intros; simp
     map_smul' := by intros; simp } : V →ₗ[ℂ] ℂ).mkContinuous ‖F‖
    (fun w => by simpa using F.le_opNorm w)

@[simp] theorem linearizedLoad_apply (F : ConjugateLoad V) (w : V) :
    linearizedLoad F w = star (F w) := rfl

def loadRiesz (F : ConjugateLoad V) : V :=
  (InnerProductSpace.toDual ℂ V).symm (linearizedLoad F)

theorem loadRiesz_spec (F : ConjugateLoad V) (w : V) :
    F w = ⟪w, loadRiesz F⟫_ℂ := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ)
    (x := w) (y := linearizedLoad F)
  calc
    F w = star (linearizedLoad F w) := by simp only [linearizedLoad_apply, star_star]
    _ = star ⟪loadRiesz F, w⟫_ℂ := congrArg star h.symm
    _ = ⟪w, loadRiesz F⟫_ℂ := by rw [Complex.star_def, inner_conj_symm]

theorem loadRiesz_unique (F : ConjugateLoad V) (z : V)
    (hz : ∀ w, F w = ⟪w, z⟫_ℂ) : z = loadRiesz F :=
  ext_inner_left ℂ (fun w => (hz w).symm.trans (loadRiesz_spec F w))

theorem loadRiesz_norm (F : ConjugateLoad V) : ‖loadRiesz F‖ = ‖F‖ := by
  have hn : ‖linearizedLoad F‖ = ‖F‖ := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro w
      simpa using F.le_opNorm w
    · apply F.opNorm_le_bound (norm_nonneg _)
      intro w
      simpa using (linearizedLoad F).le_opNorm w
  simpa [loadRiesz] using ((InnerProductSpace.toDual ℂ V).symm.norm_map
    (linearizedLoad F)).trans hn

@[simp] theorem loadRiesz_add (F G : ConjugateLoad V) :
    loadRiesz (F + G) = loadRiesz F + loadRiesz G := by
  apply Eq.symm
  apply loadRiesz_unique
  intro w
  simp [loadRiesz_spec, inner_add_right]

@[simp] theorem loadRiesz_smul (c : ℂ) (F : ConjugateLoad V) :
    loadRiesz (c • F) = c • loadRiesz F := by
  apply Eq.symm
  apply loadRiesz_unique
  intro w
  simp [loadRiesz_spec, inner_smul_right]

/-- The complex-linear isometric Riesz map for conjugate-dual loads. -/
def loadRieszLinearIsometry : ConjugateLoad V →ₗᵢ[ℂ] V where
  toFun := loadRiesz
  map_add' := loadRiesz_add
  map_smul' := loadRiesz_smul
  norm_map' := loadRiesz_norm

/-- Riesz representative in the second slot; the existing mathlib map
represents the form in the first slot, so its adjoint is required. -/
def formRepresentative (a : GW.Analysis.BoundedForm V) : V →L[ℂ] V :=
  (InnerProductSpace.continuousLinearMapOfBilin a).adjoint

theorem formRepresentative_spec (a : GW.Analysis.BoundedForm V) (w u : V) :
    a w u = ⟪w, formRepresentative a u⟫_ℂ := by
  rw [formRepresentative, ContinuousLinearMap.adjoint_inner_right]
  exact (InnerProductSpace.continuousLinearMapOfBilin_apply a w u).symm

theorem formRepresentative_unique (a : GW.Analysis.BoundedForm V) (T : V →L[ℂ] V)
    (hT : ∀ w u, a w u = ⟪w, T u⟫_ℂ) : T = formRepresentative a := by
  ext u
  exact ext_inner_left ℂ (fun w => (hT w u).symm.trans (formRepresentative_spec a w u))

theorem formRepresentative_norm_le (a : GW.Analysis.BoundedForm V) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ w u, ‖a w u‖ ≤ C * ‖w‖ * ‖u‖) :
    ‖formRepresentative a‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro u
  have hp := ha (formRepresentative a u) u
  rw [formRepresentative_spec, inner_self_eq_norm_sq_to_K] at hp
  change ‖((‖formRepresentative a u‖ : ℂ) ^ 2)‖ ≤
    C * ‖formRepresentative a u‖ * ‖u‖ at hp
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_norm] at hp
  by_cases hz : formRepresentative a u = 0
  · simp only [hz, norm_zero]
    exact mul_nonneg hC (norm_nonneg u)
  · have hn := norm_pos_iff.mpr hz
    nlinarith

theorem formRepresentative_selfadjoint (a : GW.Analysis.BoundedForm V)
    (ha : ∀ w u, a w u = star (a u w)) :
    (formRepresentative a).adjoint = formRepresentative a := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro w u
  rw [← inner_conj_symm, ← formRepresentative_spec, ha u w]
  simpa [Complex.star_def] using formRepresentative_spec a w u

/-- Physical sources are represented by the actual adjoint of the embedding. -/
theorem physicalLoad_spec {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (j : V →L[ℂ] H) (f : H) (w : V) :
    ⟪j w, f⟫_ℂ = ⟪w, j.adjoint f⟫_ℂ :=
  (j.adjoint_inner_right w f).symm

/-- A concrete complex-valued orientation test, including multiplication by `I`. -/
example (z w : ℂ) :
    (innerSLFlip ℂ (Complex.I * z)) w = Complex.I * (innerSLFlip ℂ z) w := by
  simp [innerSLFlip_apply_apply, inner_smul_right, ← smul_eq_mul]

end Froehlich
