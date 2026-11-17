import Froehlich.Nodes.BA01
import Mathlib.Analysis.SpecificLimits.Normed

/-! BA02 (`lem:inversecalculus`). Geometric series live in the noncommutative
Banach ring of bounded endomorphisms. Inverse-order statements concern arbitrary
energy Riesz vectors, so also apply to form-dual sources. -/

noncomputable section
open scoped InnerProductSpace

namespace Froehlich

section Banach
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- Completeness is the existing operator-norm completeness instance. -/
example : CompleteSpace (E →L[𝕜] E) := inferInstance

def neumannInverse (K : E →L[𝕜] E) : E →L[𝕜] E := ∑' n : ℕ, K ^ n

theorem neumannInverse_left (K : E →L[𝕜] E) (hK : ‖K‖ < 1) :
    neumannInverse K * (1 - K) = 1 := geom_series_mul_neg K hK

theorem neumannInverse_right (K : E →L[𝕜] E) (hK : ‖K‖ < 1) :
    (1 - K) * neumannInverse K = 1 := mul_neg_geom_series K hK

theorem neumannInverse_norm_le (K : E →L[𝕜] E) {r : ℝ}
    (hKr : ‖K‖ ≤ r) (hr : r < 1) : ‖neumannInverse K‖ ≤ (1 - r)⁻¹ := by
  have hK := lt_of_le_of_lt hKr hr
  have hn := tsum_geometric_le_of_norm_lt_one K hK
  have hi : (1 - ‖K‖)⁻¹ ≤ (1 - r)⁻¹ :=
    (inv_le_inv₀ (sub_pos.mpr hK) (sub_pos.mpr hr)).mpr (by linarith)
  have h1 : ‖(1 : E →L[𝕜] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  change ‖neumannInverse K‖ ≤ _ at hn
  linarith

/-- This identity needs only the indicated sides of the two inverse identities. -/
theorem inverse_sub_identity (T S R Q : E →L[𝕜] E)
    (hRT : R * T = 1) (hSQ : S * Q = 1) :
    R - Q = R * (S - T) * Q := by
  rw [mul_sub, sub_mul, mul_assoc R S Q, hSQ, hRT, mul_one, one_mul]

end Banach

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Self-adjointness is retained on arbitrary two-sided bounded inverses. -/
theorem inverse_selfadjoint (T R : V →L[ℂ] V) (hT : T.adjoint = T)
    (hRT : R * T = 1) (hTR : T * R = 1) : R.adjoint = R := by
  have hleft : T * R.adjoint = 1 := by
    have h := congrArg ContinuousLinearMap.adjoint hRT
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp, hT,
      ContinuousLinearMap.adjoint_one] using h
  calc
    R.adjoint = (R * T) * R.adjoint := by rw [hRT, one_mul]
    _ = R * (T * R.adjoint) := mul_assoc _ _ _
    _ = R := by rw [hleft, mul_one]

theorem inverse_nonnegative (T R : V →L[ℂ] V) (hT : T.adjoint = T)
    (hTR : ∀ z, T (R z) = z)
    (hp : ∀ u, 0 ≤ (⟪u, T u⟫_ℂ).re) (z : V) :
    0 ≤ (⟪z, R z⟫_ℂ).re := by
  have hs : ⟪T (R z), R z⟫_ℂ = ⟪R z, T (R z)⟫_ℂ := by
    rw [← T.adjoint_inner_right, hT]
  have h := hp (R z)
  rw [← hs, hTR] at h
  exact h

def inverseVariationalFunctional (T : V →L[ℂ] V) (z u : V) : ℝ :=
  2 * (⟪z, u⟫_ℂ).re - (⟪u, T u⟫_ℂ).re

theorem inverse_variational_square (T R : V →L[ℂ] V) (hT : T.adjoint = T)
    (hTR : ∀ z, T (R z) = z) (z u : V) :
    inverseVariationalFunctional T z u = (⟪z, R z⟫_ℂ).re -
      (⟪u - R z, T (u - R z)⟫_ℂ).re := by
  have hs : ⟪R z, T u⟫_ℂ = ⟪z, u⟫_ℂ := by
    rw [← T.adjoint_inner_left, hT, hTR]
  have hc : (⟪u, z⟫_ℂ).re = (⟪z, u⟫_ℂ).re := by
    rw [← inner_conj_symm z u]
    rfl
  have hd : (⟪R z, z⟫_ℂ).re = (⟪z, R z⟫_ℂ).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  simp only [inverseVariationalFunctional, map_sub, inner_sub_left, inner_sub_right,
    Complex.sub_re, hTR, hs, hc, hd]
  ring

theorem inverse_variational_maximum (T R : V →L[ℂ] V) (hT : T.adjoint = T)
    (hTR : ∀ z, T (R z) = z) (hp : ∀ u, 0 ≤ (⟪u, T u⟫_ℂ).re) (z : V) :
    IsGreatest (Set.range (inverseVariationalFunctional T z)) (⟪z, R z⟫_ℂ).re := by
  constructor
  · refine ⟨R z, ?_⟩
    rw [inverse_variational_square T R hT hTR, sub_self]
    simp
  · rintro _ ⟨u, rfl⟩
    rw [inverse_variational_square T R hT hTR]
    exact sub_le_self _ (hp _)

theorem inverse_order (T₁ T₂ R₁ R₂ : V →L[ℂ] V)
    (hT₁ : T₁.adjoint = T₁) (hT₂ : T₂.adjoint = T₂)
    (h₁ : ∀ z, T₁ (R₁ z) = z) (h₂ : ∀ z, T₂ (R₂ z) = z)
    (hp₁ : ∀ u, 0 ≤ (⟪u, T₁ u⟫_ℂ).re)
    (hp₂ : ∀ u, 0 ≤ (⟪u, T₂ u⟫_ℂ).re)
    (horder : ∀ u, (⟪u, T₁ u⟫_ℂ).re ≤ (⟪u, T₂ u⟫_ℂ).re) (z : V) :
    (⟪z, R₂ z⟫_ℂ).re ≤ (⟪z, R₁ z⟫_ℂ).re := by
  have he := (inverse_variational_maximum T₂ R₂ hT₂ h₂ hp₂ z).1
  obtain ⟨u, hu⟩ := he
  rw [← hu]
  apply le_trans _ ((inverse_variational_maximum T₁ R₁ hT₁ h₁ hp₁ z).2
    (Set.mem_range_self u))
  exact sub_le_sub_left (horder u) _

end Froehlich
