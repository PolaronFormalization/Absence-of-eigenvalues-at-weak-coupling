import Froehlich.Nodes.BA02
import GW.Operators.CoerciveBounded

/-! FA02 (`lem:coercive`): the retained coercive inverse, on the complete
energy Hilbert space. No physical-domain ambient norm is substituted. -/

noncomputable section
open scoped InnerProductSpace

namespace Froehlich
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

def coerciveEnergyInverse (T : V →L[ℂ] V) (hT : T.adjoint = T)
    {α : ℝ} (hα : 0 < α) (hp : ∀ u, α * ‖u‖ ^ 2 ≤ (⟪u, T u⟫_ℂ).re) :
    V →L[ℂ] V := GW.Operators.coerciveInverse T hT hα hp

theorem coerciveEnergyInverse_left (T : V →L[ℂ] V) (hT : T.adjoint = T)
    {α : ℝ} (hα : 0 < α) (hp : ∀ u, α * ‖u‖ ^ 2 ≤ (⟪u, T u⟫_ℂ).re) :
    coerciveEnergyInverse T hT hα hp * T = 1 := by
  ext u
  exact GW.Operators.coerciveInverse_left T hT hα hp u

theorem coerciveEnergyInverse_right (T : V →L[ℂ] V) (hT : T.adjoint = T)
    {α : ℝ} (hα : 0 < α) (hp : ∀ u, α * ‖u‖ ^ 2 ≤ (⟪u, T u⟫_ℂ).re) :
    T * coerciveEnergyInverse T hT hα hp = 1 := by
  ext u
  exact GW.Operators.coerciveInverse_right T hT hα hp u

theorem coerciveEnergyInverse_norm_le (T : V →L[ℂ] V) (hT : T.adjoint = T)
    {α : ℝ} (hα : 0 < α) (hp : ∀ u, α * ‖u‖ ^ 2 ≤ (⟪u, T u⟫_ℂ).re) :
    ‖coerciveEnergyInverse T hT hα hp‖ ≤ α⁻¹ :=
  GW.Operators.coerciveInverse_norm_le T hT hα hp

/-- In Riesz coordinates this inverse solves the specified conjugate-dual
equation, including the orientation of its right-hand side. -/
theorem coerciveEnergyInverse_load (T : V →L[ℂ] V) (hT : T.adjoint = T)
    {α : ℝ} (hα : 0 < α) (hp : ∀ u, α * ‖u‖ ^ 2 ≤ (⟪u, T u⟫_ℂ).re)
    (F : ConjugateLoad V) (w : V) :
    ⟪w, T (coerciveEnergyInverse T hT hα hp (loadRiesz F))⟫_ℂ = F w := by
  change ⟪w, T (GW.Operators.coerciveInverse T hT hα hp (loadRiesz F))⟫_ℂ = F w
  rw [GW.Operators.coerciveInverse_right]
  exact (loadRiesz_spec F w).symm

/-- A different chosen inverse is identified by its actual inverse equation. -/
theorem coerciveEnergyInverse_unique (T S : V →L[ℂ] V) (hT : T.adjoint = T)
    {α : ℝ} (hα : 0 < α) (hp : ∀ u, α * ‖u‖ ^ 2 ≤ (⟪u, T u⟫_ℂ).re)
    (hST : S * T = 1) : S = coerciveEnergyInverse T hT hα hp := by
  calc
    S = S * (T * coerciveEnergyInverse T hT hα hp) := by
      rw [coerciveEnergyInverse_right, mul_one]
    _ = (S * T) * coerciveEnergyInverse T hT hα hp := (mul_assoc _ _ _).symm
    _ = coerciveEnergyInverse T hT hα hp := by rw [hST, one_mul]

/-- The interface is instantiated on a genuine complete complex Hilbert space. -/
example (z : ℂ) :
    coerciveEnergyInverse (ContinuousLinearMap.id ℂ ℂ) ContinuousLinearMap.adjoint_id
      (by norm_num : (0 : ℝ) < 1)
      (fun u => by simpa only [ContinuousLinearMap.id_apply, one_mul,
        RCLike.re_eq_complex_re]
        using (norm_sq_eq_re_inner (𝕜 := ℂ) u).le) z = z := by
  exact GW.Operators.coerciveInverse_right (ContinuousLinearMap.id ℂ ℂ)
    ContinuousLinearMap.adjoint_id (by norm_num : (0 : ℝ) < 1)
    (fun u => by simpa only [ContinuousLinearMap.id_apply, one_mul,
      RCLike.re_eq_complex_re]
      using (norm_sq_eq_re_inner (𝕜 := ℂ) u).le) z

end Froehlich
