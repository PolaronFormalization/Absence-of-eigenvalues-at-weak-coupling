import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! FA03: the numerical convex combination applied to each form-domain vector. -/
namespace Froehlich

theorem graph_coercivity_interpolation {s mass kinetic ε a b : ℝ}
    (hε : 0 < ε) (ha : 0 < a) (hb : 0 ≤ b)
    (h₁ : ε * mass ≤ s) (h₂ : a * kinetic - b * mass ≤ s) :
    (ε / (2 * (b + ε))) * a * kinetic + ε / 2 * mass ≤ s := by
  have hd : 0 < 2 * (b + ε) := by linarith
  have ht : 0 ≤ ε / (2 * (b + ε)) := le_of_lt (div_pos hε hd)
  have ht1 : ε / (2 * (b + ε)) ≤ 1 := by
    apply (div_le_one hd).mpr
    linarith
  have hfirst := mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr ht1)
  have hsecond := mul_le_mul_of_nonneg_left h₂ ht
  have he : ε / (2 * (b + ε)) * (b + ε) = ε / 2 := by
    field_simp
  have heM := congrArg (fun t : ℝ => t * mass) he
  nlinarith
end Froehlich
