import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! The scalar final step in the source two-vector positivity argument. -/
namespace Froehlich

theorem twoVector_scalar_positivity {A T q b a2 : ℝ}
    (hA : 0 < A) (hb : 0 ≤ b) (ha : 0 ≤ a2)
    (hcs : A*a2 ≤ T*b) (hcriterion : 0 ≤ A+T*q) :
    0 ≤ b+q*a2 := by
  by_cases hq : 0 ≤ q
  · exact add_nonneg hb (mul_nonneg hq ha)
  · have hnq : 0 ≤ -q := by linarith
    have hm := mul_le_mul_of_nonneg_left hcs hnq
    have hp := mul_nonneg hcriterion hb
    have hresult : 0 ≤ A*(b+q*a2) := by nlinarith
    exact nonneg_of_mul_nonneg_right hresult hA

end Froehlich
