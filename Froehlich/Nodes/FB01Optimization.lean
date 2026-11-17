import Froehlich.Nodes.FA03
import Mathlib.Tactic.Ring

/-! The source's explicit splitting radius and scalar Young remainders.
These numerical lemmas do not assume or assert any field-form estimate. -/
noncomputable section
namespace Froehlich

def lySplittingRadius (C g theta : ℝ) : ℝ :=
  max 1 (2*C) * max 1 (g^2 / theta^2)

theorem lySplittingRadius_lower (C g theta : ℝ) : 1 ≤ lySplittingRadius C g theta := by
  have hc : 0 ≤ max 1 (2*C) := zero_le_one.trans (le_max_left _ _)
  simpa only [one_mul, lySplittingRadius] using
    (mul_le_mul (le_max_left 1 (2*C)) (le_max_left 1 (g^2/theta^2)) zero_le_one hc)

theorem lySplittingRadius_tail (C g theta : ℝ) (ht : 0 < theta) :
    C*g^2/(theta * lySplittingRadius C g theta) ≤ theta/2 := by
  have hl := lySplittingRadius_lower C g theta
  have hc : 0 ≤ max 1 (2*C) := zero_le_one.trans (le_max_left _ _)
  have hx : 0 ≤ g^2/theta^2 := div_nonneg (sq_nonneg g) (sq_nonneg theta)
  have hb : (2*C)*(g^2/theta^2) ≤ lySplittingRadius C g theta :=
    mul_le_mul (le_max_right 1 (2*C)) (le_max_right 1 (g^2/theta^2)) hx hc
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg theta)
  rw [mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_gt ht))] at hm
  apply (div_le_iff₀ (mul_pos ht (zero_lt_one.trans_le hl))).mpr
  nlinarith

theorem lySplittingRadius_upper (C g theta : ℝ) :
    lySplittingRadius C g theta ≤ max 1 (2*C) * (1+g^2/theta^2) := by
  have hx : 0 ≤ g^2/theta^2 := div_nonneg (sq_nonneg g) (sq_nonneg theta)
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (le_max_left 1 (2*C)))
  exact max_le (by linarith) (by linarith)

def lyScalarRemainderConstant (C : ℝ) : ℝ := C*(max 1 (2*C)+1)+1

theorem lyScalarRemainderConstant_pos (C : ℝ) (hC : 0 ≤ C) :
    0 < lyScalarRemainderConstant C := by
  have hc : 0 ≤ max 1 (2*C)+1 := by linarith [le_max_left 1 (2*C)]
  exact add_pos_of_nonneg_of_pos (mul_nonneg hC hc) zero_lt_one

theorem lyScalarRemainder_bound (C g theta : ℝ) (hC : 0 ≤ C) (ht : 0 < theta) :
    C*g^2*lySplittingRadius C g theta/theta +
        C*g^2/(theta*lySplittingRadius C g theta) ≤
      lyScalarRemainderConstant C * (g^2/theta + g^4/theta^3) := by
  let C0 : ℝ := max 1 (2*C)
  have ht0 : theta ≠ 0 := ne_of_gt ht
  have hC0 : 0 ≤ C0 := zero_le_one.trans (le_max_left _ _)
  have hcoef : 0 ≤ C*g^2/theta := div_nonneg (mul_nonneg hC (sq_nonneg g)) ht.le
  have hlow := mul_le_mul_of_nonneg_left (lySplittingRadius_upper C g theta) hcoef
  have hl : C*g^2*lySplittingRadius C g theta/theta ≤
      C*C0*(g^2/theta+g^4/theta^3) := by
    calc
      _ = (C*g^2/theta)*lySplittingRadius C g theta := by ring
      _ ≤ (C*g^2/theta)*(max 1 (2*C)*(1+g^2/theta^2)) := hlow
      _ = _ := by
        dsimp only [C0]
        field_simp [ht0]
        <;> ring
  have hradius := lySplittingRadius_lower C g theta
  have hh : C*g^2/(theta*lySplittingRadius C g theta) ≤ C*g^2/theta :=
    div_le_div_of_nonneg_left (mul_nonneg hC (sq_nonneg g)) ht
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hradius ht.le)
  have hA : 0 ≤ g^2/theta := div_nonneg (sq_nonneg g) ht.le
  have hg4 : 0 ≤ g^4 := by simpa only [← pow_mul] using pow_nonneg (sq_nonneg g) 2
  have hB : 0 ≤ g^4/theta^3 := div_nonneg hg4 (pow_nonneg ht.le 3)
  have hCB : 0 ≤ C*(g^4/theta^3) := mul_nonneg hC hB
  unfold lyScalarRemainderConstant
  change _ ≤ (C*(C0+1)+1)*(g^2/theta+g^4/theta^3)
  calc
    _ ≤ C*C0*(g^2/theta+g^4/theta^3) + C*g^2/theta := add_le_add hl hh
    _ = (C*(C0+1)+1)*(g^2/theta+g^4/theta^3) -
        (C*(g^4/theta^3)+g^2/theta+g^4/theta^3) := by ring
    _ ≤ _ := sub_le_self _ (add_nonneg (add_nonneg hCB hA) hB)

end Froehlich
