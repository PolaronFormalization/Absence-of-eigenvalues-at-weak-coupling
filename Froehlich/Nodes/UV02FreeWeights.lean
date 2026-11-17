import Froehlich.Nodes.FD02FreeForm

/-! UV02's fixed-cutoff free resolvent scalar estimate. The large shift c
will be chosen after the finite cutoff; no limiting estimate uses it. -/
noncomputable section
namespace Froehlich

theorem freeShift_number_ratio_sq (x t c : ℝ) (hx : 0 ≤ x) (ht : 0 ≤ t) (hc : 1 ≤ c) :
    (t+1)/(x+t+c)^2 ≤ 1/c := by
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hd : 0 < x+t+c := by positivity
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) hcpos).mpr
  have hbase : c*(t+1) ≤ (t+c)^2 := by
    nlinarith [sq_nonneg t,mul_nonneg ht hcpos.le,mul_nonneg hcpos.le (sub_nonneg.mpr hc)]
  have hmono : (t+c)^2 ≤ (x+t+c)^2 :=
    (sq_le_sq₀ (by positivity) hd.le).mpr (by linarith)
  nlinarith

theorem freeShift_number_sqrt_ratio_sq (x c : ℝ) (n : ℕ) (hx : 0 ≤ x) (hc : 1 ≤ c) :
    (Real.sqrt ((n : ℝ)+1)/(x+(n : ℝ)+c))^2 ≤ 1/c := by
  rw [div_pow,Real.sq_sqrt (by positivity)]
  exact freeShift_number_ratio_sq x n c hx (Nat.cast_nonneg n) hc

theorem freeShift_reciprocal_bound (x c : ℝ) (n : ℕ) (hx : 0 ≤ x) (hc : 1 ≤ c) :
    0 < x+(n : ℝ)+c ∧ (x+(n : ℝ)+c)⁻¹ ≤ c⁻¹ := by
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hd : 0 < x+(n : ℝ)+c := by positivity
  exact ⟨hd,(inv_le_inv₀ hd hcpos).mpr (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)⟩

end Froehlich
