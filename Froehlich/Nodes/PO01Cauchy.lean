import Froehlich.Nodes.PO01Square

/-! The source weighted Cauchy--Schwarz estimate is proved by positivity at
one explicitly chosen vector; no new Hilbert-space structure is installed. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem twoVector_inverse_cauchy (B R : H →L[ℂ] H) (hB : B.adjoint = B)
    (hBR : ∀ v, B (R v) = v) (beta : ℝ) (hb : 0 < beta)
    (hp : ∀ v, beta*‖v‖^2 ≤ (⟪v,B v⟫_ℂ).re) (t y : H) :
    ‖⟪t,y⟫_ℂ‖^2 ≤ (⟪t,R t⟫_ℂ).re*(⟪y,B y⟫_ℂ).re := by
  let N : ℝ := (⟪t,R t⟫_ℂ).re
  have hpos (v : H) : 0 ≤ (⟪v,B v⟫_ℂ).re :=
    (mul_nonneg hb.le (sq_nonneg ‖v‖)).trans (hp v)
  have hN : 0 ≤ N := inverse_nonnegative B R hB hBR hpos t
  have hNt : beta*‖R t‖^2 ≤ N := by
    have h := hp (R t)
    rw [hBR] at h
    exact h.trans_eq (inner_re_symm (𝕜 := ℂ) _ _)
  by_cases hz : N = 0
  · have hsq : ‖R t‖^2 ≤ 0 := nonpos_of_mul_nonpos_right (hNt.trans_eq hz) hb
    have hnorm : ‖R t‖ = 0 := by nlinarith [norm_nonneg (R t)]
    have hRt : R t = 0 := norm_eq_zero.mp hnorm
    have ht : t = 0 := by rw [← hBR t,hRt,map_zero]
    subst t
    simp
  · have hn : 0 < N := lt_of_le_of_ne hN (Ne.symm hz)
    let r : ℂ := ⟪t,y⟫_ℂ
    let gamma : ℂ := r / (N : ℂ)
    have hcross : ((starRingEnd ℂ) gamma*r).re = ‖r‖^2/N := by
      have hc : (starRingEnd ℂ) gamma*r = ((‖r‖^2/N : ℝ) : ℂ) := by
        dsimp [gamma]
        rw [map_div₀,Complex.conj_ofReal]
        calc
          ((starRingEnd ℂ) r / (N : ℂ))*r = ((starRingEnd ℂ) r*r)/(N : ℂ) := by ring
          _ = _ := by simp only [Complex.conj_mul',Complex.ofReal_div,Complex.ofReal_pow]
      exact congrArg Complex.re hc
    have hgamma : ‖gamma‖^2 = ‖r‖^2/N^2 := by
      dsimp [gamma]
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn]
      ring
    have hscaled : N*‖gamma‖^2 = ‖r‖^2/N := by
      rw [hgamma]
      field_simp [ne_of_gt hn] <;> ring
    have hc := twoVector_completion_square B R hB hBR t y (-gamma) 0
    have hq := hpos (y+(-gamma) • R t)
    have hc' : (⟪y,B y⟫_ℂ).re - 2*((starRingEnd ℂ) gamma*r).re =
        (⟪y+(-gamma) • R t,B (y+(-gamma) • R t)⟫_ℂ).re - N*‖gamma‖^2 := by
      simpa only [zero_mul,zero_add,norm_neg,map_neg,neg_mul,Complex.neg_re,
        zero_sub,neg_mul,sub_eq_add_neg,r,N,add_zero,mul_neg] using hc
    rw [hcross,hscaled] at hc'
    have hdiv : ‖r‖^2/N ≤ (⟪y,B y⟫_ℂ).re := by linarith
    have hfinal := (div_le_iff₀ hn).mp hdiv
    simpa only [r,N,mul_comm] using hfinal

end Froehlich
