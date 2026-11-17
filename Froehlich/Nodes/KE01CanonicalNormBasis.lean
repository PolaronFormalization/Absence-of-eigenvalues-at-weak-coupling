import Mathlib.Analysis.Normed.Module.Multilinear.Curry

set_option autoImplicit false
noncomputable section
namespace Froehlich
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem linearMap_norm_le_coordinates (d : ℕ) (L : (Fin d → ℝ) →L[ℝ] V)
    (K : ℝ) (hK : 0 ≤ K) (hL : ∀ i : Fin d, ‖L (Pi.single i 1)‖ ≤ K) :
    ‖L‖ ≤ (d : ℝ)*K := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hK)
  intro x
  have hx : L x = ∑ i : Fin d, x i • L (Pi.single i 1) := by
    have h := congrArg L (Finset.univ_sum_single x)
    rw [map_sum] at h
    have he (i : Fin d) : Pi.single i (x i) = x i • (Pi.single i (1 : ℝ) : Fin d → ℝ) := by
      funext j
      by_cases hj : j = i
      · subst j; simp
      · simp [Pi.single_apply,hj,Ne.symm hj]
    simpa only [he,map_smul] using h.symm
  calc
    ‖L x‖ = ‖∑ i : Fin d, x i • L (Pi.single i 1)‖ := congrArg norm hx
    _ ≤ ∑ i : Fin d, ‖x i • L (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, ‖x‖*K := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm x i) (hL i) (norm_nonneg _) (norm_nonneg _)
    _ = ((d : ℝ)*K)*‖x‖ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

/-- A dimension-only bound, for every order, from all ordered coordinate
entries of an actual continuous multilinear map on the native sup-norm Pi space. -/
theorem multilinearMap_norm_le_coordinates (d k : ℕ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin d → ℝ) V)
    (K : ℝ) (hK : 0 ≤ K)
    (hA : ∀ is : Fin k → Fin d, ‖A (fun j => Pi.single (is j) 1)‖ ≤ K) :
    ‖A‖ ≤ (d : ℝ)^k*K := by
  induction k generalizing K with
  | zero =>
    simpa only [ContinuousMultilinearMap.fin0_apply_norm,pow_zero,one_mul] using hA Fin.elim0
  | succ k ih =>
    have hrow (i : Fin d) : ‖A.curryLeft (Pi.single i 1)‖ ≤ (d : ℝ)^k*K := by
      apply ih _ K hK
      intro is
      rw [ContinuousMultilinearMap.curryLeft_apply]
      have hv : Fin.cons (Pi.single i (1 : ℝ) : Fin d → ℝ)
          (fun j : Fin k => (Pi.single (is j) 1 : Fin d → ℝ)) =
          (fun j : Fin (k+1) => (Pi.single ((Fin.cons i is : Fin (k+1) → Fin d) j) 1 : Fin d → ℝ)) := by
        funext j
        exact Fin.cases rfl (fun _ => rfl) j
      rw [hv]
      exact hA (Fin.cons i is)
    rw [←A.curryLeft_norm]
    have hb := linearMap_norm_le_coordinates d A.curryLeft ((d : ℝ)^k*K)
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hK) hrow
    exact hb.trans_eq (by rw [pow_succ]; ring)

end Froehlich
