import Froehlich.Nodes.RS02InverseDerivativeBoundsTools

set_option autoImplicit false

/-! Finite scalar majorization of the exact multi-index inverse recurrence.
This helper chooses constants before the parameter, without estimating or
altering the binomial coefficients in the source formula. -/
noncomputable section
namespace Froehlich

theorem rs02UniformInverseRecurrence_bound {d : ℕ} {P : Type*}
    (r : ℕ) (F : (Fin d → ℕ) → P → ℝ) (K : (Fin d → ℕ) → ℝ)
    (hK : ∀ beta, 0 ≤ K beta)
    (hzero : ∀ p, F 0 p ≤ 2)
    (hrec : ∀ alpha, (∑ i, alpha i) ≤ r → alpha ≠ 0 → ∀ p,
      F alpha p ≤ 2*∑ beta ∈ (multiIndexBox alpha).erase 0,
        (multiIndexBinomial alpha beta : ℝ)*
          (K beta*F (fun i => alpha i-beta i) p)) :
    ∀ alpha, (∑ i, alpha i) ≤ r → ∃ C : ℝ, 0 < C ∧ ∀ p, F alpha p ≤ C := by
  classical
  have H : ∀ m : ℕ, ∀ alpha : Fin d → ℕ, (∑ i, alpha i) = m →
      (∑ i, alpha i) ≤ r → ∃ C : ℝ, 0 < C ∧ ∀ p, F alpha p ≤ C := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro alpha hm hr
      by_cases ha : alpha = 0
      · subst alpha
        exact ⟨3,by norm_num,fun p => (hzero p).trans (by norm_num)⟩
      let S := (multiIndexBox alpha).erase 0
      have hmR : m ≤ r := by simpa only [hm] using hr
      have hEach (b : S) : ∃ C : ℝ, 0 < C ∧ ∀ p, F (fun i => alpha i-b.val i) p ≤ C := by
        have hlt : (∑ i, (alpha i-b.val i)) < m := by
          simpa only [hm] using rs02MultiIndex_difference_order_lt alpha b.val b.property
        exact ih _ hlt (fun i => alpha i-b.val i) rfl ((Nat.le_of_lt hlt).trans hmR)
      choose C hCpos hCbound using hEach
      let B : ℝ := ∑ b : S, (multiIndexBinomial alpha b.val : ℝ)*(K b.val*C b)
      have hB : 0 ≤ B := by
        apply Finset.sum_nonneg
        intro b _
        exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hK b.val) (hCpos b).le)
      refine ⟨1+2*B,by positivity,?_⟩
      intro p
      calc
        F alpha p ≤ 2*∑ beta ∈ S, (multiIndexBinomial alpha beta : ℝ)*
            (K beta*F (fun i => alpha i-beta i) p) := hrec alpha hr ha p
        _ = 2*∑ b : S, (multiIndexBinomial alpha b.val : ℝ)*
            (K b.val*F (fun i => alpha i-b.val i) p) := by
          exact congrArg (fun x : ℝ => 2*x)
            (Finset.sum_coe_sort (s := S) (f := fun beta : Fin d → ℕ =>
              (multiIndexBinomial alpha beta : ℝ)*(K beta*F (fun i => alpha i-beta i) p))).symm
        _ ≤ 2*B := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum
          intro b _
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hCbound b p) (hK b.val)) (Nat.cast_nonneg _)
        _ ≤ 1+2*B := by linarith
  intro alpha hr
  exact H (∑ i, alpha i) alpha rfl hr

end Froehlich
