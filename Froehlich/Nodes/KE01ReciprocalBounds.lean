import Froehlich.Nodes.KE01QuadraticJets
import Froehlich.Nodes.KE01ScalarInverse
import Froehlich.Nodes.KE01CanonicalNormLocal
import Froehlich.Nodes.RS02InverseDerivativeBoundsFinite

set_option autoImplicit false
noncomputable section
namespace Froehlich

private theorem ke01_quadratic_contDiff (e : ℝ) (k : ℕ) :
    ContDiff ℝ k (kernelDenominatorCoordinates e) :=
  contDiff_const.sub ((contDiff_norm_sq ℝ).comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff)

private theorem ke01_quadratic_partial_bound (alpha : Fin 3 → ℕ) (e : ℝ)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (q : Fin 3 → ℝ)
    (hq : ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm q‖ ≤ 1/4) :
    ‖coordinateMultiPartial alpha (kernelDenominatorCoordinates e) q‖ ≤
      kernelQuadraticJetBound (∑ i,alpha i) := by
  exact (coordinateMultiPartial_norm_le_iterated_at alpha (kernelDenominatorCoordinates e) q
    (ke01_quadratic_contDiff e _).contDiffAt).trans
      (kernelDenominatorCoordinates_iterated_bound _ e he q hq)

theorem kernelInverseDenominator_derivatives_uniform :
    ∀ alpha : Fin 3 → ℕ, (∑ i,alpha i) ≤ 3 → ∃ C : ℝ, 0 < C ∧
      ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (q : Fin 3 → ℝ),
        ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm q‖ ≤ 1/4 →
        ‖coordinateMultiPartial alpha (fun y => (kernelDenominatorCoordinates e y)⁻¹) q‖ ≤ C := by
  let P := {p : ℝ × (Fin 3 → ℝ) // p.1 ∈ Set.Icc (-1/4 : ℝ) 0 ∧
    ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm p.2‖ ≤ 1/4}
  let F := fun (alpha : Fin 3 → ℕ) (p : P) =>
    ‖coordinateMultiPartial alpha (fun y => (kernelDenominatorCoordinates p.val.1 y)⁻¹) p.val.2‖
  let K := fun beta : Fin 3 → ℕ => kernelQuadraticJetBound (∑ i,beta i)
  have hzero (p : P) : F 0 p ≤ 2 := by
    change ‖coordinateMultiPartial 0 (fun y => (kernelDenominatorCoordinates p.val.1 y)⁻¹) p.val.2‖ ≤ 2
    rw [coordinateMultiPartial_zero,Real.norm_eq_abs]
    exact (thresholdKernel_denominator_inv_bound p.val.1 p.property.1 _ p.property.2).trans (by norm_num)
  have hrec (alpha : Fin 3 → ℕ) (_ha : (∑ i,alpha i) ≤ 3) (han : alpha ≠ 0) (p : P) :
      F alpha p ≤ 2*∑ beta ∈ (multiIndexBox alpha).erase 0,
        (multiIndexBinomial alpha beta : ℝ)*(K beta*F (fun i => alpha i-beta i) p) := by
    let S : Set (Fin 3 → ℝ) := {x | ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm x‖ < 1/3}
    have hS : IsOpen S := isOpen_lt
      (continuous_norm.comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous) continuous_const
    have hx : p.val.2 ∈ S := by dsimp [S]; linarith [p.property.2]
    have hn : ∀ x ∈ S,kernelDenominatorCoordinates p.val.1 x ≠ 0 := by
      intro x hx
      exact ne_of_gt (ke01_denominator_pos p.val.1 p.property.1 _ hx)
    have hr := ke01_scalarInverse_multiPartial (kernelDenominatorCoordinates p.val.1) alpha han S hS
      (ke01_quadratic_contDiff p.val.1 _).contDiffOn hn p.val.2 hx
    change ‖coordinateMultiPartial alpha (fun y => (kernelDenominatorCoordinates p.val.1 y)⁻¹) p.val.2‖ ≤ _
    rw [hr,norm_mul,norm_neg]
    have hI : ‖(kernelDenominatorCoordinates p.val.1 p.val.2)⁻¹‖ ≤ 2 := by
      exact (thresholdKernel_denominator_inv_bound p.val.1 p.property.1 _ p.property.2).trans (by norm_num)
    refine (mul_le_mul_of_nonneg_right hI (norm_nonneg _)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun beta _ => ?_))
    refine norm_nsmul_le.trans ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (ke01_quadratic_partial_bound beta p.val.1 p.property.1 p.val.2 p.property.2)
        (norm_nonneg _)) (Nat.cast_nonneg _)
  have hb := rs02UniformInverseRecurrence_bound 3 F K
    (fun beta => kernelQuadraticJetBound_nonnegative _) hzero hrec
  intro alpha ha
  obtain ⟨C,hC,hB⟩ := hb alpha ha
  exact ⟨C,hC,fun e he q hq => hB ⟨(e,q),he,hq⟩⟩

end Froehlich
