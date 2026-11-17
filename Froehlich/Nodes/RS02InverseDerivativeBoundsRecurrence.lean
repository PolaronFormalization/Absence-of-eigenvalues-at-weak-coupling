import Froehlich.Nodes.RS02InverseSmooth
import Froehlich.Nodes.RS02InteractionMultiIndex
import Froehlich.Nodes.RS02InverseDerivativeBoundsTools
import Froehlich.Nodes.CA01MultiIndexInverse

set_option autoImplicit false

/-! The exact source recurrence for the ACTUAL normalized inverse, and
its scalar norm majorization by the literal interaction derivative bounds. -/
noncomputable section
namespace Froehlich
open scoped BoundedEndReal
local instance rs02InverseBoundsRecurrenceHighGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance rs02InverseBoundsRecurrenceEndGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance rs02InverseBoundsRecurrenceEndReal (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace
local instance rs02InverseBoundsRecurrenceEndBounded (n : ℕ) : IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  NormedSpace.toIsBoundedSMul
local instance rs02InverseBoundsRecurrenceEndContinuous (n : ℕ) : ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  IsBoundedSMul.continuousSMul

theorem rs02NormalizedOperator_nonzero_multiPartial_norm_le (beta : Fin 3 → ℕ) (hb : beta ≠ 0)
    (g : ℝ) (n : ℕ) (e : ℝ) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (hg : |g| ≤ 1) (q : Fin 3 → ℝ) :
    ‖coordinateMultiPartial beta
      (fun p => auxiliaryNormalizedOperator g n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2) q‖ ≤
      interactionDerivativeBound beta*|g| := by
  let T := fun p : Fin 3 → ℝ => auxiliaryInteractionOperator g n e
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2
  let M := fun p : Fin 3 → ℝ => auxiliaryNormalizedOperator g n e
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2
  have hfun : coordinateMultiPartial beta M = coordinateMultiPartial beta T := by
    change coordinateMultiPartial beta (fun p => (1 : HighSectorSpace n →L[ℂ] HighSectorSpace n)+T p) = _
    exact rs02CoordinateMultiPartial_const_add beta hb 1 T
  have hnorm : ‖coordinateMultiPartial beta M q‖ = ‖coordinateMultiPartial beta T q‖ := by
    exact congrArg (fun A : HighSectorSpace n →L[ℂ] HighSectorSpace n => ‖A‖) (congrFun hfun q)
  calc
    _ = ‖coordinateMultiPartial beta T q‖ := by simpa only [M] using! hnorm
    _ ≤ _ := auxiliaryInteractionOperator_multiPartial_norm_le beta g n e hn he hg q

theorem rs02NormalizedInverse_multiPartial_recurrence (alpha : Fin 3 → ℕ)
    (ha : (∑ i, alpha i) ≤ 3) (ha0 : alpha ≠ 0) (g : ℝ) (n : ℕ) (e : ℝ)
    (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
    (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2) (q : Fin 3 → ℝ) :
    coordinateMultiPartial alpha
      (fun p => auxiliaryNormalizedInverse g n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2 hg hsmall) q =
      -auxiliaryNormalizedInverse g n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he.2 hg hsmall *
        ∑ beta ∈ (multiIndexBox alpha).erase 0, multiIndexBinomial alpha beta •
          (coordinateMultiPartial beta
            (fun p => auxiliaryNormalizedOperator g n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2) q *
           coordinateMultiPartial (fun i => alpha i-beta i)
            (fun p => auxiliaryNormalizedInverse g n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2 hg hsmall) q) := by
  let M := fun p : Fin 3 → ℝ => auxiliaryNormalizedOperator g n e
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2
  let Q := fun p : Fin 3 → ℝ => auxiliaryNormalizedInverse g n e
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2 hg hsmall
  have hM : ContDiff ℝ 3 M := by
    simpa only [M,Function.comp_def] using!
      (auxiliaryNormalizedOperator_contDiff g n e hn he).comp
        (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff
  have hMa : ContDiffOn ℝ (∑ i, alpha i : ℕ) M Set.univ :=
    (hM.of_le (by exact_mod_cast ha)).contDiffOn
  exact actualInverseFamily_coordinateMultiPartial M Q alpha ha0 Set.univ isOpen_univ hMa
    (fun p _ => ⟨auxiliaryNormalizedInverse_right g n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2 hg hsmall,
      auxiliaryNormalizedInverse_left g n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2 hg hsmall⟩) q (Set.mem_univ q)

theorem rs02NormalizedInverse_recurrence_norm_le (alpha : Fin 3 → ℕ)
    (ha : (∑ i, alpha i) ≤ 3) (ha0 : alpha ≠ 0) (g : ℝ) (n : ℕ) (e : ℝ)
    (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
    (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2) (q : Fin 3 → ℝ) :
    ‖coordinateMultiPartial alpha
      (fun p => auxiliaryNormalizedInverse g n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2 hg hsmall) q‖ ≤
      2*∑ beta ∈ (multiIndexBox alpha).erase 0, (multiIndexBinomial alpha beta : ℝ)*
        (interactionDerivativeBound beta*‖coordinateMultiPartial (fun i => alpha i-beta i)
          (fun p => auxiliaryNormalizedInverse g n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2 hg hsmall) q‖) := by
  classical
  let M := fun p : Fin 3 → ℝ => auxiliaryNormalizedOperator g n e
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2
  let Q := fun p : Fin 3 → ℝ => auxiliaryNormalizedInverse g n e
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2 hg hsmall
  let S := ∑ beta ∈ (multiIndexBox alpha).erase 0, multiIndexBinomial alpha beta •
    (coordinateMultiPartial beta M q*coordinateMultiPartial (fun i => alpha i-beta i) Q q)
  have hre := rs02NormalizedInverse_multiPartial_recurrence alpha ha ha0 g n e hn he hg hsmall q
  have hnorm : ‖coordinateMultiPartial alpha Q q‖ = ‖-(Q q)*S‖ := by
    simpa only [Q,M,S] using! congrArg (fun A : HighSectorSpace n →L[ℂ] HighSectorSpace n => ‖A‖) hre
  have hsum : ‖S‖ ≤ ∑ beta ∈ (multiIndexBox alpha).erase 0, (multiIndexBinomial alpha beta : ℝ)*
      (interactionDerivativeBound beta*‖coordinateMultiPartial (fun i => alpha i-beta i) Q q‖) := by
    calc
      _ ≤ ∑ beta ∈ (multiIndexBox alpha).erase 0, ‖multiIndexBinomial alpha beta •
          (coordinateMultiPartial beta M q*coordinateMultiPartial (fun i => alpha i-beta i) Q q)‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro beta hb
        have hMbeta : ‖coordinateMultiPartial beta M q‖ ≤ interactionDerivativeBound beta := by
          have h := rs02NormalizedOperator_nonzero_multiPartial_norm_le beta (Finset.mem_erase.mp hb).1
            g n e hn he hg q
          exact h.trans ((mul_le_mul_of_nonneg_left hg (interactionDerivativeBound_nonneg beta)).trans_eq (mul_one _))
        have hprod : ‖coordinateMultiPartial beta M q*coordinateMultiPartial (fun i => alpha i-beta i) Q q‖ ≤
            interactionDerivativeBound beta*‖coordinateMultiPartial (fun i => alpha i-beta i) Q q‖ :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_right hMbeta (coordinateMultiPartial (fun i => alpha i-beta i) Q q).opNorm_nonneg)
        have hN : ‖multiIndexBinomial alpha beta •
            (coordinateMultiPartial beta M q*coordinateMultiPartial (fun i => alpha i-beta i) Q q)‖ ≤
            (multiIndexBinomial alpha beta : ℝ)*
              ‖coordinateMultiPartial beta M q*coordinateMultiPartial (fun i => alpha i-beta i) Q q‖ := norm_nsmul_le
        exact hN.trans (mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _))
  calc
    _ = ‖-(Q q)*S‖ := by simpa only [Q] using! hnorm
    _ ≤ ‖-(Q q)‖*‖S‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖Q q‖*‖S‖ := by rw [ContinuousLinearMap.opNorm_neg]
    _ ≤ 2*‖S‖ := mul_le_mul_of_nonneg_right
      (auxiliaryNormalizedInverse_norm_le g n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he.2 hg hsmall) S.opNorm_nonneg
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)

end Froehlich
