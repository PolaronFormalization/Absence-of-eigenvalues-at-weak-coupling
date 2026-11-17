import Froehlich.Nodes.RS02ResolventDerivatives
import Froehlich.Nodes.RS02InverseDerivativeBounds

set_option autoImplicit false

/-! Uniform middle-factor bounds from the exact finite source expansion. -/
noncomputable section
namespace Froehlich
open scoped BoundedEndReal
local instance rs02ResolventBoundsHighGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance rs02ResolventBoundsEndGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance rs02ResolventBoundsEndReal (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace

private theorem norm_sum_nsmul_bound {I A : Type*} [NormedAddCommGroup A]
    (s : Finset I) (c : I → ℕ) (f : I → A) (v : I → ℝ)
    (hv : ∀ i ∈ s, ‖f i‖ ≤ v i) :
    ‖∑ i ∈ s, c i • f i‖ ≤ ∑ i ∈ s, (c i : ℝ)*v i := by
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  have hN : ‖c i • f i‖ ≤ (c i : ℝ)*‖f i‖ := norm_nsmul_le
  exact hN.trans (mul_le_mul_of_nonneg_left (hv i hi) (Nat.cast_nonneg _))

theorem auxiliaryResolventMiddleJet_uniform :
    ∀ alpha : Fin 3 → ℕ, (∑ i, alpha i) ≤ 3 → ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2)
        (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
        (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2),
        ‖auxiliaryResolventMiddleJet alpha n e p he g hg hsmall‖ ≤ C := by
  classical
  have hEach (gamma : Fin 3 → ℕ) : ∃ C : ℝ, 0 < C ∧
      ∀ (g : ℝ) (n : ℕ) (e : ℝ) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
        (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2) (q : Fin 3 → ℝ),
        (∑ i, gamma i) ≤ 3 →
        ‖coordinateMultiPartial gamma
          (fun t => auxiliaryNormalizedInverse g n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he.2 hg hsmall) q‖ ≤ C := by
    by_cases hgamma : (∑ i, gamma i) ≤ 3
    · obtain ⟨C,hC,hbound⟩ := auxiliaryNormalizedInverse_derivatives_uniform gamma hgamma
      exact ⟨C,hC,fun g n e hn he hg hs q _ => hbound g n e hn he hg hs q⟩
    · exact ⟨1,one_pos,fun _ _ _ _ _ _ _ _ h => False.elim (hgamma h)⟩
  choose C hC hBound using hEach
  intro alpha ha
  let V := fun beta gamma : Fin 3 → ℕ =>
    scalarDerivativeCoefficientBound (∑ i, beta i)*C gamma*
      scalarDerivativeCoefficientBound (∑ i, (alpha i-beta i-gamma i))
  let S : ℝ := ∑ beta ∈ multiIndexBox alpha, (multiIndexBinomial alpha beta : ℝ)*
    ∑ gamma ∈ multiIndexBox (fun i => alpha i-beta i),
      (multiIndexBinomial (fun i => alpha i-beta i) gamma : ℝ)*V beta gamma
  have hS : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro beta _
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro gamma _
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
      (mul_nonneg (scalarDerivativeCoefficientBound_nonnegative _) (hC gamma).le)
      (scalarDerivativeCoefficientBound_nonnegative _))
  refine ⟨S+1,by positivity,?_⟩
  intro n e p hn he g hg hs
  have hNorm : ‖auxiliaryResolventMiddleJet alpha n e p he g hg hs‖ ≤ S := by
    dsimp only [auxiliaryResolventMiddleJet,S]
    apply norm_sum_nsmul_bound
    intro beta hbeta
    apply norm_sum_nsmul_bound
    intro gamma hgamma
    have hga : gamma ∈ multiIndexBox alpha := (mem_multiIndexBox alpha gamma).mpr (fun i =>
      ((mem_multiIndexBox _ gamma).mp hgamma i).trans (Nat.sub_le (alpha i) (beta i)))
    have hdeg : (∑ i, gamma i) ≤ 3 := (rs02MultiIndex_order_le alpha gamma hga).trans ha
    let A := coordinateMultiPartial gamma
      (fun t => auxiliaryNormalizedInverse g n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he.2 hg hs)
      ((EuclideanSpace.equiv (Fin 3) ℝ) p)
    have hA : ‖A‖ ≤ C gamma := hBound gamma g n e hn he hg hs _ hdeg
    have hM := auxiliaryResolventMiddleTerm_norm_le (canonicalMultiIndexCoordinates beta)
      (canonicalMultiIndexCoordinates (fun i => alpha i-beta i-gamma i)) n e p he.2 A
    have hProd := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hA (scalarDerivativeCoefficientBound_nonnegative (∑ i, beta i)))
      (scalarDerivativeCoefficientBound_nonnegative (∑ i, (alpha i-beta i-gamma i)))
    refine hM.trans ?_
    simpa only [canonicalMultiIndexCoordinates_length,V] using! hProd
  exact hNorm.trans (le_add_of_nonneg_right zero_le_one)

end Froehlich
