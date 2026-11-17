import Froehlich.Nodes.RS03Smooth
import Froehlich.Nodes.RS02SourceDerivativesCompositionBounds
import Froehlich.Nodes.RS02SourceDerivatives

set_option autoImplicit false

/-! Canonical derivatives of the actual bounded self-energy expression. -/
noncomputable section
namespace Froehlich
open scoped InnerProductSpace
local instance rs03DerivativesHighGroup : NormedAddCommGroup (HighSectorSpace 1) :=
  Submodule.normedAddCommGroup (HighSectorSpace 1)
local instance rs03DerivativesHighInner : InnerProductSpace ℝ (HighSectorSpace 1) :=
  InnerProductSpace.rclikeToReal ℂ (HighSectorSpace 1)
local instance rs03DerivativesHighReal : NormedSpace ℝ (HighSectorSpace 1) :=
  rs03DerivativesHighInner.toNormedSpace
local instance rs03DerivativesHighModule : Module ℝ (HighSectorSpace 1) := rs03DerivativesHighReal.toModule
local instance rs03DerivativesHighBounded : IsBoundedSMul ℝ (HighSectorSpace 1) := NormedSpace.toIsBoundedSMul
local instance rs03DerivativesHighContinuous : ContinuousSMul ℝ (HighSectorSpace 1) := IsBoundedSMul.continuousSMul

private theorem rs03Derivative_norm_sum {I A : Type*} [NormedAddCommGroup A]
    (s : Finset I) (c : I → ℕ) (f : I → A) (v : I → ℝ) (hv : ∀ i ∈ s, ‖f i‖ ≤ v i) :
    ‖∑ i ∈ s, c i • f i‖ ≤ ∑ i ∈ s, (c i : ℝ)*v i := by
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  exact norm_nsmul_le.trans (mul_le_mul_of_nonneg_left (hv i hi) (Nat.cast_nonneg _))


theorem auxiliarySelfEnergy_derivatives_uniform :
    ∀ alpha : Fin 3 → ℕ, (∑ i, alpha i) ≤ 2 → ∃ C : ℝ, 0 < C ∧
      ∀ (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
        (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (q : Fin 3 → ℝ),
        ‖coordinateMultiPartial alpha
          (fun t => auxiliarySelfEnergy e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs) q‖ ≤ C*g^2 := by
  classical
  obtain ⟨Cz,hCz,hZ⟩ := auxiliaryNormalizedSource_derivatives_uniform
  have hEach (delta : Fin 3 → ℕ) : ∃ C : ℝ, 0 < C ∧
      ∀ (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
        (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (q : Fin 3 → ℝ),
        (∑ i, delta i) ≤ 3 → ‖coordinateMultiPartial delta
          (fun t => auxiliaryNormalizedInverse g 1 e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he.2 hg hs
            (auxiliaryNormalizedSource g e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he.2)) q‖ ≤ C*|g| := by
    by_cases hd : (∑ i, delta i) ≤ 3
    · obtain ⟨C,hC,hB⟩ := auxiliaryNormalizedInverse_source_derivatives_uniform delta hd
      exact ⟨C,hC,fun g e he hg hs q _ => hB g e he hg hs q⟩
    · exact ⟨1,one_pos,fun _ _ _ _ _ _ h => False.elim (hd h)⟩
  choose CH hCH hHB using hEach
  intro alpha ha
  let S : ℝ := ∑ beta ∈ multiIndexBox alpha, (multiIndexBinomial alpha beta : ℝ)*
    (scalarDerivativeCoefficientBound (∑ i, beta i)*Cz*CH (fun i => alpha i-beta i))
  have hS : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro beta _
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
      (mul_nonneg (scalarDerivativeCoefficientBound_nonnegative _) hCz.le) (hCH _).le)
  refine ⟨S+1,by positivity,?_⟩
  intro g e he hg hs q
  let z := fun t : Fin 3 → ℝ => auxiliaryNormalizedSource g e
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he.2
  let H := fun t : Fin 3 → ℝ => auxiliaryNormalizedInverse g 1 e
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he.2 hg hs
      (auxiliaryNormalizedSource g e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he.2)
  let B : HighSectorSpace 1 →L[ℝ] HighSectorSpace 1 →L[ℝ] ℝ := -(innerSL ℝ)
  have hz : ContDiff ℝ 3 z := by
    simpa only [z,Function.comp_def] using!
      (auxiliaryNormalizedSource_contDiff g e he).comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff
  have hH : ContDiff ℝ 3 H := by
    simpa only [H,Function.comp_def] using!
      (auxiliaryNormalizedInverse_source_contDiff g e he hg hs).comp
        (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff
  have hp := coordinateMultiPartial_realBilinear alpha B z H Set.univ isOpen_univ
    (hz.of_le (by exact_mod_cast (ha.trans (by norm_num : (2:ℕ)≤3)))).contDiffOn
    (hH.of_le (by exact_mod_cast (ha.trans (by norm_num : (2:ℕ)≤3)))).contDiffOn q (Set.mem_univ q)
  have hf : (fun t => auxiliarySelfEnergy e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs) =
      (fun t => B (z t) (H t)) := by
    funext t
    exact auxiliarySelfEnergy_bounded_formula e _ he g hg hs
  have hNorm : ‖coordinateMultiPartial alpha
      (fun t => auxiliarySelfEnergy e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs) q‖ =
      ‖∑ beta ∈ multiIndexBox alpha, multiIndexBinomial alpha beta •
        B (coordinateMultiPartial beta z q) (coordinateMultiPartial (fun i => alpha i-beta i) H q)‖ := by
    rw [hf]
    exact congrArg (fun u : ℝ => ‖u‖) hp
  have hsum : ‖∑ beta ∈ multiIndexBox alpha, multiIndexBinomial alpha beta •
      B (coordinateMultiPartial beta z q) (coordinateMultiPartial (fun i => alpha i-beta i) H q)‖ ≤
      ∑ beta ∈ multiIndexBox alpha, (multiIndexBinomial alpha beta : ℝ)*
        ((scalarDerivativeCoefficientBound (∑ i, beta i)*Cz*CH (fun i => alpha i-beta i))*g^2) := by
    apply rs03Derivative_norm_sum
    intro beta hb
    have hbd : (∑ i, beta i) ≤ 3 := (rs02MultiIndex_order_le alpha beta hb).trans (ha.trans (by norm_num))
    have hd : (∑ i, (alpha i-beta i)) ≤ 3 :=
      (Finset.sum_le_sum (fun i _ => Nat.sub_le (alpha i) (beta i))).trans (ha.trans (by norm_num))
    have hzb : ‖coordinateMultiPartial beta z q‖ ≤ scalarDerivativeCoefficientBound (∑ i, beta i)*Cz*|g| := by
      simpa only [z] using! hZ beta hbd g e he q
    have hHb : ‖coordinateMultiPartial (fun i => alpha i-beta i) H q‖ ≤ CH (fun i => alpha i-beta i)*|g| :=
      hHB _ g e he hg hs q hd
    have hA : ‖B (coordinateMultiPartial beta z q) (coordinateMultiPartial (fun i => alpha i-beta i) H q)‖ ≤
        ‖coordinateMultiPartial beta z q‖*‖coordinateMultiPartial (fun i => alpha i-beta i) H q‖ := by
      simpa only [B,ContinuousLinearMap.neg_apply,norm_neg,innerSL_apply_apply] using!
        norm_inner_le_norm (coordinateMultiPartial beta z q) (coordinateMultiPartial (fun i => alpha i-beta i) H q)
    calc
      _ ≤ _ := hA.trans (mul_le_mul hzb hHb (norm_nonneg _) (mul_nonneg
        (mul_nonneg (scalarDerivativeCoefficientBound_nonnegative _) hCz.le) (abs_nonneg g)))
      _ = _ := by rw [←sq_abs]; ring
  calc
    _ = _ := hNorm
    _ ≤ _ := hsum
    _ = S*g^2 := by simp only [S,Finset.sum_mul,mul_assoc]
    _ ≤ (S+1)*g^2 := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (sq_nonneg g)

end Froehlich
