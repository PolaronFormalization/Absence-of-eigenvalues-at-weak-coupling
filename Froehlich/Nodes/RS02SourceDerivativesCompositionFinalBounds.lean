import Froehlich.Nodes.RS02SourceDerivativesCompositionBounds
import Froehlich.Nodes.CA02OperatorMultiIndex

set_option autoImplicit false

/-! Uniform canonical derivatives of the actual full-Fock source solution. -/
noncomputable section
namespace Froehlich
open scoped BoundedEndReal
local instance rs02SourceFinalBoundsHighGroup : NormedAddCommGroup (HighSectorSpace 1) :=
  Submodule.normedAddCommGroup (HighSectorSpace 1)
local instance rs02SourceFinalBoundsHighReal : NormedSpace ℝ (HighSectorSpace 1) :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance rs02SourceFinalBoundsHighModule : Module ℝ (HighSectorSpace 1) :=
  rs02SourceFinalBoundsHighReal.toModule
local instance rs02SourceFinalBoundsFockReal : NormedSpace ℝ GW.Fock.Carrier :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance rs02SourceFinalBoundsFockModule : Module ℝ GW.Fock.Carrier :=
  rs02SourceFinalBoundsFockReal.toModule
local instance rs02SourceFinalBoundsHighBounded : IsBoundedSMul ℝ (HighSectorSpace 1) :=
  NormedSpace.toIsBoundedSMul
local instance rs02SourceFinalBoundsHighContinuous : ContinuousSMul ℝ (HighSectorSpace 1) :=
  IsBoundedSMul.continuousSMul
local instance rs02SourceFinalBoundsFockBounded : IsBoundedSMul ℝ GW.Fock.Carrier :=
  NormedSpace.toIsBoundedSMul
local instance rs02SourceFinalBoundsFockContinuous : ContinuousSMul ℝ GW.Fock.Carrier :=
  IsBoundedSMul.continuousSMul
local instance rs02SourceFinalBoundsEndGroup : NormedAddCommGroup (HighSectorSpace 1 →L[ℂ] HighSectorSpace 1) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance rs02SourceFinalBoundsEndReal : NormedSpace ℝ (HighSectorSpace 1 →L[ℂ] HighSectorSpace 1) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace 1)).toNormedSpace
local instance rs02SourceFinalBoundsEndBounded : IsBoundedSMul ℝ (HighSectorSpace 1 →L[ℂ] HighSectorSpace 1) :=
  NormedSpace.toIsBoundedSMul
local instance rs02SourceFinalBoundsEndContinuous : ContinuousSMul ℝ (HighSectorSpace 1 →L[ℂ] HighSectorSpace 1) :=
  IsBoundedSMul.continuousSMul

local instance rs02SourceFinalBoundsRealEndGroup : NormedAddCommGroup (HighSectorSpace 1 →L[ℝ] HighSectorSpace 1) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance rs02SourceFinalBoundsHighSelfScalarComm : SMulCommClass ℝ ℝ (HighSectorSpace 1) where
  smul_comm r s x := by
    apply Subtype.ext
    change (r : ℂ) • ((s : ℂ) • (x : GW.Fock.Carrier)) =
      (s : ℂ) • ((r : ℂ) • (x : GW.Fock.Carrier))
    rw [smul_smul, smul_smul, mul_comm]
local instance rs02SourceFinalBoundsRealEndSpace : NormedSpace ℝ (HighSectorSpace 1 →L[ℝ] HighSectorSpace 1) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := HighSectorSpace 1) (F := HighSectorSpace 1) (σ₁₂ := RingHom.id ℝ)
local instance rs02SourceFinalBoundsRealEndBounded : IsBoundedSMul ℝ (HighSectorSpace 1 →L[ℝ] HighSectorSpace 1) :=
  NormedSpace.toIsBoundedSMul
local instance rs02SourceFinalBoundsRealEndContinuous : ContinuousSMul ℝ (HighSectorSpace 1 →L[ℝ] HighSectorSpace 1) :=
  IsBoundedSMul.continuousSMul


private theorem sourceFinal_norm_sum {I A : Type*} [NormedAddCommGroup A]
    (s : Finset I) (c : I → ℕ) (f : I → A) (v : I → ℝ) (hv : ∀ i ∈ s, ‖f i‖ ≤ v i) :
    ‖∑ i ∈ s, c i • f i‖ ≤ ∑ i ∈ s, (c i : ℝ)*v i := by
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  exact norm_nsmul_le.trans (mul_le_mul_of_nonneg_left (hv i hi) (Nat.cast_nonneg _))

theorem auxiliaryGroundSourceVector_derivatives_uniform :
    ∀ alpha : Fin 3 → ℕ, (∑ i, alpha i) ≤ 3 → ∃ C : ℝ, 0 < C ∧
      ∀ (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
        (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (q : Fin 3 → ℝ),
        ‖coordinateMultiPartial alpha
          (fun t => auxiliaryGroundSourceVector e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs) q‖ ≤ C*|g| := by
  classical
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
    (scalarDerivativeCoefficientBound (∑ i, beta i)*CH (fun i => alpha i-beta i))
  have hS : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro beta _
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
      (scalarDerivativeCoefficientBound_nonnegative _) (hCH _).le)
  refine ⟨S+1,by positivity,?_⟩
  intro g e he hg hs q
  let G := fun t : Fin 3 → ℝ => auxiliaryPhysicalFreeInverse 1 e
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he.2
  let H := fun t : Fin 3 → ℝ => auxiliaryNormalizedInverse g 1 e
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he.2 hg hs
      (auxiliaryNormalizedSource g e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he.2)
  let V : (HighSectorSpace 1 →L[ℂ] HighSectorSpace 1) →L[ℝ]
      (HighSectorSpace 1 →L[ℝ] HighSectorSpace 1) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ (HighSectorSpace 1) (HighSectorSpace 1) ℝ ℝ).toContinuousLinearMap
  let U : HighSectorSpace 1 →L[ℝ] GW.Fock.Carrier := (HighSectorSpace 1).subtypeL.restrictScalars ℝ
  let B : (HighSectorSpace 1 →L[ℂ] HighSectorSpace 1) →L[ℝ]
      (HighSectorSpace 1 →L[ℝ] GW.Fock.Carrier) :=
    ((ContinuousLinearMap.compL ℝ (HighSectorSpace 1) (HighSectorSpace 1) GW.Fock.Carrier) U).comp V
  have hG : ContDiff ℝ 3 G := by
    simpa only [G,Function.comp_def] using!
      (auxiliaryPhysicalFreeInverse_contDiff 1 e he.2).comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff
  have hH : ContDiff ℝ 3 H := by
    simpa only [H,Function.comp_def] using!
      (auxiliaryNormalizedInverse_source_contDiff g e he hg hs).comp
        (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff
  have hp := coordinateMultiPartial_realBilinear alpha B G H Set.univ isOpen_univ
    (hG.of_le (by exact_mod_cast ha)).contDiffOn (hH.of_le (by exact_mod_cast ha)).contDiffOn q (Set.mem_univ q)
  have hf : (fun t => auxiliaryGroundSourceVector e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs) =
      (fun t => B (G t) (H t)) := by
    funext t
    exact auxiliaryGroundSourceVector_formula g e _ he hg hs
  have hNorm : ‖coordinateMultiPartial alpha
      (fun t => auxiliaryGroundSourceVector e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs) q‖ =
      ‖∑ beta ∈ multiIndexBox alpha, multiIndexBinomial alpha beta •
        B (coordinateMultiPartial beta G q) (coordinateMultiPartial (fun i => alpha i-beta i) H q)‖ := by
    rw [hf]
    exact congrArg (fun u : GW.Fock.Carrier => ‖u‖) hp
  have hsum : ‖∑ beta ∈ multiIndexBox alpha, multiIndexBinomial alpha beta •
      B (coordinateMultiPartial beta G q) (coordinateMultiPartial (fun i => alpha i-beta i) H q)‖ ≤
      ∑ beta ∈ multiIndexBox alpha, (multiIndexBinomial alpha beta : ℝ)*
        (scalarDerivativeCoefficientBound (∑ i, beta i)*(CH (fun i => alpha i-beta i)*|g|)) := by
    apply sourceFinal_norm_sum
    intro beta hb
    have hd : (∑ i, (alpha i-beta i)) ≤ 3 :=
      (Finset.sum_le_sum (fun i _ => Nat.sub_le (alpha i) (beta i))).trans ha
    have hGb : ‖coordinateMultiPartial beta G q‖ ≤ scalarDerivativeCoefficientBound (∑ i, beta i) :=
      auxiliaryPhysicalFreeInverse_multiPartial_norm_le beta 1 e he.2 q
    have hHb : ‖coordinateMultiPartial (fun i => alpha i-beta i) H q‖ ≤ CH (fun i => alpha i-beta i)*|g| :=
      hHB _ g e he hg hs q hd
    have hA : ‖B (coordinateMultiPartial beta G q) (coordinateMultiPartial (fun i => alpha i-beta i) H q)‖ ≤
        ‖coordinateMultiPartial beta G q‖*‖coordinateMultiPartial (fun i => alpha i-beta i) H q‖ := by
      change ‖(coordinateMultiPartial beta G q (coordinateMultiPartial (fun i => alpha i-beta i) H q) : GW.Fock.Carrier)‖ ≤ _
      exact (coordinateMultiPartial beta G q).le_opNorm _
    exact hA.trans (mul_le_mul hGb hHb (norm_nonneg _) (scalarDerivativeCoefficientBound_nonnegative _))
  calc
    _ = _ := hNorm
    _ ≤ _ := hsum
    _ = S*|g| := by simp only [S,Finset.sum_mul,mul_assoc]
    _ ≤ (S+1)*|g| := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (abs_nonneg g)

end Froehlich
