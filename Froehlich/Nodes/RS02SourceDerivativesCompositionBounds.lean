import Froehlich.Nodes.RS02SourceDerivativesComposition
import Froehlich.Nodes.RS02SourceDerivatives
import Froehlich.Nodes.RS02InverseDerivativeBounds
import Froehlich.Nodes.CA01BlockProduct

set_option autoImplicit false

/-! Genuine canonical Qz derivatives have uniform linear coupling bounds.
Only finite scalar constants are selected; every vector and derivative is
that of the actual normalized source and inverse. -/
noncomputable section
namespace Froehlich
open scoped BoundedEndReal
local instance rs02SourceCompBoundsHighGroup : NormedAddCommGroup (HighSectorSpace 1) :=
  Submodule.normedAddCommGroup (HighSectorSpace 1)
local instance rs02SourceCompBoundsHighReal : NormedSpace ℝ (HighSectorSpace 1) :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance rs02SourceCompBoundsHighModule : Module ℝ (HighSectorSpace 1) :=
  rs02SourceCompBoundsHighReal.toModule
local instance rs02SourceCompBoundsHighBounded : IsBoundedSMul ℝ (HighSectorSpace 1) :=
  NormedSpace.toIsBoundedSMul
local instance rs02SourceCompBoundsHighContinuous : ContinuousSMul ℝ (HighSectorSpace 1) :=
  IsBoundedSMul.continuousSMul
local instance rs02SourceCompBoundsEndGroup : NormedAddCommGroup (HighSectorSpace 1 →L[ℂ] HighSectorSpace 1) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance rs02SourceCompBoundsEndReal : NormedSpace ℝ (HighSectorSpace 1 →L[ℂ] HighSectorSpace 1) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace 1)).toNormedSpace
local instance rs02SourceCompBoundsEndBounded : IsBoundedSMul ℝ (HighSectorSpace 1 →L[ℂ] HighSectorSpace 1) :=
  NormedSpace.toIsBoundedSMul
local instance rs02SourceCompBoundsEndContinuous : ContinuousSMul ℝ (HighSectorSpace 1 →L[ℂ] HighSectorSpace 1) :=
  IsBoundedSMul.continuousSMul

local instance rs02SourceCompBoundsRealEndGroup : NormedAddCommGroup (HighSectorSpace 1 →L[ℝ] HighSectorSpace 1) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance rs02SourceCompBoundsHighSelfScalarComm : SMulCommClass ℝ ℝ (HighSectorSpace 1) where
  smul_comm r s x := by
    apply Subtype.ext
    change (r : ℂ) • ((s : ℂ) • (x : GW.Fock.Carrier)) =
      (s : ℂ) • ((r : ℂ) • (x : GW.Fock.Carrier))
    rw [smul_smul, smul_smul, mul_comm]
local instance rs02SourceCompBoundsRealEndSpace : NormedSpace ℝ (HighSectorSpace 1 →L[ℝ] HighSectorSpace 1) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := HighSectorSpace 1) (F := HighSectorSpace 1) (σ₁₂ := RingHom.id ℝ)
local instance rs02SourceCompBoundsRealEndBounded : IsBoundedSMul ℝ (HighSectorSpace 1 →L[ℝ] HighSectorSpace 1) :=
  NormedSpace.toIsBoundedSMul
local instance rs02SourceCompBoundsRealEndContinuous : ContinuousSMul ℝ (HighSectorSpace 1 →L[ℝ] HighSectorSpace 1) :=
  IsBoundedSMul.continuousSMul

private theorem sourceCompNorm_sum_bound {I A : Type*} [NormedAddCommGroup A]
    (s : Finset I) (c : I → ℕ) (f : I → A) (v : I → ℝ) (hv : ∀ i ∈ s, ‖f i‖ ≤ v i) :
    ‖∑ i ∈ s, c i • f i‖ ≤ ∑ i ∈ s, (c i : ℝ)*v i := by
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  have hN : ‖c i • f i‖ ≤ (c i : ℝ)*‖f i‖ := norm_nsmul_le
  exact hN.trans (mul_le_mul_of_nonneg_left (hv i hi) (Nat.cast_nonneg _))

theorem auxiliaryNormalizedInverse_source_derivatives_uniform :
    ∀ alpha : Fin 3 → ℕ, (∑ i, alpha i) ≤ 3 → ∃ C : ℝ, 0 < C ∧
      ∀ (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
        (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (q : Fin 3 → ℝ),
        ‖coordinateMultiPartial alpha
          (fun t => auxiliaryNormalizedInverse g 1 e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he.2 hg hs
            (auxiliaryNormalizedSource g e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he.2)) q‖ ≤ C*|g| := by
  classical
  obtain ⟨Cz,hCz,hzbound⟩ := auxiliarySourceJets_uniform_bound
  have hEach (beta : Fin 3 → ℕ) : ∃ C : ℝ, 0 < C ∧
      ∀ (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
        (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (q : Fin 3 → ℝ),
        (∑ i, beta i) ≤ 3 → ‖coordinateMultiPartial beta
          (fun t => auxiliaryNormalizedInverse g 1 e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he.2 hg hs) q‖ ≤ C := by
    by_cases hb : (∑ i, beta i) ≤ 3
    · obtain ⟨C,hC,hB⟩ := auxiliaryNormalizedInverse_derivatives_uniform beta hb
      exact ⟨C,hC,fun g e he hg hs q _ => hB g 1 e (by norm_num) he hg hs q⟩
    · exact ⟨1,one_pos,fun _ _ _ _ _ _ h => False.elim (hb h)⟩
  choose CQ hCQ hQB using hEach
  intro alpha ha
  let S : ℝ := ∑ beta ∈ multiIndexBox alpha, (multiIndexBinomial alpha beta : ℝ)*
    (CQ beta*scalarDerivativeCoefficientBound (∑ i, (alpha i-beta i))*Cz)
  have hS : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro beta _
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
      (mul_nonneg (hCQ beta).le (scalarDerivativeCoefficientBound_nonnegative _)) hCz.le)
  refine ⟨S+1,by positivity,?_⟩
  intro g e he hg hs q
  let Q := fun t : Fin 3 → ℝ => auxiliaryNormalizedInverse g 1 e
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he.2 hg hs
  let z := fun t : Fin 3 → ℝ => auxiliaryNormalizedSource g e
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he.2
  let B : (HighSectorSpace 1 →L[ℂ] HighSectorSpace 1) →L[ℝ] (HighSectorSpace 1 →L[ℝ] HighSectorSpace 1) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ (HighSectorSpace 1) (HighSectorSpace 1) ℝ ℝ).toContinuousLinearMap
  have hQ : ContDiff ℝ 3 Q := by
    simpa only [Q,Function.comp_def] using!
      (auxiliaryNormalizedInverse_contDiff g 1 e (by norm_num) he hg hs).comp
        (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff
  have hz : ContDiff ℝ 3 z := by
    simpa only [z,Function.comp_def] using!
      (auxiliaryNormalizedSource_contDiff g e he).comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff
  have hprod := coordinateMultiPartial_realBilinear alpha B Q z Set.univ isOpen_univ
    (hQ.of_le (by exact_mod_cast ha)).contDiffOn (hz.of_le (by exact_mod_cast ha)).contDiffOn q (Set.mem_univ q)
  have hNorm : ‖coordinateMultiPartial alpha (fun t => Q t (z t)) q‖ =
      ‖∑ beta ∈ multiIndexBox alpha, multiIndexBinomial alpha beta •
        B (coordinateMultiPartial beta Q q) (coordinateMultiPartial (fun i => alpha i-beta i) z q)‖ := by
    simpa only [B] using! congrArg (fun u : HighSectorSpace 1 => ‖u‖) hprod
  have hZ (delta : Fin 3 → ℕ) : ‖coordinateMultiPartial delta z q‖ ≤
      scalarDerivativeCoefficientBound (∑ i, delta i)*Cz*|g| := by
    have hd := auxiliaryNormalizedSource_multiPartial delta g e he q
    have hj := hzbound (canonicalMultiIndexCoordinates delta) g e
      ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he.2
    calc
      _ = ‖auxiliarySourceJetChartHigh (canonicalMultiIndexCoordinates delta) g e q he.2‖ := by
        simpa only [z] using! congrArg (fun u : HighSectorSpace 1 => ‖u‖) hd
      _ ≤ _ := by
        simpa only [auxiliarySourceJetChartHigh,auxiliarySourceJetHigh_norm,
          canonicalMultiIndexCoordinates_length] using! hj
  have hsum : ‖∑ beta ∈ multiIndexBox alpha, multiIndexBinomial alpha beta •
      B (coordinateMultiPartial beta Q q) (coordinateMultiPartial (fun i => alpha i-beta i) z q)‖ ≤
      ∑ beta ∈ multiIndexBox alpha, (multiIndexBinomial alpha beta : ℝ)*
        (CQ beta*(scalarDerivativeCoefficientBound (∑ i, (alpha i-beta i))*Cz*|g|)) := by
    apply sourceCompNorm_sum_bound
    intro beta hb
    have hdeg := (rs02MultiIndex_order_le alpha beta hb).trans ha
    have hQB' : ‖coordinateMultiPartial beta Q q‖ ≤ CQ beta := hQB beta g e he hg hs q hdeg
    have happly : ‖B (coordinateMultiPartial beta Q q) (coordinateMultiPartial (fun i => alpha i-beta i) z q)‖ ≤
        ‖coordinateMultiPartial beta Q q‖*‖coordinateMultiPartial (fun i => alpha i-beta i) z q‖ := by
      change ‖coordinateMultiPartial beta Q q (coordinateMultiPartial (fun i => alpha i-beta i) z q)‖ ≤ _
      exact (coordinateMultiPartial beta Q q).le_opNorm _
    exact happly.trans (mul_le_mul hQB' (hZ _) (norm_nonneg _) (hCQ beta).le)
  calc
    _ = _ := by simpa only [Q,z] using! hNorm
    _ ≤ _ := hsum
    _ = S*|g| := by simp only [S,Finset.sum_mul,mul_assoc]
    _ ≤ (S+1)*|g| := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (abs_nonneg g)

end Froehlich
