import Froehlich.Nodes.RS02InverseDerivativeBoundsRecurrence
import Froehlich.Nodes.RS02InverseDerivativeBoundsFinite

set_option autoImplicit false

/-! Uniform bounds for genuine canonical derivatives of the ACTUAL chosen
normalized inverse. The private record merely packages all quantified
parameters before the finite recurrence chooses its constants. -/
noncomputable section
namespace Froehlich
open scoped BoundedEndReal
local instance rs02InverseBoundsHighGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance rs02InverseBoundsEndGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance rs02InverseBoundsEndReal (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace
local instance rs02InverseBoundsEndBounded (n : ℕ) : IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  NormedSpace.toIsBoundedSMul
local instance rs02InverseBoundsEndContinuous (n : ℕ) : ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  IsBoundedSMul.continuousSMul

private structure InverseBoundParameters where
  n : ℕ
  hn : n ≤ 2
  e : ℝ
  he : e ∈ Set.Icc (-1/4 : ℝ) 0
  g : ℝ
  hg : |g| ≤ 1
  hsmall : auxiliaryResolventConstant*|g| ≤ 1/2
  q : Fin 3 → ℝ

theorem auxiliaryNormalizedInverse_derivatives_uniform :
    ∀ alpha : Fin 3 → ℕ, (∑ i, alpha i) ≤ 3 → ∃ C : ℝ, 0 < C ∧
      ∀ (g : ℝ) (n : ℕ) (e : ℝ) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
        (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2) (q : Fin 3 → ℝ),
        ‖coordinateMultiPartial alpha
          (fun p => auxiliaryNormalizedInverse g n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2 hg hsmall) q‖ ≤ C := by
  let F : (Fin 3 → ℕ) → InverseBoundParameters → ℝ := fun alpha P =>
    ‖coordinateMultiPartial alpha
      (fun p => auxiliaryNormalizedInverse P.g P.n P.e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p)
        P.he.2 P.hg P.hsmall) P.q‖
  have hzero : ∀ P : InverseBoundParameters, F 0 P ≤ 2 := by
    intro P
    simpa only [F,coordinateMultiPartial_zero] using!
      auxiliaryNormalizedInverse_norm_le P.g P.n P.e
        ((EuclideanSpace.equiv (Fin 3) ℝ).symm P.q) P.he.2 P.hg P.hsmall
  have hrec : ∀ alpha, (∑ i, alpha i) ≤ 3 → alpha ≠ 0 → ∀ P : InverseBoundParameters,
      F alpha P ≤ 2*∑ beta ∈ (multiIndexBox alpha).erase 0,
        (multiIndexBinomial alpha beta : ℝ)*(interactionDerivativeBound beta*F (fun i => alpha i-beta i) P) := by
    intro alpha ha ha0 P
    simpa only [F] using! rs02NormalizedInverse_recurrence_norm_le alpha ha ha0
      P.g P.n P.e P.hn P.he P.hg P.hsmall P.q
  have h := rs02UniformInverseRecurrence_bound 3 F interactionDerivativeBound
    interactionDerivativeBound_nonneg hzero hrec
  intro alpha ha
  obtain ⟨C,hC,hbound⟩ := h alpha ha
  refine ⟨C,hC,?_⟩
  intro g n e hn he hg hsmall q
  let P : InverseBoundParameters := ⟨n,hn,e,he,g,hg,hsmall,q⟩
  simpa only [F,P] using! hbound P

end Froehlich
