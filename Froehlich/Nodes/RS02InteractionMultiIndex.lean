import Froehlich.Nodes.RS02InteractionSmooth
import Froehlich.Nodes.CA02OperatorMultiIndex
import Froehlich.Nodes.CA01BlockProduct

/-! The literal source multi-index Leibniz formula for the bounded interaction. -/
noncomputable section
namespace Froehlich
open scoped InnerProductSpace BoundedEndReal
local instance rs02InteractionMultiHighNormedGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance rs02InteractionMultiEndNormedGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance rs02InteractionMultiEndRealNormedSpace (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace
local instance rs02InteractionMultiEndBoundedSMul (n : ℕ) : IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  NormedSpace.toIsBoundedSMul
local instance rs02InteractionMultiEndContinuousSMul (n : ℕ) : ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  IsBoundedSMul.continuousSMul

local instance rs02InteractionMultiEnergyNormedGroup (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    NormedAddCommGroup (AuxiliaryEnergySpace n e p0 he) :=
  Submodule.normedAddCommGroup (AuxiliaryEnergySpace n e p0 he)
local instance rs02InteractionMultiMapNormedGroup (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    NormedAddCommGroup (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance rs02InteractionMultiMapRealNormedSpace (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    NormedSpace ℝ (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance rs02InteractionMultiMapBoundedSMul (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  NormedSpace.toIsBoundedSMul
local instance rs02InteractionMultiMapContinuousSMul (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  IsBoundedSMul.continuousSMul

local instance rs02InteractionMultiNestedContinuous (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    ContinuousSMul ℝ ((HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) →L[ℂ]
      (HighSectorSpace n →L[ℂ] HighSectorSpace n)) := by
  exact realContinuousSMulOfComplex
    (E := (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) →L[ℂ]
      (HighSectorSpace n →L[ℂ] HighSectorSpace n))

theorem auxiliaryInteractionJetPair_fixed_sandwich (g : ℝ) (is js : List (Fin 3))
    (n : ℕ) (e : ℝ) (p0 p : GW.Space) (hn : n ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) :
    auxiliaryInteractionJetPair g is js n e p he.2 =
      formSandwichReal (auxiliaryFixedInteractionForm g n e p0 he.2)
        (auxiliaryFixedEnergyWeightJet is n e p0 p he.2)
        (auxiliaryFixedEnergyWeightJet js n e p0 p he.2) := by
  apply formRepresentative_unique
  intro w u
  exact auxiliaryInteractionJetPair_spec g is js n e p0 p hn he w u

theorem auxiliaryInteractionOperator_multiPartial (alpha : Fin 3 → ℕ) (g : ℝ)
    (n : ℕ) (e : ℝ) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (q : Fin 3 → ℝ) :
    coordinateMultiPartial alpha
      (fun p => auxiliaryInteractionOperator g n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2) q =
      ∑ beta ∈ multiIndexBox alpha, multiIndexBinomial alpha beta •
        auxiliaryInteractionJetPair g (canonicalMultiIndexCoordinates beta)
          (canonicalMultiIndexCoordinates (fun i => alpha i-beta i)) n e
            ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he.2 := by
  let p0 : GW.Space := 0
  let J := fun p : Fin 3 → ℝ => auxiliaryFixedEnergyWeightJet [] n e p0
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2
  let a := auxiliaryFixedInteractionForm g n e p0 he.2
  have hJ : ContDiff ℝ (∑ i, alpha i : ℕ) J := by
    exact auxiliaryFixedEnergyWeightJetChart_contDiff [] n e p0 he.2 (∑ i, alpha i)
  have hEq : (fun p => auxiliaryInteractionOperator g n e
      ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2) =
      (fun p => formSandwichReal a (J p) (J p)) := by
    funext p
    exact auxiliaryInteraction_fixed_sandwich g n e p0 _ hn he
  rw [hEq]
  have h := coordinateMultiPartial_realBilinear alpha (formSandwichReal a) J J
    Set.univ isOpen_univ hJ.contDiffOn hJ.contDiffOn q (Set.mem_univ q)
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro beta _
  apply congrArg (fun A => multiIndexBinomial alpha beta • A)
  dsimp only [J]
  rw [auxiliaryFixedEnergyWeightJet_zero_multiPartial,
    auxiliaryFixedEnergyWeightJet_zero_multiPartial]
  exact (auxiliaryInteractionJetPair_fixed_sandwich g _ _ n e p0 _ hn he).symm

def interactionDerivativeBound (alpha : Fin 3 → ℕ) : ℝ :=
  ∑ beta ∈ multiIndexBox alpha, (multiIndexBinomial alpha beta : ℝ)*
    (scalarDerivativeCoefficientBound (∑ i, beta i)*
      scalarDerivativeCoefficientBound (∑ i, (alpha i-beta i))*auxiliaryResolventConstant)

theorem interactionDerivativeBound_nonneg (alpha : Fin 3 → ℕ) :
    0 ≤ interactionDerivativeBound alpha := by
  apply Finset.sum_nonneg
  intro beta _
  exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
    (mul_nonneg (scalarDerivativeCoefficientBound_nonnegative _)
      (scalarDerivativeCoefficientBound_nonnegative _)) auxiliaryResolventConstant_pos.le)

theorem auxiliaryInteractionOperator_multiPartial_norm_le (alpha : Fin 3 → ℕ) (g : ℝ)
    (n : ℕ) (e : ℝ) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (hg : |g| ≤ 1) (q : Fin 3 → ℝ) :
    ‖coordinateMultiPartial alpha
      (fun p => auxiliaryInteractionOperator g n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2) q‖ ≤
      interactionDerivativeBound alpha*|g| := by
  classical
  rw [auxiliaryInteractionOperator_multiPartial alpha g n e hn he]
  calc
    _ ≤ ∑ beta ∈ multiIndexBox alpha, ‖multiIndexBinomial alpha beta •
        auxiliaryInteractionJetPair g (canonicalMultiIndexCoordinates beta)
          (canonicalMultiIndexCoordinates (fun i => alpha i-beta i)) n e
            ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he.2‖ := norm_sum_le _ _
    _ ≤ ∑ beta ∈ multiIndexBox alpha, (multiIndexBinomial alpha beta : ℝ)*
        (scalarDerivativeCoefficientBound (∑ i, beta i)*
          scalarDerivativeCoefficientBound (∑ i, (alpha i-beta i))*auxiliaryResolventConstant*|g|) := by
      apply Finset.sum_le_sum
      intro beta _
      have h := auxiliaryInteractionJetPair_norm_le g (canonicalMultiIndexCoordinates beta)
        (canonicalMultiIndexCoordinates (fun i => alpha i-beta i)) n e
          ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he.2 hg
      have hN : ‖multiIndexBinomial alpha beta •
          auxiliaryInteractionJetPair g (canonicalMultiIndexCoordinates beta)
            (canonicalMultiIndexCoordinates (fun i => alpha i-beta i)) n e
              ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he.2‖ ≤
          (multiIndexBinomial alpha beta : ℝ)*
            ‖auxiliaryInteractionJetPair g (canonicalMultiIndexCoordinates beta)
              (canonicalMultiIndexCoordinates (fun i => alpha i-beta i)) n e
                ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he.2‖ := norm_nsmul_le
      have ht := hN.trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))
      simpa only [canonicalMultiIndexCoordinates_length] using! ht
    _ = interactionDerivativeBound alpha*|g| := by
      simp only [interactionDerivativeBound,Finset.sum_mul,mul_assoc]

end Froehlich
