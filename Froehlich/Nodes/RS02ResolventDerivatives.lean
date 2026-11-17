import Froehlich.Nodes.RS02InverseSmooth
import Froehlich.Nodes.RS02ResolventFactorTerms
import Froehlich.Nodes.CA02OperatorMultiIndex
import Froehlich.Nodes.CA01BlockProduct

set_option autoImplicit false

/-! Literal finite middle factors for the source's differentiated G Q G. -/
noncomputable section
namespace Froehlich
open scoped BoundedEndReal
local instance rs02ResolventDerivativesHighGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance rs02ResolventDerivativesEndGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance rs02ResolventDerivativesEndReal (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace
local instance rs02ResolventDerivativesEndBounded (n : ℕ) : IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  NormedSpace.toIsBoundedSMul
local instance rs02ResolventDerivativesEndContinuous (n : ℕ) : ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  IsBoundedSMul.continuousSMul

theorem auxiliaryResolventMiddleTerm_norm_le (is js : List (Fin 3)) (n : ℕ) (e : ℝ)
    (p : GW.Space) (he : e ≤ 0) (A : HighSectorSpace n →L[ℂ] HighSectorSpace n) :
    ‖auxiliaryResolventMiddleTerm is js n e p he A‖ ≤
      scalarDerivativeCoefficientBound is.length * ‖A‖ * scalarDerivativeCoefficientBound js.length := by
  let D := auxiliaryRelativeWeightJet is n e p he
  let E := auxiliaryRelativeWeightJet js n e p he
  have hD : ‖D‖ ≤ scalarDerivativeCoefficientBound is.length := auxiliaryRelativeWeightJet_norm_le is n e p he
  have hE : ‖E.adjoint‖ ≤ scalarDerivativeCoefficientBound js.length :=
    (ContinuousLinearMap.adjoint.norm_map E).trans_le (auxiliaryRelativeWeightJet_norm_le js n e p he)
  change ‖D.comp (A.comp E.adjoint)‖ ≤ _
  calc
    _ ≤ ‖D‖*‖A.comp E.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖D‖*(‖A‖*‖E.adjoint‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) D.opNorm_nonneg
    _ ≤ scalarDerivativeCoefficientBound is.length*(‖A‖*scalarDerivativeCoefficientBound js.length) :=
      mul_le_mul hD (mul_le_mul_of_nonneg_left hE A.opNorm_nonneg)
        (mul_nonneg A.opNorm_nonneg E.adjoint.opNorm_nonneg)
        (scalarDerivativeCoefficientBound_nonnegative is.length)
    _ = _ := by ring

def auxiliaryResolventMiddleJet (alpha : Fin 3 → ℕ) (n : ℕ) (e : ℝ) (p : GW.Space)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2) : HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  ∑ beta ∈ multiIndexBox alpha, multiIndexBinomial alpha beta •
    ∑ gamma ∈ multiIndexBox (fun i => alpha i-beta i),
      multiIndexBinomial (fun i => alpha i-beta i) gamma •
        auxiliaryResolventMiddleTerm (canonicalMultiIndexCoordinates beta)
          (canonicalMultiIndexCoordinates (fun i => alpha i-beta i-gamma i)) n e p he.2
          (coordinateMultiPartial gamma
            (fun q => auxiliaryNormalizedInverse g n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he.2 hg hsmall)
            ((EuclideanSpace.equiv (Fin 3) ℝ) p))

theorem auxiliaryResolvent_multiPartial_factor (alpha : Fin 3 → ℕ) (ha : (∑ i, alpha i) ≤ 3)
    (n : ℕ) (e : ℝ) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2)
    (q : Fin 3 → ℝ) :
    coordinateMultiPartial alpha
      (fun t => auxiliaryResolvent n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hsmall) q =
      (auxiliaryPhysicalFreeInverse n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he.2).comp
        ((auxiliaryResolventMiddleJet alpha n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he g hg hsmall).comp
          (auxiliaryPhysicalFreeInverse n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he.2)) := by
  let G := fun t : Fin 3 → ℝ => auxiliaryPhysicalFreeInverse n e
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he.2
  let Q := fun t : Fin 3 → ℝ => auxiliaryNormalizedInverse g n e
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he.2 hg hsmall
  let B := ContinuousLinearMap.mul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n)
  let H := fun t => B (Q t) (G t)
  have hG : ContDiff ℝ 3 G := by
    simpa only [G,Function.comp_def] using!
      (auxiliaryPhysicalFreeInverse_contDiff n e he.2).comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff
  have hQ : ContDiff ℝ 3 Q := by
    simpa only [Q,Function.comp_def] using!
      (auxiliaryNormalizedInverse_contDiff g n e hn he hg hsmall).comp
        (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff
  have hH : ContDiff ℝ 3 H := by
    simpa only [H,Function.comp_apply] using! (B.contDiff.comp hQ).clm_apply hG
  have hGa : ContDiffOn ℝ (∑ i, alpha i : ℕ) G Set.univ :=
    (hG.of_le (by exact_mod_cast ha)).contDiffOn
  have hHa : ContDiffOn ℝ (∑ i, alpha i : ℕ) H Set.univ :=
    (hH.of_le (by exact_mod_cast ha)).contDiffOn
  have ho := coordinateMultiPartial_realBilinear alpha B G H Set.univ isOpen_univ hGa hHa q (Set.mem_univ q)
  have hi (beta : Fin 3 → ℕ) :
      coordinateMultiPartial (fun i => alpha i-beta i) H q =
        ∑ gamma ∈ multiIndexBox (fun i => alpha i-beta i),
          multiIndexBinomial (fun i => alpha i-beta i) gamma •
            B (coordinateMultiPartial gamma Q q)
              (coordinateMultiPartial (fun i => alpha i-beta i-gamma i) G q) := by
    have hd : (∑ i, (alpha i-beta i)) ≤ 3 :=
      (Finset.sum_le_sum (fun i _ => Nat.sub_le (alpha i) (beta i))).trans ha
    exact coordinateMultiPartial_realBilinear (fun i => alpha i-beta i) B Q G Set.univ isOpen_univ
      (hQ.of_le (by exact_mod_cast hd)).contDiffOn (hG.of_le (by exact_mod_cast hd)).contDiffOn q (Set.mem_univ q)
  change coordinateMultiPartial alpha (fun t => B (G t) (H t)) q = _
  rw [ho]
  let L := ContinuousLinearMap.mulLeftRight ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) (G q) (G q)
  have hL (A : HighSectorSpace n →L[ℂ] HighSectorSpace n) :
      L A = (G q).comp (A.comp (G q)) := by
    simp only [L,ContinuousLinearMap.mulLeftRight_apply,mul_assoc]
    apply ContinuousLinearMap.ext
    intro u
    rfl
  rw [←hL]
  change _ = L (auxiliaryResolventMiddleJet alpha n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he g hg hsmall)
  simp only [auxiliaryResolventMiddleJet,ContinuousLinearEquiv.apply_symm_apply,map_sum,map_nsmul]
  apply Finset.sum_congr rfl
  intro beta _
  apply congrArg (fun A => multiIndexBinomial alpha beta • A)
  rw [hi beta]
  simp only [map_sum,map_nsmul]
  apply Finset.sum_congr rfl
  intro gamma _
  apply congrArg (fun A => multiIndexBinomial (fun i => alpha i-beta i) gamma • A)
  dsimp only [G]
  rw [auxiliaryPhysicalFreeInverse_multiPartial,auxiliaryPhysicalFreeInverse_multiPartial]
  rw [hL]
  exact auxiliaryResolventMiddleTerm_factor _ _ n e _ he.2 _

end Froehlich
