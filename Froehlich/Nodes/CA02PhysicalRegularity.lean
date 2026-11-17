import Froehlich.Nodes.CA02PhysicalDerivative
import Froehlich.Nodes.CA02ScalarJointBounds
import Froehlich.Nodes.CA02CoordinateJets

set_option autoImplicit false

/-! Joint operator-norm continuity and genuine norm C3 regularity of source G.
The continuity estimate comes from uniform scalar bounds, before invoking
continuous-coordinate-jet calculus. -/
noncomputable section
namespace Froehlich
open scoped BoundedEndReal
local instance ca02PhysicalRegularityHighNormedGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance ca02PhysicalRegularityEndNormedGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ca02PhysicalRegularityEndRealNormedSpace (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace
local instance ca02PhysicalRegularityEndRealBoundedSMul (n : ℕ) : IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  NormedSpace.toIsBoundedSMul
local instance ca02PhysicalRegularityEndRealContinuousSMul (n : ℕ) : ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  IsBoundedSMul.continuousSMul

theorem auxiliaryPhysicalWeightJetChart_joint_lipschitz (is : List (Fin 3))
    (n : ℕ) (e : ℝ) (he : e ≤ 0) (p q : Fin 3 → ℝ) :
    ‖auxiliaryPhysicalWeightJetChart n e he is q-auxiliaryPhysicalWeightJetChart n e he is p‖ ≤
      (‖coordinateDerivativeAssembler (E := ℝ) 3‖*scalarDerivativeCoefficientBound (is.length+1))*‖q-p‖ := by
  let H := ‖coordinateDerivativeAssembler (E := ℝ) 3‖*scalarDerivativeCoefficientBound (is.length+1)
  have hH : 0 ≤ H := mul_nonneg (coordinateDerivativeAssembler (E := ℝ) 3).opNorm_nonneg (scalarDerivativeCoefficientBound_nonnegative _)
  apply operator_norm_le_of_ae_multiplier_coordinates
    (HighSectorSpace n).subtypeₗᵢ (HighSectorSpace n).subtypeₗᵢ _
    (fun m K => ((auxiliaryInverseWeightJetChart is n e q m K-
      auxiliaryInverseWeightJetChart is n e p m K : ℝ) : ℂ))
    (H*‖q-p‖) (mul_nonneg hH (norm_nonneg _))
  · intro m K
    simpa only [Complex.norm_real,Real.norm_eq_abs,H] using
      auxiliaryInverseWeightJetChart_joint_lipschitz is n m e he K p q
  · intro f m
    have h := highOperatorRemainder_ae n
      (auxiliaryPhysicalWeightJetChart n e he is q) (auxiliaryPhysicalWeightJetChart n e he is p)
      (auxiliaryPhysicalWeightJetChart n e he is q) 0
      (auxiliaryInverseWeightJetChart is n e q) (auxiliaryInverseWeightJetChart is n e p)
      (auxiliaryInverseWeightJetChart is n e q)
      (fun f m => auxiliaryPhysicalWeightJetChart_ae is n m e he q f)
      (fun f m => auxiliaryPhysicalWeightJetChart_ae is n m e he p f)
      (fun f m => auxiliaryPhysicalWeightJetChart_ae is n m e he q f) f m
    have hz : (0 : ℝ) • auxiliaryPhysicalWeightJetChart n e he is q = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      change (0 : ℝ) • auxiliaryPhysicalWeightJetChart n e he is q v = 0
      exact zero_smul ℝ _
    rw [hz,sub_zero] at h
    simpa only [zero_mul,sub_zero] using! h

theorem auxiliaryPhysicalWeightJetChart_continuous (is : List (Fin 3))
    (n : ℕ) (e : ℝ) (he : e ≤ 0) : Continuous (auxiliaryPhysicalWeightJetChart n e he is) := by
  let H := ‖coordinateDerivativeAssembler (E := ℝ) 3‖*scalarDerivativeCoefficientBound (is.length+1)
  have hH : 0 ≤ H := mul_nonneg (coordinateDerivativeAssembler (E := ℝ) 3).opNorm_nonneg (scalarDerivativeCoefficientBound_nonnegative _)
  have hL : LipschitzWith ⟨H,hH⟩ (auxiliaryPhysicalWeightJetChart n e he is) := by
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro p q
    simpa only [NNReal.coe_mk,H] using! auxiliaryPhysicalWeightJetChart_joint_lipschitz is n e he q p
  exact hL.continuous

theorem auxiliaryPhysicalWeightJetChart_contDiff (is : List (Fin 3))
    (n : ℕ) (e : ℝ) (he : e ≤ 0) (k : ℕ) :
    ContDiff ℝ k (auxiliaryPhysicalWeightJetChart n e he is) := by
  apply contDiffOn_univ.mp
  apply contDiffOn_of_continuousCoordinateJets (auxiliaryPhysicalWeightJetChart n e he)
    (is.length+k) Set.univ isOpen_univ
  · intro js _
    exact (auxiliaryPhysicalWeightJetChart_continuous js n e he).continuousOn
  · intro js _ p _ i
    exact auxiliaryPhysicalWeightJetChart_hasDerivAt_update js n e he p i
  · exact le_rfl

theorem auxiliaryPhysicalFreeInverse_contDiff (n : ℕ) (e : ℝ) (he : e ≤ 0) :
    ContDiff ℝ 3 (fun p : GW.Space => auxiliaryPhysicalFreeInverse n e p he) := by
  have h := (auxiliaryPhysicalWeightJetChart_contDiff [] n e he 3).comp
    (EuclideanSpace.equiv (Fin 3) ℝ).contDiff
  simpa only [Function.comp_def,auxiliaryPhysicalWeightJetChart,ContinuousLinearEquiv.symm_apply_apply,
    auxiliaryPhysicalWeightJet_nil] using! h

end Froehlich
