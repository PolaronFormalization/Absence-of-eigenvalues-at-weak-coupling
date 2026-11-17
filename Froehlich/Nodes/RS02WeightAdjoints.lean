import Froehlich.Nodes.RS02RealLinear
import Froehlich.Nodes.CA02PhysicalDerivative

/-! Derivatives of the actual real weight multiplier retain self-adjointness. -/
noncomputable section
namespace Froehlich
open scoped BoundedEndReal
local instance rs02WeightAdjointsHighGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance rs02WeightAdjointsEndGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance rs02WeightAdjointsEndReal (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace
local instance rs02WeightAdjointsEndBounded (n : ℕ) : IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  NormedSpace.toIsBoundedSMul
local instance rs02WeightAdjointsEndContinuous (n : ℕ) : ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  IsBoundedSMul.continuousSMul

theorem auxiliaryPhysicalWeightJetChart_selfadjoint (is : List (Fin 3)) (n : ℕ)
    (e : ℝ) (he : e ≤ 0) (p : Fin 3 → ℝ) :
    (auxiliaryPhysicalWeightJetChart n e he is p).adjoint =
      auxiliaryPhysicalWeightJetChart n e he is p := by
  induction is generalizing p with
  | nil => exact auxiliaryPhysicalFreeInverse_selfadjoint n e _ he
  | cons i is ih =>
    have hd := auxiliaryPhysicalWeightJetChart_hasDerivAt_update is n e he p i
    have ha := (boundedAdjointReal (H := HighSectorSpace n)).hasFDerivAt.comp_hasDerivAt (p i) hd
    have hEq : (fun t : ℝ => boundedAdjointReal (auxiliaryPhysicalWeightJetChart n e he is (Function.update p i t))) =
        (fun t : ℝ => auxiliaryPhysicalWeightJetChart n e he is (Function.update p i t)) := by
      funext t
      exact ih _
    change HasDerivAt
      (fun t : ℝ => boundedAdjointReal (auxiliaryPhysicalWeightJetChart n e he is (Function.update p i t)))
      (boundedAdjointReal (auxiliaryPhysicalWeightJetChart n e he (i::is) p)) (p i) at ha
    rw [hEq] at ha
    exact ha.unique hd

theorem auxiliaryPhysicalWeightJet_selfadjoint (is : List (Fin 3)) (n : ℕ)
    (e : ℝ) (he : e ≤ 0) (p : GW.Space) :
    (auxiliaryPhysicalWeightJet is n e p he).adjoint = auxiliaryPhysicalWeightJet is n e p he := by
  simpa only [auxiliaryPhysicalWeightJetChart,ContinuousLinearEquiv.symm_apply_apply] using!
    auxiliaryPhysicalWeightJetChart_selfadjoint is n e he ((EuclideanSpace.equiv (Fin 3) ℝ) p)

end Froehlich
