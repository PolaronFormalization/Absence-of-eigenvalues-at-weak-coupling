import Froehlich.Nodes.CA02FixedEnergyDerivative
import Froehlich.Nodes.CA02WeightedScalarJointBounds
import Froehlich.Nodes.CA02CoordinateJets

set_option autoImplicit false

/-! Joint norm continuity and C3 regularity in the actual fixed weighted
energy target. All coordinate derivatives are the genuine operator jets. -/
noncomputable section
namespace Froehlich
open scoped BoundedEndReal
local instance ca02FixedEnergyRegularityHighNormedGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance ca02FixedEnergyRegularityEndNormedGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ca02FixedEnergyRegularityEndRealNormedSpace (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace
local instance ca02FixedEnergyRegularityEndRealBoundedSMul (n : ℕ) : IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  NormedSpace.toIsBoundedSMul
local instance ca02FixedEnergyRegularityEndRealContinuousSMul (n : ℕ) : ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  IsBoundedSMul.continuousSMul

theorem auxiliaryFixedEnergyJetChartCoordinates_joint_lipschitzOn
    (is : List (Fin 3)) (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0)
    (p q r : Fin 3 → ℝ) (hq : q ∈ Metric.closedBall p 1) (hr : r ∈ Metric.closedBall p 1) :
    ‖auxiliaryFixedEnergyJetChartCoordinates n e p0 he is r-
      auxiliaryFixedEnergyJetChartCoordinates n e p0 he is q‖ ≤
      (‖coordinateDerivativeAssembler (E := ℝ) 3‖*scalarDerivativeCoefficientBound (is.length+1)*
        (1+‖p0-(EuclideanSpace.equiv (Fin 3) ℝ).symm p‖+euclideanChartInverseNorm))*‖r-q‖ := by
  let C := ‖coordinateDerivativeAssembler (E := ℝ) 3‖*scalarDerivativeCoefficientBound (is.length+1)*
    (1+‖p0-(EuclideanSpace.equiv (Fin 3) ℝ).symm p‖+euclideanChartInverseNorm)
  have hE : 0 ≤ euclideanChartInverseNorm :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.opNorm_nonneg
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg
    (coordinateDerivativeAssembler (E := ℝ) 3).opNorm_nonneg
    (scalarDerivativeCoefficientBound_nonnegative _)) (by positivity)
  let a : (Fin 3 → ℝ) → ∀ m, GW.Fock.Coordinates m → ℝ :=
    fun u m K => auxiliaryWeight n e p0 m K*auxiliaryInverseWeightJetChart is n e u m K
  apply operator_norm_le_of_ae_multiplier_coordinates
    (HighSectorSpace n).subtypeₗᵢ (HighSectorSpace n).subtypeₗᵢ _
    (fun m K => ((a r m K-a q m K : ℝ) : ℂ)) (C*‖r-q‖) (mul_nonneg hC (norm_nonneg _))
  · intro m K
    have heq : a r m K-a q m K = auxiliaryWeight n e p0 m K*
        (auxiliaryInverseWeightJetChart is n e r m K-auxiliaryInverseWeightJetChart is n e q m K) := by
      dsimp only [a]; ring
    rw [heq,Complex.norm_real,Real.norm_eq_abs]
    simpa only [C] using! auxiliaryFixedWeightJetChart_joint_lipschitzOn is n m e p0 he K p q r hq hr
  · intro f m
    have h := highOperatorRemainder_ae n
      (auxiliaryFixedEnergyJetChartCoordinates n e p0 he is r)
      (auxiliaryFixedEnergyJetChartCoordinates n e p0 he is q)
      (auxiliaryFixedEnergyJetChartCoordinates n e p0 he is r) 0
      (a r) (a q) (a r)
      (fun f m => auxiliaryFixedEnergyJetChartCoordinates_ae is n m e p0 he r f)
      (fun f m => auxiliaryFixedEnergyJetChartCoordinates_ae is n m e p0 he q f)
      (fun f m => auxiliaryFixedEnergyJetChartCoordinates_ae is n m e p0 he r f) f m
    have hz : (0 : ℝ) • auxiliaryFixedEnergyJetChartCoordinates n e p0 he is r = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      change (0 : ℝ) • auxiliaryFixedEnergyJetChartCoordinates n e p0 he is r v = 0
      exact zero_smul ℝ _
    rw [hz,sub_zero] at h
    simpa only [zero_mul,sub_zero] using! h

theorem auxiliaryFixedEnergyJetChartCoordinates_continuous (is : List (Fin 3))
    (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    Continuous (auxiliaryFixedEnergyJetChartCoordinates n e p0 he is) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let C := ‖coordinateDerivativeAssembler (E := ℝ) 3‖*scalarDerivativeCoefficientBound (is.length+1)*
    (1+‖p0-(EuclideanSpace.equiv (Fin 3) ℝ).symm p‖+euclideanChartInverseNorm)
  have hE : 0 ≤ euclideanChartInverseNorm :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.opNorm_nonneg
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg
    (coordinateDerivativeAssembler (E := ℝ) 3).opNorm_nonneg
    (scalarDerivativeCoefficientBound_nonnegative _)) (by positivity)
  have hLip : LipschitzOnWith ⟨C,hC⟩ (auxiliaryFixedEnergyJetChartCoordinates n e p0 he is)
      (Metric.closedBall p 1) := by
    apply lipschitzOnWith_iff_norm_sub_le.mpr
    intro q hq r hr
    simpa only [dist_eq_norm,NNReal.coe_mk,C] using!
      auxiliaryFixedEnergyJetChartCoordinates_joint_lipschitzOn is n e p0 he p r q hr hq
  exact hLip.continuousOn.continuousAt (Metric.closedBall_mem_nhds p (by norm_num))

local instance ca02FixedEnergyRegularityEnergyNormedGroup (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    NormedAddCommGroup (AuxiliaryEnergySpace n e p0 he) :=
  Submodule.normedAddCommGroup (AuxiliaryEnergySpace n e p0 he)
local instance ca02FixedEnergyRegularityEnergyMapNormedGroup (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    NormedAddCommGroup (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ca02FixedEnergyRegularityEnergyMapRealNormedSpace (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    NormedSpace ℝ (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance ca02FixedEnergyRegularityEnergyMapRealBoundedSMul (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  NormedSpace.toIsBoundedSMul
local instance ca02FixedEnergyRegularityEnergyMapRealContinuousSMul (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  IsBoundedSMul.continuousSMul

theorem auxiliaryFixedEnergyWeightJetChart_continuous (is : List (Fin 3))
    (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    Continuous (auxiliaryFixedEnergyWeightJetChart n e p0 he is) := by
  let L : (HighSectorSpace n →L[ℂ] HighSectorSpace n) →L[ℝ]
      (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
    ((ContinuousLinearMap.compL ℂ (HighSectorSpace n) (HighSectorSpace n)
      (AuxiliaryEnergySpace n e p0 he))
      (auxiliaryFreeInverseEnergy n e p0 he).toLinearIsometry.toContinuousLinearMap).restrictScalars ℝ
  have hc := L.continuous.comp (auxiliaryFixedEnergyJetChartCoordinates_continuous is n e p0 he)
  apply hc.congr
  intro q
  apply ContinuousLinearMap.ext
  intro f
  change (auxiliaryEnergyCoordinates n e p0 he).symm
    ((auxiliaryEnergyCoordinates n e p0 he) (auxiliaryFixedEnergyWeightJetChart n e p0 he is q f)) = _
  exact (auxiliaryEnergyCoordinates n e p0 he).symm_apply_apply _

theorem auxiliaryFixedEnergyWeightJetChart_contDiff (is : List (Fin 3))
    (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) (k : ℕ) :
    ContDiff ℝ k (auxiliaryFixedEnergyWeightJetChart n e p0 he is) := by
  apply contDiffOn_univ.mp
  apply contDiffOn_of_continuousCoordinateJets (auxiliaryFixedEnergyWeightJetChart n e p0 he)
    (is.length+k) Set.univ isOpen_univ
  · intro js _
    exact (auxiliaryFixedEnergyWeightJetChart_continuous js n e p0 he).continuousOn
  · intro js _ p _ i
    exact auxiliaryFixedEnergyWeightJetChart_hasDerivAt_update js n e p0 he p i
  · exact le_rfl

theorem auxiliaryFixedEnergyWeightJet_zero_contDiff (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    ContDiff ℝ 3 (fun p : GW.Space => auxiliaryFixedEnergyWeightJet [] n e p0 p he) := by
  have h := (auxiliaryFixedEnergyWeightJetChart_contDiff [] n e p0 he 3).comp
    (EuclideanSpace.equiv (Fin 3) ℝ).contDiff
  simpa only [Function.comp_def,auxiliaryFixedEnergyWeightJetChart,
    ContinuousLinearEquiv.symm_apply_apply] using! h

end Froehlich
