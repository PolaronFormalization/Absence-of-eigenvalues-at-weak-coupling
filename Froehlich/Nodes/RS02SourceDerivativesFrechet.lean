import Froehlich.Nodes.RS02SourceDerivatives
import Froehlich.Nodes.CA01TotalDerivative

set_option autoImplicit false

/-! The true Euclidean total derivative of the normalized source is the
assembled genuine coordinate jets, with a parameter-independent Hilbert
operator norm bound. -/
noncomputable section
namespace Froehlich
local instance rs02SourceDerivativesFrechetHighNormedGroup : NormedAddCommGroup (HighSectorSpace 1) :=
  Submodule.normedAddCommGroup (HighSectorSpace 1)
local instance rs02SourceDerivativesFrechetHighRealSpace : NormedSpace ℝ (HighSectorSpace 1) :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance rs02SourceDerivativesFrechetHighBoundedSMul : IsBoundedSMul ℝ (HighSectorSpace 1) :=
  NormedSpace.toIsBoundedSMul
local instance rs02SourceDerivativesFrechetHighContinuousSMul : ContinuousSMul ℝ (HighSectorSpace 1) :=
  IsBoundedSMul.continuousSMul

local instance rs02SourceDerivativesFrechetTotalDerivativeNorm :
    Norm (GW.Space →L[ℝ] HighSectorSpace 1) := ContinuousLinearMap.hasOpNorm

theorem auxiliarySourceJetHigh_hasFDerivAt (is : List (Fin 3)) (g e : ℝ) (he : e ≤ 0) (p : GW.Space) :
    HasFDerivAt (fun q : GW.Space => auxiliarySourceJetHigh is g e q he)
      (euclideanCoordinateDerivative 3 (fun i => auxiliarySourceJetHigh (i::is) g e p he)) p := by
  apply euclideanContinuousPartials_hasFDerivAt 3 _
    (fun q i => auxiliarySourceJetHigh (i::is) g e q he) Set.univ isOpen_univ
  · intro i
    exact (auxiliarySourceJetHigh_contDiff (i::is) g e he 0).continuous.continuousOn
  · intro q _ i
    have h := auxiliarySourceJetChartHigh_hasDerivAt_update is g e he
      ((EuclideanSpace.equiv (Fin 3) ℝ) q) i
    simpa only [auxiliarySourceJetChartHigh,ContinuousLinearEquiv.symm_apply_apply] using! h
  · exact Set.mem_univ p

theorem auxiliaryNormalizedSource_hasFDerivAt (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (p : GW.Space) :
    HasFDerivAt (fun q : GW.Space => auxiliaryNormalizedSource g e q he.2)
      (euclideanCoordinateDerivative 3 (fun i => auxiliarySourceJetHigh [i] g e p he.2)) p := by
  have heq : (fun q : GW.Space => auxiliaryNormalizedSource g e q he.2) =
      (fun q => auxiliarySourceJetHigh [] g e q he.2) := by
    funext q
    exact auxiliaryNormalizedSource_eq_sourceJetHigh g e q he
  rw [heq]
  exact auxiliarySourceJetHigh_hasFDerivAt [] g e he.2 p

theorem auxiliaryNormalizedSource_fderiv_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (p : GW.Space),
      ‖fderiv ℝ (fun q : GW.Space => auxiliaryNormalizedSource g e q he.2) p‖ ≤ C*|g| := by
  obtain ⟨Cv,hCv,hv⟩ := auxiliarySourceJets_uniform_bound
  let A := coordinateDerivativeAssembler (E := HighSectorSpace 1) 3
  let L := (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap
  let C := ‖A‖*scalarDerivativeCoefficientBound 1*Cv*‖L‖
  have hA : 0 ≤ ‖A‖ := A.opNorm_nonneg
  have hL : 0 ≤ ‖L‖ := L.opNorm_nonneg
  have hCr := scalarDerivativeCoefficientBound_nonnegative 1
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (mul_nonneg hA hCr) hCv.le) hL
  refine ⟨C+1,by positivity,?_⟩
  intro g e he p
  have hd := (auxiliaryNormalizedSource_hasFDerivAt g e he p).fderiv
  have hnorm : ‖fderiv ℝ (fun q : GW.Space => auxiliaryNormalizedSource g e q he.2) p‖ =
      ‖euclideanCoordinateDerivative 3 (fun i => auxiliarySourceJetHigh [i] g e p he.2)‖ := by
    simpa only [] using! congrArg (fun T : GW.Space →L[ℝ] HighSectorSpace 1 => ‖T‖) hd
  have htuple : ‖(fun i : Fin 3 => auxiliarySourceJetHigh [i] g e p he.2)‖ ≤
      scalarDerivativeCoefficientBound 1*Cv*|g| := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hCr hCv.le) (abs_nonneg g))).mpr
    intro i
    simpa only [auxiliarySourceJetHigh_norm,List.length_singleton] using! hv [i] g e p he.2
  have hcoord : ‖coordinateDerivative 3 (fun i => auxiliarySourceJetHigh [i] g e p he.2)‖ ≤
      ‖A‖*(scalarDerivativeCoefficientBound 1*Cv*|g|) :=
    (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left htuple hA)
  calc
    _ = ‖euclideanCoordinateDerivative 3 (fun i => auxiliarySourceJetHigh [i] g e p he.2)‖ := hnorm
    _ ≤ ‖coordinateDerivative 3 (fun i => auxiliarySourceJetHigh [i] g e p he.2)‖*‖L‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖A‖*(scalarDerivativeCoefficientBound 1*Cv*|g|))*‖L‖ :=
      mul_le_mul_of_nonneg_right hcoord hL
    _ = C*|g| := by dsimp only [C]; ring
    _ ≤ (C+1)*|g| := by nlinarith [abs_nonneg g]

end Froehlich
