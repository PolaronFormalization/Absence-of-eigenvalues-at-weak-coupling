import Froehlich.Nodes.PT03KernelDefinitions
import Froehlich.Nodes.PT01InverseContinuity
import Froehlich.Nodes.UV01SourceTransport
import Froehlich.Nodes.RS02SourceDerivativesComposition

set_option autoImplicit false

/-! The literal scalar kernels are jointly measurable. J is jointly
continuous everywhere; C is continuous on the source momentum ball. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

private theorem pt03_extend_continuous (n : ℕ)
    (R : GW.Space → HighSectorSpace n →L[ℂ] HighSectorSpace n) (hR : Continuous R) :
    Continuous (fun p : GW.Space => (HighSectorSpace n).subtypeL.comp ((R p).comp (highSectorProject n))) :=
  (hR.clm_comp_const (highSectorProject n)).const_clm_comp (HighSectorSpace n).subtypeL

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

theorem cutoffThresholdSourceVector_continuous (Lambda : GW.Operators.PositiveCutoff) :
    Continuous (cutoffThresholdSourceVector e he g hg hs Lambda) := by
  let J : HighEnergySpace (-(0 : GW.Space)) 1 →L[ℂ] GW.Fock.Carrier :=
    (energyEmbedding (-(0 : GW.Space))).comp (HighEnergySpace (-(0 : GW.Space)) 1).subtypeL
  let z := loadRiesz (cutoffHighFiberSourceLoad g (-(0 : GW.Space)) 1 Lambda.val)
  let Q := fun p : GW.Space => cutoffCommonEnergyInverse 1 e 0 p (by norm_num) he g hg hs Lambda
  have hQ : Continuous Q := cutoffCommonEnergyInverse_continuous 1 e 0 (by norm_num) he g hg hs Lambda
  have h : Continuous (fun p : GW.Space => J (Q p z)) :=
    J.continuous.comp (hQ.clm_apply continuous_const)
  have heq (p : GW.Space) : J (Q p z) = cutoffThresholdSourceVector e he g hg hs Lambda p := by
    have hsol : Q p z = cutoffCommonSourceSolution 1 e 0 p (by norm_num) he g hg hs Lambda := by
      unfold cutoffCommonSourceSolution
      rw [cutoffCommonSourceLoad_eq]
    rw [hsol,cutoffCommonGroundSourceSolution_eq]
    change energyEmbedding (-(0 : GW.Space))
      (energyCoordinateChange (-(0 : GW.Space)) (-p)
        (cutoffGroundSourceEnergy e p he g hg hs Lambda : EnergySpace (-p))) = _
    exact energyCoordinateChange_intertwines (-(0 : GW.Space)) (-p) _
  have hfun : (fun p : GW.Space => J (Q p z)) = cutoffThresholdSourceVector e he g hg hs Lambda := funext heq
  rw [←hfun]
  exact h

private theorem pt03_J_continuous
    (h : GW.Space → GW.Fock.Carrier)
    (Z X : GW.Space → GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier)
    (hh : Continuous h) (hZ : Continuous Z) (hX : Continuous X) :
    Continuous (fun t : GW.Space × (GW.Space × GW.Space) =>
      ⟪GW.Fock.vacuum-h t.2.1,Z (t.1+t.2.1+t.2.2) (GW.Fock.vacuum-h t.2.2)⟫_ℂ +
      ⟪h t.2.1,X t.1 (h t.2.2)⟫_ℂ) := by
  have hq : Continuous (fun t : GW.Space × (GW.Space × GW.Space) => h t.2.1) :=
    hh.comp (continuous_fst.comp continuous_snd)
  have hr : Continuous (fun t : GW.Space × (GW.Space × GW.Space) => h t.2.2) :=
    hh.comp (continuous_snd.comp continuous_snd)
  have hz : Continuous (fun t : GW.Space × (GW.Space × GW.Space) => Z (t.1+t.2.1+t.2.2)) :=
    hZ.comp ((continuous_fst.add (continuous_fst.comp continuous_snd)).add
      (continuous_snd.comp continuous_snd))
  have hx : Continuous (fun t : GW.Space × (GW.Space × GW.Space) => X t.1) := hX.comp continuous_fst
  exact ((continuous_const.sub hq).inner (𝕜 := ℂ) (hz.clm_apply (continuous_const.sub hr))).add
    (hq.inner (𝕜 := ℂ) (hx.clm_apply hr))

theorem thresholdKernelJ_continuous :
    Continuous (fun t : GW.Space × (GW.Space × GW.Space) => thresholdKernelJ e he g hg hs t.1 t.2.1 t.2.2) := by
  have hh : Continuous (fun p : GW.Space => auxiliaryGroundSourceVector e p he g hg hs) :=
    (auxiliaryGroundSourceVector_contDiff g e he hg hs).continuous
  have hz : Continuous (fun p : GW.Space => auxiliaryZ e p he g hg hs) :=
    pt03_extend_continuous 0 _ (auxiliaryResolvent_contDiff g 0 e (by norm_num) he hg hs).continuous
  have hx0 : Continuous (fun p : GW.Space => auxiliaryExtendedResolvent 2 e p he g hg hs) :=
    pt03_extend_continuous 2 _ (auxiliaryResolvent_contDiff g 2 e (by norm_num) he hg hs).continuous
  have hx : Continuous (fun P : GW.Space => auxiliaryX e he g hg hs P) := hx0.comp continuous_neg
  exact pt03_J_continuous (fun p : GW.Space => auxiliaryGroundSourceVector e p he g hg hs)
    (fun p : GW.Space => auxiliaryZ e p he g hg hs)
    (fun P : GW.Space => auxiliaryX e he g hg hs P) hh hz hx

theorem cutoffThresholdKernelJ_continuous (Lambda : GW.Operators.PositiveCutoff) :
    Continuous (fun t : GW.Space × (GW.Space × GW.Space) => cutoffThresholdKernelJ e he g hg hs Lambda t.1 t.2.1 t.2.2) := by
  have hz : Continuous (fun p : GW.Space => cutoffAuxiliaryZ e p he Lambda g hg hs) :=
    pt03_extend_continuous 0 _ (cutoffAuxiliaryResolvent_continuous 0 e (by norm_num) he g hg hs Lambda)
  have hx0 : Continuous (fun p : GW.Space => cutoffAuxiliaryExtendedResolvent 2 e p he Lambda g hg hs) :=
    pt03_extend_continuous 2 _ (cutoffAuxiliaryResolvent_continuous 2 e (by norm_num) he g hg hs Lambda)
  have hx : Continuous (fun P : GW.Space => cutoffAuxiliaryX e he Lambda g hg hs P) := hx0.comp continuous_neg
  exact pt03_J_continuous (cutoffThresholdSourceVector e he g hg hs Lambda)
    (fun p : GW.Space => cutoffAuxiliaryZ e p he Lambda g hg hs)
    (fun P : GW.Space => cutoffAuxiliaryX e he Lambda g hg hs P)
    (cutoffThresholdSourceVector_continuous e he g hg hs Lambda) hz hx

private theorem pt03_denominator_continuous (e : ℝ) :
    Continuous (fun t : GW.Space × (GW.Space × GW.Space) => 1+e-‖t.1‖^2) :=
  continuous_const.sub (continuous_fst.norm.pow 2)

theorem thresholdKernelC_measurable :
    Measurable (fun t : GW.Space × (GW.Space × GW.Space) => thresholdKernelC e he g hg hs t.1 t.2.1 t.2.2) := by
  have hi := Complex.continuous_ofReal.measurable.comp (pt03_denominator_continuous e).measurable.inv
  exact hi.sub (thresholdKernelJ_continuous e he g hg hs).measurable

theorem cutoffThresholdKernelC_measurable (Lambda : GW.Operators.PositiveCutoff) :
    Measurable (fun t : GW.Space × (GW.Space × GW.Space) => cutoffThresholdKernelC e he g hg hs Lambda t.1 t.2.1 t.2.2) := by
  have hi := Complex.continuous_ofReal.measurable.comp (pt03_denominator_continuous e).measurable.inv
  exact hi.sub (cutoffThresholdKernelJ_continuous e he g hg hs Lambda).measurable

theorem thresholdKernelC_continuousOn :
    ContinuousOn (fun t : GW.Space × (GW.Space × GW.Space) => thresholdKernelC e he g hg hs t.1 t.2.1 t.2.2)
      {t | ‖t.1‖ ≤ 1/4} := by
  intro t ht
  have hn : 1+e-‖t.1‖^2 ≠ 0 := ne_of_gt
    ((by norm_num : (0:ℝ)<11/16).trans_le (thresholdKernel_denominator_lower e he t.1 ht))
  have hi : ContinuousAt (fun x : GW.Space × (GW.Space × GW.Space) =>
      (((1+e-‖x.1‖^2)⁻¹ : ℝ) : ℂ)) t :=
    Complex.continuous_ofReal.continuousAt.comp ((pt03_denominator_continuous e).continuousAt.inv₀ hn)
  exact (hi.sub (thresholdKernelJ_continuous e he g hg hs).continuousAt).continuousWithinAt

theorem cutoffThresholdKernelC_continuousOn (Lambda : GW.Operators.PositiveCutoff) :
    ContinuousOn (fun t : GW.Space × (GW.Space × GW.Space) => cutoffThresholdKernelC e he g hg hs Lambda t.1 t.2.1 t.2.2)
      {t | ‖t.1‖ ≤ 1/4} := by
  intro t ht
  have hn : 1+e-‖t.1‖^2 ≠ 0 := ne_of_gt
    ((by norm_num : (0:ℝ)<11/16).trans_le (thresholdKernel_denominator_lower e he t.1 ht))
  have hi : ContinuousAt (fun x : GW.Space × (GW.Space × GW.Space) =>
      (((1+e-‖x.1‖^2)⁻¹ : ℝ) : ℂ)) t :=
    Complex.continuous_ofReal.continuousAt.comp ((pt03_denominator_continuous e).continuousAt.inv₀ hn)
  exact (hi.sub (cutoffThresholdKernelJ_continuous e he g hg hs Lambda).continuousAt).continuousWithinAt

end Froehlich
