import Froehlich.Nodes.UV01

/-! CV01: fixed physical embeddings carry genuine common-energy inverse
convergence to operator-norm convergence on the fixed physical high sector. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def fixedPhysicalInverseMap (j : V →L[ℂ] H) : (V →L[ℂ] V) →L[ℂ] (H →L[ℂ] H) :=
  (ContinuousLinearMap.compL ℂ H V H j).comp ((ContinuousLinearMap.compL ℂ H V V).flip j.adjoint)

@[simp] theorem fixedPhysicalInverseMap_apply (j : V →L[ℂ] H) (Q : V →L[ℂ] V) :
    fixedPhysicalInverseMap j Q=j.comp (Q.comp j.adjoint) := rfl

theorem fixedPhysicalInverseMap_error (j : V →L[ℂ] H) (Q T : V →L[ℂ] V) :
    ‖fixedPhysicalInverseMap j Q-fixedPhysicalInverseMap j T‖ ≤ ‖j‖^2*‖Q-T‖ := by
  rw [←map_sub,fixedPhysicalInverseMap_apply]
  calc
    _ ≤ ‖j‖*‖(Q-T).comp j.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖j‖*(‖Q-T‖*‖j.adjoint‖) := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.opNorm_comp_le _ _) j.opNorm_nonneg
    _ = _ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring

variable (n : ℕ) (e : ℝ) (p0 p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2)

theorem cutoffCommonEnergyInverse_physical (Λ : GW.Operators.PositiveCutoff) :
    fixedPhysicalInverseMap (highEnergyEmbedding (-p0) n)
      (cutoffCommonEnergyInverse n e p0 p hn he g hg hsmall Λ) =
        cutoffAuxiliaryResolvent n e p he Λ g hg hsmall := by
  let B := highEnergyCoordinateChange (-p0) (-p) n
  have hj : (highEnergyEmbedding (-p0) n).comp B=highEnergyEmbedding (-p) n :=
    ContinuousLinearMap.ext (highEnergyCoordinateChange_physical (-p0) (-p) n)
  have ha := congrArg ContinuousLinearMap.adjoint hj
  simp only [ContinuousLinearMap.adjoint_comp] at ha
  have hc : fixedPhysicalInverseMap (highEnergyEmbedding (-p0) n)
      (cutoffCommonEnergyInverse n e p0 p hn he g hg hsmall Λ) =
      (highEnergyEmbedding (-p) n).comp
        ((cutoffAuxiliaryEnergyInverse n e p hn he g hg hsmall Λ).comp (highEnergyEmbedding (-p) n).adjoint) := by
    simp only [fixedPhysicalInverseMap_apply,cutoffCommonEnergyInverse,ContinuousLinearMap.comp_assoc]
    rw [←ContinuousLinearMap.comp_assoc (highEnergyEmbedding (-p0) n),hj,ha]
  rw [hc]
  exact cutoffCompressedEnergyInverse_physical n e p hn he Λ g hg hsmall

theorem singularCommonEnergyInverse_physical :
    fixedPhysicalInverseMap (highEnergyEmbedding (-p0) n)
      (singularCommonEnergyInverse n e p0 p hn he g hg hsmall) = auxiliaryResolvent n e p he g hg hsmall := by
  let B := highEnergyCoordinateChange (-p0) (-p) n
  have hj : (highEnergyEmbedding (-p0) n).comp B=highEnergyEmbedding (-p) n :=
    ContinuousLinearMap.ext (highEnergyCoordinateChange_physical (-p0) (-p) n)
  have ha := congrArg ContinuousLinearMap.adjoint hj
  simp only [ContinuousLinearMap.adjoint_comp] at ha
  have hc : fixedPhysicalInverseMap (highEnergyEmbedding (-p0) n)
      (singularCommonEnergyInverse n e p0 p hn he g hg hsmall) =
      (highEnergyEmbedding (-p) n).comp
        ((auxiliaryCompressedEnergyInverse n e p hn he g hg hsmall).comp (highEnergyEmbedding (-p) n).adjoint) := by
    simp only [fixedPhysicalInverseMap_apply,singularCommonEnergyInverse,ContinuousLinearMap.comp_assoc]
    rw [←ContinuousLinearMap.comp_assoc (highEnergyEmbedding (-p0) n),hj,ha]
  rw [hc]
  exact auxiliaryCompressedEnergyInverse_physical n e p hn he g hg hsmall

include hn p0 in
theorem cutoffAuxiliaryResolvent_uniform_on_bounded (K : Set GW.Space) (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn
      (fun Λ : GW.Operators.PositiveCutoff => fun p : GW.Space => cutoffAuxiliaryResolvent n e p he Λ g hg hsmall)
      (fun p : GW.Space => auxiliaryResolvent n e p he g hg hsmall) atTop K := by
  have h := (fixedPhysicalInverseMap (highEnergyEmbedding (-p0) n)).uniformContinuous.comp_tendstoUniformlyOn
    (cutoffCommonEnergyInverse_uniform_on_bounded n e p0 hn he g hg hsmall K hK)
  simpa only [Function.comp_def,cutoffCommonEnergyInverse_physical n e p0 _ hn he g hg hsmall,
    singularCommonEnergyInverse_physical n e p0 _ hn he g hg hsmall] using! h

end Froehlich
