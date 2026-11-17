import Froehlich.Nodes.UV01EnergyInverse
import Froehlich.Nodes.FA01

/-! Actual cutoff compressed maximal-domain resolvent at the same fixed e. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

private theorem conjugatedInverse_left {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (L : H ≃L[ℂ] E) (M Q : H →L[ℂ] H) (hQM : Q*M=1) :
    (L.toContinuousLinearMap.comp (Q.comp L.toContinuousLinearMap.adjoint)) *
      (L.symm.toContinuousLinearMap.adjoint.comp (M.comp L.symm.toContinuousLinearMap)) = 1 := by
  have ha (v : H) : L.toContinuousLinearMap.adjoint (L.symm.toContinuousLinearMap.adjoint v) = v := by
    have h : L.symm.toContinuousLinearMap.comp L.toContinuousLinearMap = ContinuousLinearMap.id ℂ H :=
      ContinuousLinearMap.ext L.symm_apply_apply
    have h' := congrArg ContinuousLinearMap.adjoint h
    simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_id] at h'
    exact congrArg (fun T : H →L[ℂ] H => T v) h'
  apply ContinuousLinearMap.ext
  intro u
  change L (Q (L.toContinuousLinearMap.adjoint (L.symm.toContinuousLinearMap.adjoint (M (L.symm u))))) = u
  rw [ha]
  have hm := congrArg (fun T : H →L[ℂ] H => T (L.symm u)) hQM
  change Q (M (L.symm u)) = L.symm u at hm
  rw [hm,L.apply_symm_apply]

variable (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (Λ : GW.Operators.PositiveCutoff)

def cutoffCompressedEnergyOperator (g : ℝ) : HighEnergySpace (-p) n →L[ℂ] HighEnergySpace (-p) n :=
  ((auxiliaryEnergyLiftEquivalence n e p hn he).symm.toContinuousLinearMap).adjoint.comp
    ((cutoffAuxiliaryNormalizedOperator g Λ.val Λ.property n e p he.2).comp
      (auxiliaryEnergyLiftEquivalence n e p hn he).symm.toContinuousLinearMap)

variable (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2)

def cutoffAuxiliaryResolvent : HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  (auxiliaryPhysicalFreeInverse n e p he.2).comp
    ((cutoffAuxiliaryNormalizedInverse g Λ.val Λ.property n e p he.2 hg hsmall).comp
      (auxiliaryPhysicalFreeInverse n e p he.2))

theorem cutoffCompressedEnergyOperator_spec (w u : HighEnergySpace (-p) n) :
    ⟪w,cutoffCompressedEnergyOperator n e p hn he Λ g u⟫_ℂ =
      (compressedFiberFormData g (-p) n (some Λ)).form w u -
      ((e-1+(n : ℝ) : ℝ) : ℂ)*⟪highEnergyEmbedding (-p) n w,highEnergyEmbedding (-p) n u⟫_ℂ := by
  let L := auxiliaryEnergyLiftEquivalence n e p hn he
  have hw : auxiliaryEnergyLift n e p he.2 (L.symm w) = (w : EnergySpace (-p)) := by
    rw [← auxiliaryEnergyLiftEquivalence_val n e p hn he]
    exact congrArg (fun z : HighEnergySpace (-p) n => (z : EnergySpace (-p))) (L.apply_symm_apply w)
  have hu : auxiliaryEnergyLift n e p he.2 (L.symm u) = (u : EnergySpace (-p)) := by
    rw [← auxiliaryEnergyLiftEquivalence_val n e p hn he]
    exact congrArg (fun z : HighEnergySpace (-p) n => (z : EnergySpace (-p))) (L.apply_symm_apply u)
  have hi : ⟪highEnergyEmbedding (-p) n w,highEnergyEmbedding (-p) n u⟫_ℂ =
      ⟪energyEmbedding (-p) (w : EnergySpace (-p)),energyEmbedding (-p) (u : EnergySpace (-p))⟫_ℂ := by
    change ⟪(highEnergyEmbedding (-p) n w : GW.Fock.Carrier),
      (highEnergyEmbedding (-p) n u : GW.Fock.Carrier)⟫_ℂ = _
    rw [highEnergyEmbedding_apply,highEnergyEmbedding_apply]
  calc
    _ = ⟪L.symm w,cutoffAuxiliaryNormalizedOperator g Λ.val Λ.property n e p he.2 (L.symm u)⟫_ℂ := by
      exact L.symm.toContinuousLinearMap.adjoint_inner_right w _
    _ = (fiberFormData g (-p) (some Λ)).form
        (auxiliaryEnergyLift n e p he.2 (L.symm w)) (auxiliaryEnergyLift n e p he.2 (L.symm u)) +
        ((1-(n : ℝ)-e : ℝ) : ℂ)*
        ⟪energyEmbedding (-p) (auxiliaryEnergyLift n e p he.2 (L.symm w)),
          energyEmbedding (-p) (auxiliaryEnergyLift n e p he.2 (L.symm u))⟫_ℂ :=
      cutoffAuxiliaryNormalizedOperator_form n e p hn he g Λ (L.symm w) (L.symm u)
    _ = _ := by
      rw [hw,hu,hi]
      change (fiberFormData g (-p) (some Λ)).form w u + ((1-(n : ℝ)-e : ℝ) : ℂ)*
        ⟪energyEmbedding (-p) (w : EnergySpace (-p)),energyEmbedding (-p) (u : EnergySpace (-p))⟫_ℂ =
        (fiberFormData g (-p) (some Λ)).form w u - ((e-1+(n : ℝ) : ℝ) : ℂ)*
          ⟪energyEmbedding (-p) (w : EnergySpace (-p)),energyEmbedding (-p) (u : EnergySpace (-p))⟫_ℂ
      push_cast
      ring

theorem cutoffCompressedEnergyInverse_left :
    cutoffAuxiliaryEnergyInverse n e p hn he g hg hsmall Λ * cutoffCompressedEnergyOperator n e p hn he Λ g = 1 := by
  simpa only [cutoffAuxiliaryEnergyInverse,cutoffCompressedEnergyOperator] using
    conjugatedInverse_left (auxiliaryEnergyLiftEquivalence n e p hn he)
      (cutoffAuxiliaryNormalizedOperator g Λ.val Λ.property n e p he.2)
      (cutoffAuxiliaryNormalizedInverse g Λ.val Λ.property n e p he.2 hg hsmall)
      (cutoffAuxiliaryNormalizedInverse_left g Λ.val Λ.property n e p he.2 hg hsmall)

theorem cutoffCompressedEnergyInverse_right :
    cutoffCompressedEnergyOperator n e p hn he Λ g * cutoffAuxiliaryEnergyInverse n e p hn he g hg hsmall Λ = 1 := by
  let L := auxiliaryEnergyLiftEquivalence n e p hn he
  have ha (v : HighEnergySpace (-p) n) : L.symm.toContinuousLinearMap.adjoint
      (L.toContinuousLinearMap.adjoint v) = v := by
    have h : L.toContinuousLinearMap.comp L.symm.toContinuousLinearMap = ContinuousLinearMap.id ℂ (HighEnergySpace (-p) n) :=
      ContinuousLinearMap.ext L.apply_symm_apply
    have h' := congrArg ContinuousLinearMap.adjoint h
    simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_id] at h'
    exact congrArg (fun T : HighEnergySpace (-p) n →L[ℂ] HighEnergySpace (-p) n => T v) h'
  apply ContinuousLinearMap.ext
  intro u
  change L.symm.toContinuousLinearMap.adjoint (cutoffAuxiliaryNormalizedOperator g Λ.val Λ.property n e p he.2
    (L.symm (L (cutoffAuxiliaryNormalizedInverse g Λ.val Λ.property n e p he.2 hg hsmall (L.toContinuousLinearMap.adjoint u))))) = u
  rw [L.symm_apply_apply]
  have hm := congrArg (fun T : HighSectorSpace n →L[ℂ] HighSectorSpace n => T (L.toContinuousLinearMap.adjoint u))
    (cutoffAuxiliaryNormalizedInverse_right g Λ.val Λ.property n e p he.2 hg hsmall)
  change cutoffAuxiliaryNormalizedOperator g Λ.val Λ.property n e p he.2
    (cutoffAuxiliaryNormalizedInverse g Λ.val Λ.property n e p he.2 hg hsmall (L.toContinuousLinearMap.adjoint u)) = L.toContinuousLinearMap.adjoint u at hm
  rw [hm,ha]

theorem cutoffCompressedEnergyInverse_physical :
    physicalEnergyInverse (compressedFiberFormData g (-p) n (some Λ))
      (cutoffAuxiliaryEnergyInverse n e p hn he g hg hsmall Λ) = cutoffAuxiliaryResolvent n e p he Λ g hg hsmall := by
  let L := auxiliaryEnergyLiftEquivalence n e p hn he
  have hj : (highEnergyEmbedding (-p) n).comp L.toContinuousLinearMap = auxiliaryPhysicalFreeInverse n e p he.2 :=
    ContinuousLinearMap.ext (auxiliaryEnergyLift_high_physical n e p hn he)
  have ha := congrArg ContinuousLinearMap.adjoint hj
  simp only [ContinuousLinearMap.adjoint_comp,auxiliaryPhysicalFreeInverse_selfadjoint] at ha
  apply ContinuousLinearMap.ext
  intro f
  have hf := congrArg (fun T : HighSectorSpace n →L[ℂ] HighSectorSpace n => T f) ha
  change L.toContinuousLinearMap.adjoint ((highEnergyEmbedding (-p) n).adjoint f) =
    auxiliaryPhysicalFreeInverse n e p he.2 f at hf
  change highEnergyEmbedding (-p) n (L (cutoffAuxiliaryNormalizedInverse g Λ.val Λ.property n e p he.2 hg hsmall
    (L.toContinuousLinearMap.adjoint ((highEnergyEmbedding (-p) n).adjoint f)))) =
      auxiliaryPhysicalFreeInverse n e p he.2
        (cutoffAuxiliaryNormalizedInverse g Λ.val Λ.property n e p he.2 hg hsmall (auxiliaryPhysicalFreeInverse n e p he.2 f))
  rw [auxiliaryEnergyLift_high_physical n e p hn he,hf]

include hn in
theorem cutoffAuxiliaryResolvent_isResolvent :
    GW.Operators.IsResolvent (compressedHamiltonian g (-p) n (some Λ)) ((e-1+(n : ℝ) : ℝ) : ℂ)
      (cutoffAuxiliaryResolvent n e p he Λ g hg hsmall) := by
  have h := physicalEnergyInverse_isResolvent (compressedFiberFormData g (-p) n (some Λ)) (e-1+(n : ℝ))
    (cutoffCompressedEnergyOperator n e p hn he Λ g) (cutoffAuxiliaryEnergyInverse n e p hn he g hg hsmall Λ)
    (cutoffCompressedEnergyOperator_spec n e p hn he Λ g)
    (cutoffCompressedEnergyInverse_left n e p hn he Λ g hg hsmall)
    (cutoffCompressedEnergyInverse_right n e p hn he Λ g hg hsmall)
  rw [cutoffCompressedEnergyInverse_physical n e p hn he Λ g hg hsmall] at h
  exact h

theorem cutoffAuxiliaryResolvent_norm_le : ‖cutoffAuxiliaryResolvent n e p he Λ g hg hsmall‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  have hG (u : HighSectorSpace n) : ‖auxiliaryPhysicalFreeInverse n e p he.2 u‖ ≤ ‖u‖ :=
    ((auxiliaryPhysicalFreeInverse n e p he.2).le_opNorm u).trans
      (by nlinarith [auxiliaryPhysicalFreeInverse_norm_le n e p he.2,norm_nonneg u])
  have hM := (cutoffAuxiliaryNormalizedInverse g Λ.val Λ.property n e p he.2 hg hsmall).le_opNorm
    (auxiliaryPhysicalFreeInverse n e p he.2 f)
  have hMi := cutoffAuxiliaryNormalizedInverse_norm_le g Λ.val Λ.property n e p he.2 hg hsmall
  change ‖auxiliaryPhysicalFreeInverse n e p he.2
    (cutoffAuxiliaryNormalizedInverse g Λ.val Λ.property n e p he.2 hg hsmall (auxiliaryPhysicalFreeInverse n e p he.2 f))‖ ≤ 2*‖f‖
  exact (hG _).trans (hM.trans (by nlinarith [hG f,norm_nonneg (auxiliaryPhysicalFreeInverse n e p he.2 f)]))

end Froehlich
