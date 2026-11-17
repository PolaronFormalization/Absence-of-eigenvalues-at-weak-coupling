import Froehlich.Nodes.RS01PhysicalResolvent
import Froehlich.Nodes.FA01

/-! Full-domain two-sided compressed resolvent. The actual onto energy
lift conjugates M and M⁻¹; FA01 supplies all retained physical inverse fields. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)

def auxiliaryCompressedEnergyOperator (g : ℝ) : HighEnergySpace (-p) n →L[ℂ] HighEnergySpace (-p) n :=
  ((auxiliaryEnergyLiftEquivalence n e p hn he).symm.toContinuousLinearMap).adjoint.comp
    ((auxiliaryNormalizedOperator g n e p he.2).comp
      (auxiliaryEnergyLiftEquivalence n e p hn he).symm.toContinuousLinearMap)

variable (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2)

def auxiliaryCompressedEnergyInverse : HighEnergySpace (-p) n →L[ℂ] HighEnergySpace (-p) n :=
  (auxiliaryEnergyLiftEquivalence n e p hn he).toContinuousLinearMap.comp
    ((auxiliaryNormalizedInverse g n e p he.2 hg hsmall).comp
      (auxiliaryEnergyLiftEquivalence n e p hn he).toContinuousLinearMap.adjoint)

theorem auxiliaryCompressedEnergyOperator_spec (w u : HighEnergySpace (-p) n) :
    ⟪w,auxiliaryCompressedEnergyOperator n e p hn he g u⟫_ℂ =
      (compressedFiberFormData g (-p) n none).form w u -
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
    _ = ⟪L.symm w,auxiliaryNormalizedOperator g n e p he.2 (L.symm u)⟫_ℂ := by
      exact L.symm.toContinuousLinearMap.adjoint_inner_right w _
    _ = (fiberFormData g (-p) none).form
        (auxiliaryEnergyLift n e p he.2 (L.symm w)) (auxiliaryEnergyLift n e p he.2 (L.symm u)) +
        ((1-(n : ℝ)-e : ℝ) : ℂ)*
        ⟪energyEmbedding (-p) (auxiliaryEnergyLift n e p he.2 (L.symm w)),
          energyEmbedding (-p) (auxiliaryEnergyLift n e p he.2 (L.symm u))⟫_ℂ :=
      auxiliaryNormalizedOperator_form n e p hn he g (L.symm w) (L.symm u)
    _ = _ := by
      rw [hw,hu,hi]
      change (fiberFormData g (-p) none).form w u + ((1-(n : ℝ)-e : ℝ) : ℂ)*
        ⟪energyEmbedding (-p) (w : EnergySpace (-p)),energyEmbedding (-p) (u : EnergySpace (-p))⟫_ℂ =
        (fiberFormData g (-p) none).form w u - ((e-1+(n : ℝ) : ℝ) : ℂ)*
          ⟪energyEmbedding (-p) (w : EnergySpace (-p)),energyEmbedding (-p) (u : EnergySpace (-p))⟫_ℂ
      push_cast
      ring

theorem auxiliaryCompressedEnergyInverse_left :
    auxiliaryCompressedEnergyInverse n e p hn he g hg hsmall * auxiliaryCompressedEnergyOperator n e p hn he g = 1 := by
  let L := auxiliaryEnergyLiftEquivalence n e p hn he
  have ha (v : HighSectorSpace n) : L.toContinuousLinearMap.adjoint
      (L.symm.toContinuousLinearMap.adjoint v) = v := by
    have h : L.symm.toContinuousLinearMap.comp L.toContinuousLinearMap = ContinuousLinearMap.id ℂ (HighSectorSpace n) :=
      ContinuousLinearMap.ext L.symm_apply_apply
    have h' := congrArg ContinuousLinearMap.adjoint h
    simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_id] at h'
    exact congrArg (fun T : HighSectorSpace n →L[ℂ] HighSectorSpace n => T v) h'
  apply ContinuousLinearMap.ext
  intro u
  change L (auxiliaryNormalizedInverse g n e p he.2 hg hsmall
    (L.toContinuousLinearMap.adjoint (L.symm.toContinuousLinearMap.adjoint
      (auxiliaryNormalizedOperator g n e p he.2 (L.symm u))))) = u
  rw [ha]
  have hm := congrArg (fun T : HighSectorSpace n →L[ℂ] HighSectorSpace n => T (L.symm u))
    (auxiliaryNormalizedInverse_left g n e p he.2 hg hsmall)
  change auxiliaryNormalizedInverse g n e p he.2 hg hsmall
    (auxiliaryNormalizedOperator g n e p he.2 (L.symm u)) = L.symm u at hm
  rw [hm,L.apply_symm_apply]

theorem auxiliaryCompressedEnergyInverse_right :
    auxiliaryCompressedEnergyOperator n e p hn he g * auxiliaryCompressedEnergyInverse n e p hn he g hg hsmall = 1 := by
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
  change L.symm.toContinuousLinearMap.adjoint (auxiliaryNormalizedOperator g n e p he.2
    (L.symm (L (auxiliaryNormalizedInverse g n e p he.2 hg hsmall (L.toContinuousLinearMap.adjoint u))))) = u
  rw [L.symm_apply_apply]
  have hm := congrArg (fun T : HighSectorSpace n →L[ℂ] HighSectorSpace n => T (L.toContinuousLinearMap.adjoint u))
    (auxiliaryNormalizedInverse_right g n e p he.2 hg hsmall)
  change auxiliaryNormalizedOperator g n e p he.2
    (auxiliaryNormalizedInverse g n e p he.2 hg hsmall (L.toContinuousLinearMap.adjoint u)) = L.toContinuousLinearMap.adjoint u at hm
  rw [hm,ha]

theorem auxiliaryCompressedEnergyInverse_physical :
    physicalEnergyInverse (compressedFiberFormData g (-p) n none)
      (auxiliaryCompressedEnergyInverse n e p hn he g hg hsmall) = auxiliaryResolvent n e p he g hg hsmall := by
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
  change highEnergyEmbedding (-p) n (L (auxiliaryNormalizedInverse g n e p he.2 hg hsmall
    (L.toContinuousLinearMap.adjoint ((highEnergyEmbedding (-p) n).adjoint f)))) =
      auxiliaryPhysicalFreeInverse n e p he.2
        (auxiliaryNormalizedInverse g n e p he.2 hg hsmall (auxiliaryPhysicalFreeInverse n e p he.2 f))
  rw [auxiliaryEnergyLift_high_physical n e p hn he,hf]

include hn in
theorem auxiliaryResolvent_isResolvent :
    GW.Operators.IsResolvent (compressedHamiltonian g (-p) n none) ((e-1+(n : ℝ) : ℝ) : ℂ)
      (auxiliaryResolvent n e p he g hg hsmall) := by
  have h := physicalEnergyInverse_isResolvent (compressedFiberFormData g (-p) n none) (e-1+(n : ℝ))
    (auxiliaryCompressedEnergyOperator n e p hn he g) (auxiliaryCompressedEnergyInverse n e p hn he g hg hsmall)
    (auxiliaryCompressedEnergyOperator_spec n e p hn he g)
    (auxiliaryCompressedEnergyInverse_left n e p hn he g hg hsmall)
    (auxiliaryCompressedEnergyInverse_right n e p hn he g hg hsmall)
  rw [auxiliaryCompressedEnergyInverse_physical n e p hn he g hg hsmall] at h
  exact h

end Froehlich
