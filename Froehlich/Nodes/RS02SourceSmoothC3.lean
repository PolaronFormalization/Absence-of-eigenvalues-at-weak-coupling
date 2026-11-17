import Froehlich.Nodes.RS02SourceSmoothContinuity
import Froehlich.Nodes.RS02SourceJetsIdentification
import Froehlich.Nodes.CA02CoordinateJets

set_option autoImplicit false

/-! Genuine source C3 regularity on the retained one-particle L2 and actual
high-sector Hilbert carriers, including the identified normalized Riesz source. -/
noncomputable section
namespace Froehlich

theorem auxiliarySourceJetChartL2_contDiff (is : List (Fin 3)) (g e : ℝ) (he : e ≤ 0) (k : ℕ) :
    ContDiff ℝ k (fun q : Fin 3 → ℝ => auxiliarySourceJetChartL2 is g e q he) := by
  apply contDiffOn_univ.mp
  apply contDiffOn_of_continuousCoordinateJets
    (fun js q => auxiliarySourceJetChartL2 js g e q he) (is.length+k) Set.univ isOpen_univ
  · intro js _
    exact (auxiliarySourceJetChartL2_continuous js g e he).continuousOn
  · intro js _ q _ i
    exact auxiliarySourceJetChartL2_hasDerivAt_update js g e he q i
  · exact le_rfl

theorem auxiliarySourceJetL2_contDiff (is : List (Fin 3)) (g e : ℝ) (he : e ≤ 0) (k : ℕ) :
    ContDiff ℝ k (fun p : GW.Space => auxiliarySourceJetL2 is g e p he) := by
  have h := (auxiliarySourceJetChartL2_contDiff is g e he k).comp
    (EuclideanSpace.equiv (Fin 3) ℝ).contDiff
  simpa only [Function.comp_def,auxiliarySourceJetChartL2,ContinuousLinearEquiv.symm_apply_apply] using! h

def oneParticleHighInclusion : GW.OnePhonon →L[ℂ] HighSectorSpace 1 :=
  oneParticleInclusion.codRestrict (HighSectorSpace 1) (by
    intro f
    apply (highSector_mem_iff 1 _).mpr
    apply lp.ext
    funext m
    rw [highSectorProjection_apply]
    by_cases hm : 1 ≤ m
    · rw [if_pos hm]
    · rw [if_neg hm,oneParticleInclusion_apply,
        lp.single_apply_ne 2 1 (oneParticleCoordinate f) (by omega : m ≠ 1)])

theorem auxiliarySourceJetHigh_inclusion (is : List (Fin 3)) (g e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    oneParticleHighInclusion (auxiliarySourceJetL2 is g e p he) = auxiliarySourceJetHigh is g e p he := rfl

local instance rs02SourceSmoothC3HighNormedGroup : NormedAddCommGroup (HighSectorSpace 1) :=
  Submodule.normedAddCommGroup (HighSectorSpace 1)
local instance rs02SourceSmoothC3HighRealSpace : NormedSpace ℝ (HighSectorSpace 1) :=
  NormedSpace.restrictScalars ℝ ℂ _

theorem auxiliarySourceJetHigh_contDiff (is : List (Fin 3)) (g e : ℝ) (he : e ≤ 0) (k : ℕ) :
    ContDiff ℝ k (fun p : GW.Space => auxiliarySourceJetHigh is g e p he) := by
  have h := (oneParticleHighInclusion.restrictScalars ℝ).contDiff.comp
    (auxiliarySourceJetL2_contDiff is g e he k)
  have heq : (fun p : GW.Space => oneParticleHighInclusion (auxiliarySourceJetL2 is g e p he)) =
      (fun p => auxiliarySourceJetHigh is g e p he) := by
    funext p
    exact auxiliarySourceJetHigh_inclusion is g e p he
  change ContDiff ℝ k (fun p : GW.Space => oneParticleHighInclusion (auxiliarySourceJetL2 is g e p he)) at h
  rw [heq] at h
  exact h

theorem auxiliaryNormalizedSource_contDiff (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) :
    ContDiff ℝ 3 (fun p : GW.Space => auxiliaryNormalizedSource g e p he.2) := by
  have heq : (fun p : GW.Space => auxiliaryNormalizedSource g e p he.2) =
      (fun p => auxiliarySourceJetHigh [] g e p he.2) := by
    funext p
    exact auxiliaryNormalizedSource_eq_sourceJetHigh g e p he
  rw [heq]
  exact auxiliarySourceJetHigh_contDiff [] g e he.2 3

end Froehlich
