import Froehlich.Nodes.PT01CoreLeftLimitField
import Froehlich.Nodes.PT01RegularSourceLimit
import Froehlich.Nodes.PT01CutoffPullthrough

/-! Remove the cutoff in precisely the source's local L² topology. The
left limit concerns a regular physical source, not a one-particle form load. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Froehlich

theorem ptCoreLocal_isBounded (K : Set GW.Space) (R : ℝ) (hKR : ∀ k ∈ K, ‖k‖ ≤ R) :
    Bornology.IsBounded K := isBounded_iff_forall_norm_le.mpr ⟨R,hKR⟩

theorem cutoffPullthroughVector_eq_project (m : ℕ) (e : ℝ) (p : GW.Space)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (Lambda : GW.Operators.PositiveCutoff)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (F : HighSectorSpace (m+1)) :
    cutoffPullthroughVector m e p he Lambda g hg hs F=
      highSectorProject m (cutoffAuxiliaryResolvent (m+1) e p he Lambda g hg hs F : GW.Fock.Carrier) := by
  apply Subtype.ext
  change (cutoffAuxiliaryResolvent (m+1) e p he Lambda g hg hs F : GW.Fock.Carrier)=
    highSectorProjection m (cutoffAuxiliaryResolvent (m+1) e p he Lambda g hg hs F : GW.Fock.Carrier)
  exact ((highSector_mem_iff m _).mp (highSector_mem_of_succ m _
    (cutoffAuxiliaryResolvent (m+1) e p he Lambda g hg hs F).property)).symm

theorem cutoffPullthroughSource_eq_regular (m : ℕ) (e : ℝ) (p : GW.Space)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (Lambda : GW.Operators.PositiveCutoff)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (K : Set GW.Space) (F : NumberFormSpace) (hF : numberFormEmbedding F ∈ HighSectorSpace (m+1)) :
    cutoffPullthroughSource m e p he Lambda g hg hs K F hF=
      localPullthroughSource m K F
        (highSectorProject m (cutoffAuxiliaryResolvent (m+1) e p he Lambda g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier))
        (fun k => cutoffFormFactorL2 g Lambda.val Lambda.property k)
        ((Lp.memLp (cutoffFormFactorL2 g Lambda.val Lambda.property)).restrict K) := by
  unfold cutoffPullthroughSource
  rw [cutoffPullthroughVector_eq_project]

theorem uncutPullthrough_local (m : ℕ) (e : ℝ) (p : GW.Space) (hm : m+1 ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (K : Set GW.Space) (hK : MeasurableSet K)
    (R : ℝ) (hR : 0 ≤ R) (hKR : ∀ k ∈ K, ‖k‖ ≤ R) (F : NumberFormSpace)
    (hF : numberFormEmbedding F ∈ HighSectorSpace (m+1)) :
    LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K
      (annihilationField (ptRegularSingularNumberVector (m+1) e p hm he g hg hs ⟨numberFormEmbedding F,hF⟩))=
      (HighSectorSpace m).subtypeL.compLp
        (localSingularInverseField m e p ((Nat.le_succ m).trans hm) he g hg hs K hK
          (ptCoreLocal_isBounded K R hKR)
          (localPullthroughSource m K F
            (highSectorProject m (auxiliaryResolvent (m+1) e p he g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier))
            (fun k => (fiberFormFactor g k : ℂ)) (regularSource_local_formFactor_memLp g K hK R hKR))) := by
  let f : HighSectorSpace (m+1) := ⟨numberFormEmbedding F,hF⟩
  let J : Lp (HighSectorSpace m) 2 ((volume : Measure GW.Space).restrict K) →L[ℂ]
      Lp GW.Fock.Carrier 2 ((volume : Measure GW.Space).restrict K) :=
    (HighSectorSpace m).subtypeL.compLpL 2 ((volume : Measure GW.Space).restrict K)
  let Q : GW.Operators.PositiveCutoff → Lp (HighSectorSpace m) 2 ((volume : Measure GW.Space).restrict K) := fun Lambda =>
    localCutoffInverseField m e p ((Nat.le_succ m).trans hm) he g hg hs K hK Lambda
      (localPullthroughSource m K F
        (highSectorProject m (cutoffAuxiliaryResolvent (m+1) e p he Lambda g hg hs f : GW.Fock.Carrier))
        (fun k => cutoffFormFactorL2 g Lambda.val Lambda.property k)
        ((Lp.memLp (cutoffFormFactorL2 g Lambda.val Lambda.property)).restrict K))
  let S := localSingularInverseField m e p ((Nat.le_succ m).trans hm) he g hg hs K hK
    (ptCoreLocal_isBounded K R hKR)
    (localPullthroughSource m K F
      (highSectorProject m (auxiliaryResolvent (m+1) e p he g hg hs f : GW.Fock.Carrier))
      (fun k => (fiberFormFactor g k : ℂ)) (regularSource_local_formFactor_memLp g K hK R hKR))
  have hQ : Tendsto Q atTop (𝓝 S) :=
    regularSource_cutoff_rhs_tendsto m e p hm he g hg hs K hK (ptCoreLocal_isBounded K R hKR) R hKR F hF
  have hright : Tendsto (fun Lambda => J (Q Lambda)) atTop (𝓝 (J S)) := (J.continuous.tendsto S).comp hQ
  have hleft := regularCutoff_annihilation_local_tendsto (m+1) e p hm he g hg hs f K
  have hcut (Lambda : GW.Operators.PositiveCutoff) :
      LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K
        (annihilationField (freeGraphNumberCoordinates (-p)
          (cutoffAuxiliaryGraphCoordinate (m+1) e p hm he Lambda g hg hs f)))=J (Q Lambda) := by
    have h := cutoffPullthrough_local m e p hm he Lambda g hg hs K hK R hR hKR F hF
    rw [cutoffPullthroughSource_eq_regular] at h
    exact h
  have heq : (fun Lambda : GW.Operators.PositiveCutoff =>
      LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K
        (annihilationField (freeGraphNumberCoordinates (-p)
          (cutoffAuxiliaryGraphCoordinate (m+1) e p hm he Lambda g hg hs f))))=(fun Lambda => J (Q Lambda)) := funext hcut
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

end Froehlich
