import Froehlich.Nodes.PT01InverseFieldVarying
import Froehlich.Nodes.PT01SourceField

set_option autoImplicit false

/-! Local regular-source limits use the true uncut coefficient only in L2(K),
obtained from a finite cutoff which agrees on the bounded set. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Froehlich

theorem localCutoffFormFactor_ae (g : ℝ) (Λ : GW.Operators.PositiveCutoff)
    (K : Set GW.Space) (hK : MeasurableSet K) (R : ℝ)
    (hKR : ∀ k ∈ K, ‖k‖ ≤ R) (hΛ : R ≤ Λ.val) :
    cutoffFormFactorL2 g Λ.val Λ.property =ᵐ[volume.restrict K]
      (fun k => (fiberFormFactor g k : ℂ)) := by
  filter_upwards [ae_restrict_of_ae (s := K) (cutoffFormFactorL2_ae g Λ.val Λ.property),
    self_mem_ae_restrict hK] with k hk hmem
  rw [hk]
  simp only [cutoffFormFactor,if_pos ((hKR k hmem).trans hΛ)]

theorem regularSource_local_formFactor_memLp (g : ℝ) (K : Set GW.Space) (hK : MeasurableSet K)
    (R : ℝ) (hKR : ∀ k ∈ K, ‖k‖ ≤ R) :
    MemLp (fun k => (fiberFormFactor g k : ℂ)) 2 (volume.restrict K) := by
  let L : GW.Operators.PositiveCutoff := ⟨max R 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _)⟩
  exact MemLp.ae_eq (localCutoffFormFactor_ae g L K hK R hKR (le_max_left _ _))
    ((Lp.memLp (cutoffFormFactorL2 g L.val L.property)).restrict K)

private theorem localPullthroughSource_continuous (m : ℕ) (K : Set GW.Space)
    (F : NumberFormSpace) (v : GW.Space → ℂ) (hv : MemLp v 2 (volume.restrict K)) :
    Continuous (fun u : HighSectorSpace m => localPullthroughSource m K F u v hv) := by
  let B : HighSectorSpace m →L[ℂ] ℂ →L[ℂ] HighSectorSpace m :=
    ContinuousLinearMap.smulRightL ℂ ℂ (HighSectorSpace m) (ContinuousLinearMap.id ℂ ℂ)
  let A : HighSectorSpace m →L[ℂ] Lp (HighSectorSpace m) 2 (volume.restrict K) :=
    (B.compLpL₂ 2 (volume.restrict K)).flip (hv.toLp v)
  change Continuous (fun u : HighSectorSpace m => restrictedHighAnnihilationField m K F-A u)
  exact continuous_const.sub A.continuous

theorem regularSource_cutoff_vector_tendsto (m : ℕ) (e : ℝ) (p : GW.Space)
    (hm : m+1 ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (F : HighSectorSpace (m+1)) :
    Tendsto (fun Λ : GW.Operators.PositiveCutoff => highSectorProject m
      (cutoffAuxiliaryResolvent (m+1) e p he Λ g hg hs F : GW.Fock.Carrier)) atTop
      (𝓝 (highSectorProject m (auxiliaryResolvent (m+1) e p he g hg hs F : GW.Fock.Carrier))) := by
  have hR : Tendsto
      (fun Λ : GW.Operators.PositiveCutoff => cutoffAuxiliaryResolvent (m+1) e p he Λ g hg hs) atTop
      (𝓝 (auxiliaryResolvent (m+1) e p he g hg hs)) :=
    (cutoffAuxiliaryResolvent_uniform_on_bounded (m+1) e 0 hm he g hg hs
      {p} Bornology.isBounded_singleton).tendsto_at (Set.mem_singleton p)
  let J : HighSectorSpace (m+1) →L[ℂ] HighSectorSpace m :=
    (highSectorProject m).comp (HighSectorSpace (m+1)).subtypeL
  let E : (HighSectorSpace (m+1) →L[ℂ] HighSectorSpace (m+1)) →L[ℂ] HighSectorSpace (m+1) :=
    ContinuousLinearMap.apply ℂ (HighSectorSpace (m+1)) F
  let A : (HighSectorSpace (m+1) →L[ℂ] HighSectorSpace (m+1)) →L[ℂ] HighSectorSpace m := J.comp E
  have hA : Tendsto
      (fun Λ : GW.Operators.PositiveCutoff => A (cutoffAuxiliaryResolvent (m+1) e p he Λ g hg hs)) atTop
      (𝓝 (A (auxiliaryResolvent (m+1) e p he g hg hs))) :=
    (A.continuous.tendsto (auxiliaryResolvent (m+1) e p he g hg hs)).comp hR
  exact hA

theorem regularSource_local_source_tendsto (m : ℕ) (e : ℝ) (p : GW.Space)
    (hm : m+1 ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (K : Set GW.Space) (hK : MeasurableSet K)
    (R : ℝ) (hKR : ∀ k ∈ K, ‖k‖ ≤ R) (F : NumberFormSpace)
    (hF : numberFormEmbedding F ∈ HighSectorSpace (m+1)) :
    Tendsto (fun Λ : GW.Operators.PositiveCutoff => localPullthroughSource m K F
      (highSectorProject m (cutoffAuxiliaryResolvent (m+1) e p he Λ g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier))
      (fun k => cutoffFormFactorL2 g Λ.val Λ.property k)
      ((Lp.memLp (cutoffFormFactorL2 g Λ.val Λ.property)).restrict K)) atTop
      (𝓝 (localPullthroughSource m K F
        (highSectorProject m (auxiliaryResolvent (m+1) e p he g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier))
        (fun k => (fiberFormFactor g k : ℂ)) (regularSource_local_formFactor_memLp g K hK R hKR))) := by
  let hv := regularSource_local_formFactor_memLp g K hK R hKR
  have hbase := (localPullthroughSource_continuous m K F (fun k => (fiberFormFactor g k : ℂ)) hv).tendsto _
    |>.comp (regularSource_cutoff_vector_tendsto m e p hm he g hg hs ⟨numberFormEmbedding F,hF⟩)
  apply hbase.congr'
  have hevent : ∀ᶠ Λ : GW.Operators.PositiveCutoff in atTop, R ≤ Λ.val := by
    exact eventually_atTop.mpr ⟨⟨max R 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _)⟩,
      fun Λ hΛ => (le_max_left R 1).trans hΛ⟩
  filter_upwards [hevent] with Λ hΛ
  unfold localPullthroughSource
  rw [MemLp.toLp_congr _ hv (localCutoffFormFactor_ae g Λ K hK R hKR hΛ)]
  rfl

theorem regularSource_cutoff_rhs_tendsto (m : ℕ) (e : ℝ) (p : GW.Space)
    (hm : m+1 ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (K : Set GW.Space) (hK : MeasurableSet K)
    (hKb : Bornology.IsBounded K) (R : ℝ) (hKR : ∀ k ∈ K, ‖k‖ ≤ R) (F : NumberFormSpace)
    (hF : numberFormEmbedding F ∈ HighSectorSpace (m+1)) :
    Tendsto (fun Λ : GW.Operators.PositiveCutoff => localCutoffInverseField m e p
      ((Nat.le_succ m).trans hm) he g hg hs K hK Λ
      (localPullthroughSource m K F
        (highSectorProject m (cutoffAuxiliaryResolvent (m+1) e p he Λ g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier))
        (fun k => cutoffFormFactorL2 g Λ.val Λ.property k)
        ((Lp.memLp (cutoffFormFactorL2 g Λ.val Λ.property)).restrict K))) atTop
      (𝓝 (localSingularInverseField m e p ((Nat.le_succ m).trans hm) he g hg hs K hK hKb
        (localPullthroughSource m K F
          (highSectorProject m (auxiliaryResolvent (m+1) e p he g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier))
          (fun k => (fiberFormFactor g k : ℂ)) (regularSource_local_formFactor_memLp g K hK R hKR)))) := by
  apply localCutoffInverseField_tendsto_varying
  exact regularSource_local_source_tendsto m e p hm he g hg hs K hK R hKR F hF

end Froehlich
