import Froehlich.Nodes.PT01CutoffPullthrough

/-! The finite-cutoff pull-through identity has one global almost-everywhere
set for each fixed p and Lambda. Only the annihilated variable is exhausted. -/
noncomputable section
open MeasureTheory
namespace Froehlich
variable (m : ℕ) (e : ℝ) (p : GW.Space) (hm : m+1 ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (Lambda : GW.Operators.PositiveCutoff)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (F : NumberFormSpace) (hF : numberFormEmbedding F ∈ HighSectorSpace (m+1))

def cutoffRegularSourceRow (k : GW.Space) : HighSectorSpace m :=
  highSectorProject m (annihilationField F k) - (cutoffFormFactor g Lambda.val k : ℂ) •
    cutoffPullthroughVector m e p he Lambda g hg hs ⟨numberFormEmbedding F,hF⟩

def cutoffRegularSourceRHSRow (k : GW.Space) : GW.Fock.Carrier :=
  (cutoffAuxiliaryResolvent m e (p+k) he Lambda g hg hs
    (cutoffRegularSourceRow m e p he Lambda g hg hs F hF k) : GW.Fock.Carrier)

theorem cutoffRegularSourceRow_physical_ae :
    ∀ᵐ k ∂volume, (cutoffRegularSourceRow m e p he Lambda g hg hs F hF k : GW.Fock.Carrier)=
      annihilationField F k-(cutoffFormFactor g Lambda.val k : ℂ) •
        (cutoffAuxiliaryResolvent (m+1) e p he Lambda g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier) := by
  filter_upwards [annihilationField_mem_high_of_number_high m F hF] with k hk
  change highSectorProjection m (annihilationField F k)-(cutoffFormFactor g Lambda.val k : ℂ) •
    (cutoffAuxiliaryResolvent (m+1) e p he Lambda g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier)=_
  rw [(highSector_mem_iff m _).mp hk]

include hm in
theorem localCutoffInverseField_cutoff_row_ae (K : Set GW.Space) (hK : MeasurableSet K) :
    (HighSectorSpace m).subtypeL.compLp
      (localCutoffInverseField m e p ((Nat.le_succ m).trans hm) he g hg hs K hK Lambda
        (cutoffPullthroughSource m e p he Lambda g hg hs K F hF)) =ᵐ[volume.restrict K]
      cutoffRegularSourceRHSRow m e p he Lambda g hg hs F hF := by
  let U := cutoffPullthroughVector m e p he Lambda g hg hs ⟨numberFormEmbedding F,hF⟩
  let S := cutoffPullthroughSource m e p he Lambda g hg hs K F hF
  have hinput : S =ᵐ[volume.restrict K] cutoffRegularSourceRow m e p he Lambda g hg hs F hF := by
    have hphysical := localPullthroughSource_physical m K F hF U
      (fun k => cutoffFormFactorL2 g Lambda.val Lambda.property k)
      ((Lp.memLp (cutoffFormFactorL2 g Lambda.val Lambda.property)).restrict K)
    filter_upwards [hphysical,
      ae_restrict_of_ae (s := K) (cutoffFormFactorL2_ae g Lambda.val Lambda.property),
      ae_restrict_of_ae (s := K) (cutoffRegularSourceRow_physical_ae m e p he Lambda g hg hs F hF)]
      with k hsource hcut hrow
    apply Subtype.ext
    change (S k : GW.Fock.Carrier)=_
    change (S k : GW.Fock.Carrier)=annihilationField F k-cutoffFormFactorL2 g Lambda.val Lambda.property k •
      (cutoffAuxiliaryResolvent (m+1) e p he Lambda g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier) at hsource
    rw [hcut] at hsource
    exact hsource.trans hrow.symm
  let A := localCutoffInverseField m e p ((Nat.le_succ m).trans hm) he g hg hs K hK Lambda S
  filter_upwards [(HighSectorSpace m).subtypeL.coeFn_compLp A,
    localCutoffInverseField_ae m e p ((Nat.le_succ m).trans hm) he g hg hs K hK Lambda S,hinput]
    with k hi ha hsrow
  change (HighSectorSpace m).subtypeL.compLp A k=_
  rw [hi,ha,hsrow]
  rfl

include hm in
theorem cutoffPullthrough_global :
    ∀ᵐ k ∂volume,
      annihilationField (freeGraphNumberCoordinates (-p)
        (cutoffAuxiliaryGraphCoordinate (m+1) e p hm he Lambda g hg hs ⟨numberFormEmbedding F,hF⟩)) k=
      cutoffRegularSourceRHSRow m e p he Lambda g hg hs F hF k := by
  let A := annihilationField (freeGraphNumberCoordinates (-p)
    (cutoffAuxiliaryGraphCoordinate (m+1) e p hm he Lambda g hg hs ⟨numberFormEmbedding F,hF⟩))
  have hball (N : ℕ) : ∀ᵐ k ∂volume, k ∈ Metric.closedBall (0 : GW.Space) (N : ℝ) →
      A k=cutoffRegularSourceRHSRow m e p he Lambda g hg hs F hF k := by
    let K := Metric.closedBall (0 : GW.Space) (N : ℝ)
    have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
    have hR : ∀ k ∈ K, ‖k‖ ≤ (N : ℝ) := by
      intro k hk
      simpa only [K,Metric.mem_closedBall,dist_zero_right] using hk
    have hlocal := cutoffPullthrough_local m e p hm he Lambda g hg hs K hK N (Nat.cast_nonneg N) hR F hF
    have hrow := localCutoffInverseField_cutoff_row_ae m e p hm he Lambda g hg hs F hF K hK
    have hleft := LpToLpRestrictCLM_coeFn ℂ K A
    have hEq : ∀ᵐ k ∂volume.restrict K, A k=cutoffRegularSourceRHSRow m e p he Lambda g hg hs F hF k := by
      filter_upwards [hleft,hrow] with k hl hr
      rw [hlocal] at hl
      exact hl.symm.trans hr
    exact (ae_restrict_iff' hK).mp hEq
  filter_upwards [ae_all_iff.mpr hball] with k hk
  obtain ⟨N,hN⟩ := exists_nat_ge ‖k‖
  apply hk N
  simpa only [Metric.mem_closedBall,dist_zero_right] using hN

include hm in
theorem cutoffPullthrough_global_source_domain :
    ∀ᵐ k ∂volume, ∃ q : HighSectorSpace m,
      (q : GW.Fock.Carrier)=annihilationField F k-(cutoffFormFactor g Lambda.val k : ℂ) •
        (cutoffAuxiliaryResolvent (m+1) e p he Lambda g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier) ∧
      annihilationField (freeGraphNumberCoordinates (-p)
        (cutoffAuxiliaryGraphCoordinate (m+1) e p hm he Lambda g hg hs ⟨numberFormEmbedding F,hF⟩)) k=
        (cutoffAuxiliaryResolvent m e (p+k) he Lambda g hg hs q : GW.Fock.Carrier) := by
  filter_upwards [cutoffPullthrough_global m e p hm he Lambda g hg hs F hF,
    cutoffRegularSourceRow_physical_ae m e p he Lambda g hg hs F hF] with k hpt hrow
  exact ⟨cutoffRegularSourceRow m e p he Lambda g hg hs F hF k,hrow,hpt⟩

end Froehlich
