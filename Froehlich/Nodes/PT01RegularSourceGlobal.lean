import Froehlich.Nodes.PT01RegularSourceRows
import Froehlich.Nodes.PT01CoreLocalLimitJoin

set_option autoImplicit false

/-! A single global almost-everywhere identity for each fixed momentum.
Only a countable exhaustion in the annihilated variable is used. -/
noncomputable section
open MeasureTheory
namespace Froehlich

variable (m : ℕ) (e : ℝ) (p : GW.Space) (hm : m+1 ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (F : NumberFormSpace)
    (hF : numberFormEmbedding F ∈ HighSectorSpace (m+1))

theorem uncutPullthrough_global :
    ∀ᵐ k ∂volume,
      annihilationField (ptRegularSingularNumberVector (m+1) e p hm he g hg hs ⟨numberFormEmbedding F,hF⟩) k =
        regularSourceRHSRow m e p he g hg hs F hF k := by
  let A := annihilationField
    (ptRegularSingularNumberVector (m+1) e p hm he g hg hs ⟨numberFormEmbedding F,hF⟩)
  have hball (N : ℕ) : ∀ᵐ k ∂volume,
      k ∈ Metric.closedBall (0 : GW.Space) (N : ℝ) → A k = regularSourceRHSRow m e p he g hg hs F hF k := by
    let K := Metric.closedBall (0 : GW.Space) (N : ℝ)
    have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
    have hR : ∀ k ∈ K, ‖k‖ ≤ (N : ℝ) := by
      intro k hk
      simpa only [K,Metric.mem_closedBall,dist_zero_right] using hk
    have hlocal := uncutPullthrough_local m e p hm he g hg hs K hK N (Nat.cast_nonneg N) hR F hF
    have hrow := localSingularInverseField_global_row_ae m e p he g hg hs F hF hm K hK
      (ptCoreLocal_isBounded K N hR) N hR
    have hleft := LpToLpRestrictCLM_coeFn ℂ K A
    have hEq : ∀ᵐ k ∂volume.restrict K, A k = regularSourceRHSRow m e p he g hg hs F hF k := by
      filter_upwards [hleft,hrow] with k hl hr
      rw [hlocal] at hl
      exact hl.symm.trans hr
    exact (ae_restrict_iff' hK).mp hEq
  filter_upwards [ae_all_iff.mpr hball] with k hk
  obtain ⟨N,hN⟩ := exists_nat_ge ‖k‖
  apply hk N
  simpa only [Metric.mem_closedBall,dist_zero_right] using hN

theorem uncutPullthrough_global_source_domain :
    ∀ᵐ k ∂volume, ∃ q : HighSectorSpace m,
      (q : GW.Fock.Carrier) = annihilationField F k - (fiberFormFactor g k : ℂ) •
        (auxiliaryResolvent (m+1) e p he g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier) ∧
      annihilationField (ptRegularSingularNumberVector (m+1) e p hm he g hg hs ⟨numberFormEmbedding F,hF⟩) k =
        (auxiliaryResolvent m e (p+k) he g hg hs q : GW.Fock.Carrier) := by
  filter_upwards [uncutPullthrough_global m e p hm he g hg hs F hF,
    regularSourceRow_physical_ae m e p he g hg hs F hF] with k hpt hrow
  exact ⟨regularSourceRow m e p he g hg hs F hF k,hrow,hpt⟩

end Froehlich
