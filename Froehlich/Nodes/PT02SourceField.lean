import Froehlich.Nodes.PT02LocalIdentity
import Froehlich.Nodes.PT01CoreLocalLimitJoin

/-! The literal PT02 field formula on bounded sets, and one global AE set
for each fixed p, obtained by a countable exhaustion only in k. -/
noncomputable section
open MeasureTheory
namespace Froehlich
variable (e : ℝ) (p : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem groundSourceNumber_physical :
    numberFormEmbedding (groundSourceNumber e p he g hg hs) = auxiliaryGroundSourceVector e p he g hg hs :=
  energyNumberCoordinates_intertwines (-p) _

theorem groundSource_pullthrough_local_ae (K : Set GW.Space) (hK : MeasurableSet K)
    (hKb : Bornology.IsBounded K) (R : ℝ) (hKR : ∀ k ∈ K, ‖k‖ ≤ R) :
    ∀ᵐ k ∂volume.restrict K,
      annihilationField (groundSourceNumber e p he g hg hs) k =
        (fiberFormFactor g k : ℂ) • auxiliaryZ e (p+k) he g hg hs
          (GW.Fock.vacuum-auxiliaryGroundSourceVector e p he g hg hs) := by
  let S := sourcePullthroughLocalField K (auxiliaryGroundSourceVector e p he g hg hs)
    (fun k => (fiberFormFactor g k : ℂ)) (regularSource_local_formFactor_memLp g K hK R hKR)
  let T := localSingularInverseField 0 e p (by norm_num) he g hg hs K hK hKb S
  have hleft := LpToLpRestrictCLM_coeFn ℂ K (annihilationField (groundSourceNumber e p he g hg hs))
  rw [groundSource_pullthrough_local e p he g hg hs K hK hKb R hKR] at hleft
  filter_upwards [hleft,(HighSectorSpace 0).subtypeL.coeFn_compLp T,
    localSingularInverseField_ae 0 e p (by norm_num) he g hg hs K hK hKb S,
    sourcePullthroughLocalField_physical K (auxiliaryGroundSourceVector e p he g hg hs)
      (fun k => (fiberFormFactor g k : ℂ))
      (regularSource_local_formFactor_memLp g K hK R hKR)] with k hl hj ht hsource
  change (S k : GW.Fock.Carrier) = _ at hsource
  calc
    _ = ((HighSectorSpace 0).subtypeL.compLp T k : GW.Fock.Carrier) := hl.symm
    _ = (auxiliaryResolvent 0 e (p+k) he g hg hs (S k) : GW.Fock.Carrier) := by rw [hj,ht]; rfl
    _ = auxiliaryZ e (p+k) he g hg hs (S k : GW.Fock.Carrier) :=
      (auxiliaryExtendedResolvent_on_high 0 e (p+k) he g hg hs (S k)).symm
    _ = _ := by rw [hsource,map_smul]

theorem groundSource_pullthrough_global :
    ∀ᵐ k ∂volume, annihilationField (groundSourceNumber e p he g hg hs) k =
      (fiberFormFactor g k : ℂ) • auxiliaryZ e (p+k) he g hg hs
        (GW.Fock.vacuum-auxiliaryGroundSourceVector e p he g hg hs) := by
  have hball (N : ℕ) : ∀ᵐ k ∂volume,
      k ∈ Metric.closedBall (0 : GW.Space) (N : ℝ) →
      annihilationField (groundSourceNumber e p he g hg hs) k =
        (fiberFormFactor g k : ℂ) • auxiliaryZ e (p+k) he g hg hs
          (GW.Fock.vacuum-auxiliaryGroundSourceVector e p he g hg hs) := by
    let K := Metric.closedBall (0 : GW.Space) (N : ℝ)
    have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
    have hR : ∀ k ∈ K, ‖k‖ ≤ (N : ℝ) := by
      intro k hk
      simpa only [K,Metric.mem_closedBall,dist_zero_right] using hk
    exact (ae_restrict_iff' hK).mp
      (groundSource_pullthrough_local_ae e p he g hg hs K hK
        (ptCoreLocal_isBounded K N hR) N hR)
  filter_upwards [ae_all_iff.mpr hball] with k hk
  obtain ⟨N,hN⟩ := exists_nat_ge ‖k‖
  apply hk N
  simpa only [Metric.mem_closedBall,dist_zero_right] using hN

end Froehlich
