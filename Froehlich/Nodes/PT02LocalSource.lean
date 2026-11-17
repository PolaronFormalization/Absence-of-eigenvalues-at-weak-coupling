import Froehlich.Nodes.PT02SourceConvergence
import Froehlich.Nodes.PT01RegularSourceLimit

/-! The PT02 right-hand source is locally L²: only its scalar coefficient
is localized. The vector factor is the actual cutoff/singular form-source solution. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Froehlich

def sourcePullthroughLocalField (K : Set GW.Space) (u : GW.Fock.Carrier)
    (v : GW.Space → ℂ) (hv : MemLp v 2 (volume.restrict K)) :
    Lp (HighSectorSpace 0) 2 (volume.restrict K) :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight (highSectorProject 0 (GW.Fock.vacuum-u))).compLp
    (hv.toLp v)

theorem sourcePullthroughLocalField_physical (K : Set GW.Space) (u : GW.Fock.Carrier)
    (v : GW.Space → ℂ) (hv : MemLp v 2 (volume.restrict K)) :
    ∀ᵐ k ∂volume.restrict K,
      (sourcePullthroughLocalField K u v hv k : GW.Fock.Carrier) = v k • (GW.Fock.vacuum-u) := by
  filter_upwards [((ContinuousLinearMap.id ℂ ℂ).smulRight
    (highSectorProject 0 (GW.Fock.vacuum-u))).coeFn_compLp (hv.toLp v),
    hv.coeFn_toLp] with k hk hvk
  change (((ContinuousLinearMap.id ℂ ℂ).smulRight
    (highSectorProject 0 (GW.Fock.vacuum-u))).compLp (hv.toLp v) k : GW.Fock.Carrier) = _
  rw [hk,hvk]
  rfl

theorem sourcePullthroughLocalField_continuous (K : Set GW.Space)
    (v : GW.Space → ℂ) (hv : MemLp v 2 (volume.restrict K)) :
    Continuous (fun u : GW.Fock.Carrier => sourcePullthroughLocalField K u v hv) := by
  let B : HighSectorSpace 0 →L[ℂ] ℂ →L[ℂ] HighSectorSpace 0 :=
    ContinuousLinearMap.smulRightL ℂ ℂ (HighSectorSpace 0) (ContinuousLinearMap.id ℂ ℂ)
  let A : HighSectorSpace 0 →L[ℂ] Lp (HighSectorSpace 0) 2 (volume.restrict K) :=
    (B.compLpL₂ 2 (volume.restrict K)).flip (hv.toLp v)
  change Continuous (fun u : GW.Fock.Carrier => A (highSectorProject 0 (GW.Fock.vacuum-u)))
  exact A.continuous.comp ((highSectorProject 0).continuous.comp (continuous_const.sub continuous_id))

theorem cutoffSourcePullthroughLocalField_tendsto (e : ℝ) (p : GW.Space)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant * |g| ≤ 1/2) (K : Set GW.Space) (hK : MeasurableSet K)
    (R : ℝ) (hKR : ∀ k ∈ K, ‖k‖ ≤ R) :
    Tendsto (fun Λ : GW.Operators.PositiveCutoff => sourcePullthroughLocalField K
      (energyEmbedding (-p) (cutoffGroundSourceEnergy e p he g hg hs Λ : EnergySpace (-p)))
      (fun k => cutoffFormFactorL2 g Λ.val Λ.property k)
      ((Lp.memLp (cutoffFormFactorL2 g Λ.val Λ.property)).restrict K)) atTop
      (𝓝 (sourcePullthroughLocalField K (auxiliaryGroundSourceVector e p he g hg hs)
        (fun k => (fiberFormFactor g k : ℂ)) (regularSource_local_formFactor_memLp g K hK R hKR))) := by
  let hv := regularSource_local_formFactor_memLp g K hK R hKR
  have hbase := (sourcePullthroughLocalField_continuous K (fun k => (fiberFormFactor g k : ℂ)) hv).tendsto _
    |>.comp (cutoffGroundSourceVector_tendsto e p he g hg hs)
  apply hbase.congr'
  have hevent : ∀ᶠ Λ : GW.Operators.PositiveCutoff in atTop, R ≤ Λ.val := by
    exact eventually_atTop.mpr ⟨⟨max R 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _)⟩,
      fun Λ hΛ => (le_max_left R 1).trans hΛ⟩
  filter_upwards [hevent] with Λ hΛ
  unfold sourcePullthroughLocalField
  rw [MemLp.toLp_congr _ hv (localCutoffFormFactor_ae g Λ K hK R hKR hΛ)]
  rfl

end Froehlich
