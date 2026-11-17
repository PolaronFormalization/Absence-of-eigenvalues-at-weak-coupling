import Froehlich.Nodes.FB02Vacuum
import Froehlich.Nodes.FC07CutoffAction

/-! The exact singular vacuum column is the previously constructed
conjugate-dual source, obtained only after cutoff limits. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace Topology
namespace Froehlich

theorem cutoffFiberSourceLoad_eq_inner (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space) (w : EnergySpace P) :
    cutoffFiberSourceLoad g P Λ w =
      ⟪oneParticleExtraction (energyEmbedding P w),cutoffFormFactorL2 g Λ hΛ⟫_ℂ := by
  change fockWeightedSourceLoad P (fun k => (cutoffFormFactor g Λ k : ℂ))
    (cutoffFiberSource_quotient_memLp g Λ P) w = _
  rw [fockWeightedSourceLoad_integral,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cutoffFormFactorL2_ae g Λ hΛ] with k hk
  rw [RCLike.inner_apply',hk]

theorem cutoffInteraction_vacuum_column (g : ℝ) (P : GW.Space)
    (Λ : GW.Operators.PositiveCutoff) (w : EnergySpace P) :
    cutoffInteractionForm g Λ.val Λ.property P w (vacuumEnergyLift P) = cutoffFiberSourceLoad g P Λ.val w := by
  change cutoffInteractionForm g Λ.val Λ.property P w (coreEnergyLift P vacuumCore) = _
  rw [cutoffInteractionForm_core_second,fieldRestriction_vacuum]
  have hi : ⟪energyEmbedding P w,oneParticleInclusion (cutoffFormFactorL2 g Λ.val Λ.property)⟫_ℂ =
      ⟪oneParticleExtraction (energyEmbedding P w),cutoffFormFactorL2 g Λ.val Λ.property⟫_ℂ := by
    simpa only [Complex.star_def,inner_conj_symm] using congrArg (starRingEnd ℂ)
      (oneParticleInclusion_pairing (cutoffFormFactorL2 g Λ.val Λ.property) (energyEmbedding P w))
  exact hi.trans (cutoffFiberSourceLoad_eq_inner g Λ.val Λ.property P w).symm

theorem positiveCutoff_coe_tendsto :
    Tendsto (fun Λ : GW.Operators.PositiveCutoff => (Λ : ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro R
  refine eventually_atTop.mpr ⟨⟨max R 1,zero_lt_one.trans_le (le_max_right _ _)⟩,?_⟩
  intro Λ hΛ
  change max R 1 ≤ Λ.val at hΛ
  exact (le_max_left R 1).trans hΛ

theorem singularInteraction_vacuum_column (g : ℝ) (P : GW.Space) (w : EnergySpace P) :
    singularInteraction g P w (vacuumEnergyLift P) = fiberSourceLoad g P w := by
  have hf := boundedForm_eval_tendsto (cutoffInteraction_tendsto g P) w (vacuumEnergyLift P)
  have hl : Tendsto (fun Λ : ℝ => cutoffFiberSourceLoad g P Λ w) atTop
      (𝓝 (fiberSourceLoad g P w)) :=
    ((ContinuousLinearMap.apply' ℂ (starRingEnd ℂ) w).continuous.tendsto (fiberSourceLoad g P)).comp
      (cutoffFiberSourceLoad_tendsto g P)
  have he : (fun Λ : GW.Operators.PositiveCutoff =>
      cutoffInteractionForm g Λ.val Λ.property P w (vacuumEnergyLift P)) =
      (fun Λ : GW.Operators.PositiveCutoff => cutoffFiberSourceLoad g P Λ.val w) :=
    funext (fun Λ => cutoffInteraction_vacuum_column g P Λ w)
  rw [he] at hf
  exact tendsto_nhds_unique hf (hl.comp positiveCutoff_coe_tendsto)

end Froehlich
