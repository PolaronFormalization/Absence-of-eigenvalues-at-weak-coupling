import Froehlich.Nodes.FB02A
import Froehlich.Nodes.FB01Linearity

/-! Zero coupling for the actual cutoff and singular forms. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich

theorem cutoffFormFactorL2_zero_coupling (Λ : ℝ) (hΛ : 0 < Λ) : cutoffFormFactorL2 0 Λ hΛ = 0 := by
  apply norm_eq_zero.mp
  have h : ‖cutoffFormFactorL2 0 Λ hΛ‖^2 ≤ 0 := by
    simpa using cutoffFormFactorL2_norm_sq 0 Λ hΛ
  nlinarith [norm_nonneg (cutoffFormFactorL2 0 Λ hΛ)]

theorem cutoffInteraction_zero_coupling (Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space) :
    cutoffInteractionForm 0 Λ hΛ P = 0 := by
  change boundedEnergyInteraction P (cutoffFormFactorL2 0 Λ hΛ) = 0
  rw [cutoffFormFactorL2_zero_coupling, boundedEnergyInteraction_zero_factor]

theorem singularInteraction_zero_coupling (P : GW.Space) : singularInteraction 0 P = 0 := by
  have hfun : (fun Λ : GW.Operators.PositiveCutoff => cutoffInteractionForm 0 Λ.val Λ.property P) =
      (fun _ : GW.Operators.PositiveCutoff => (0 : GW.Analysis.BoundedForm (EnergySpace P))) :=
    funext (fun Λ => cutoffInteraction_zero_coupling Λ.val Λ.property P)
  have ht : Tendsto (fun Λ : GW.Operators.PositiveCutoff => cutoffInteractionForm 0 Λ.val Λ.property P)
      atTop (𝓝 (0 : GW.Analysis.BoundedForm (EnergySpace P))) := by
    rw [hfun]
    exact tendsto_const_nhds
  exact (singularInteraction_unique 0 P 0 ht).symm

end Froehlich
