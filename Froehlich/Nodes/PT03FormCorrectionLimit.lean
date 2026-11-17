import Froehlich.Nodes.PT03FormCorrectionPhysical
import Froehlich.Nodes.CV01SchurCorrections

/-! The cutoff correction converges in genuine operator/form norm on a
fixed one-particle graph. Its physical inputs are preserved by the actual
momentum graph coordinate change. -/
noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace Froehlich
attribute [local irreducible] cutoffEnergySchurCorrection singularEnergySchurCorrection
  oneParticleEnergyCoordinateChange

variable (e : ℝ) (P0 P : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem cutoffCommonSchurCorrection_creation_pairing (Λ : GW.Operators.PositiveCutoff)
    (f h : OneParticleEnergySpace P0) :
    ⟪f,cutoffCommonSchurCorrection e P0 P he g hg hs Λ h⟫_ℂ =
      ⟪(oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) (oneParticleEnergyEmbedding P0 f) : GW.Fock.Carrier),
        cutoffAuxiliaryX e he Λ g hg hs P
          (oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) (oneParticleEnergyEmbedding P0 h) : GW.Fock.Carrier)⟫_ℂ := by
  rw [cutoffCommonSchurCorrection_spec,cutoffEnergySchurCorrection_creation_pairing,
    oneParticleEnergyCoordinateChange_physical,oneParticleEnergyCoordinateChange_physical]

theorem singularCommonSchurCorrection_pairing (f h : OneParticleEnergySpace P0) :
    ⟪f,singularCommonSchurCorrection e P0 P he g hg hs h⟫_ℂ =
      ⟪oneParticleEnergyCoordinateChange P P0 f,
        singularEnergySchurCorrection e P he g hg hs (oneParticleEnergyCoordinateChange P P0 h)⟫_ℂ := by
  unfold singularCommonSchurCorrection energyCorrectionPullback
  exact (oneParticleEnergyCoordinateChange P P0).adjoint_inner_right f
    (singularEnergySchurCorrection e P he g hg hs (oneParticleEnergyCoordinateChange P P0 h))

theorem cutoffCommonSchurCorrection_tendsto :
    Tendsto (cutoffCommonSchurCorrection e P0 P he g hg hs) atTop
      (𝓝 (singularCommonSchurCorrection e P0 P he g hg hs)) := by
  have h := commonSchurCorrection_uniform_on_ball e P0 he g hg hs ‖P-P0‖ (norm_nonneg _)
  exact h.tendsto_at (show P ∈ {Q : GW.Space | ‖Q-P0‖ ≤ ‖P-P0‖} from by
    change ‖P-P0‖ ≤ ‖P-P0‖
    exact le_rfl)

theorem cutoffEnergySchurCorrection_pairing_tendsto (f h : OneParticleEnergySpace P) :
    Tendsto (fun Λ : GW.Operators.PositiveCutoff => ⟪f,cutoffEnergySchurCorrection e P he g hg hs Λ h⟫_ℂ)
      atTop (𝓝 ⟪f,singularEnergySchurCorrection e P he g hg hs h⟫_ℂ) := by
  let L : (OneParticleEnergySpace P →L[ℂ] OneParticleEnergySpace P) →L[ℂ] ℂ :=
    (innerSL ℂ f).comp (ContinuousLinearMap.apply ℂ (OneParticleEnergySpace P) h)
  exact (L.continuous.tendsto (singularEnergySchurCorrection e P he g hg hs)).comp
    (cutoffEnergySchurCorrection_tendsto e P he g hg hs)

end Froehlich
