import Froehlich.Nodes.PT03FormCorrectionLimit
import Froehlich.Nodes.PT03FormCorrectionSingular

/-! The cutoff correction limit is the actual SP03 threshold correction,
including its genuine pullback to a fixed one-particle form carrier. -/
noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace Froehlich
variable (e : ℝ) (P0 P : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)
  (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant * |g|^2 ≤ e)
  (hquadratic : sectorQuadraticConstant * |g|^2 ≤ 1/8)

theorem singularCommonSchurCorrection_eq_threshold :
    singularCommonSchurCorrection e P0 P he g hg hs =
      energyCorrectionPullback (E := OneParticleEnergySpace P0) (H := OneParticleEnergySpace P)
        (oneParticleEnergyCoordinateChange P P0)
        (onePhononHighCorrection g e 0 P hquarter heLower he.2 (by norm_num) hquadratic) := by
  unfold singularCommonSchurCorrection
  rw [singularEnergySchurCorrection_eq_threshold e P he g hg hs hquarter heLower hquadratic]

theorem cutoffCommonSchurCorrection_tendsto_threshold :
    Tendsto (cutoffCommonSchurCorrection e P0 P he g hg hs) atTop
      (𝓝 (energyCorrectionPullback (E := OneParticleEnergySpace P0) (H := OneParticleEnergySpace P)
        (oneParticleEnergyCoordinateChange P P0)
        (onePhononHighCorrection g e 0 P hquarter heLower he.2 (by norm_num) hquadratic))) := by
  have h := cutoffCommonSchurCorrection_tendsto e P0 P he g hg hs
  rw [singularCommonSchurCorrection_eq_threshold e P0 P he g hg hs hquarter heLower hquadratic] at h
  exact h

theorem cutoffEnergySchurCorrection_pairing_tendsto_threshold (f h : OneParticleEnergySpace P) :
    Tendsto (fun Λ : GW.Operators.PositiveCutoff => ⟪f,cutoffEnergySchurCorrection e P he g hg hs Λ h⟫_ℂ)
      atTop (𝓝 ⟪f,onePhononHighCorrection g e 0 P hquarter heLower he.2 (by norm_num) hquadratic h⟫_ℂ) := by
  have hlim := cutoffEnergySchurCorrection_pairing_tendsto e P he g hg hs f h
  rw [singularEnergySchurCorrection_eq_threshold e P he g hg hs hquarter heLower hquadratic] at hlim
  exact hlim

end Froehlich
