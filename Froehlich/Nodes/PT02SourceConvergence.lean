import Froehlich.Nodes.PT02CutoffIdentity
import Froehlich.Nodes.UV01Annihilation
import Froehlich.Nodes.UV01SourceAnchors

/-! Convergence of the singular form-source solutions themselves, in their
actual energy/number and annihilation norms. The load is not a regular Fock input. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace Froehlich
variable (e : ℝ) (p : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

def groundSourceNumber : NumberFormSpace :=
  energyNumberCoordinates (-p) (auxiliaryGroundSourceEnergy e p he g hg hs : EnergySpace (-p))

theorem cutoffGroundSourceEnergy_tendsto :
    Tendsto (cutoffGroundSourceEnergy e p he g hg hs) atTop
      (𝓝 (auxiliaryGroundSourceEnergy e p he g hg hs)) := by
  let B := highEnergyCoordinateChange (-p) (-(0 : GW.Space)) 1
  have h := (B.continuous.tendsto (singularCommonSourceSolution 1 e 0 p (by norm_num) he g hg hs)).comp
    (cutoffCommonSourceSolution_tendsto 1 e 0 p (by norm_num) he g hg hs)
  have hcut (Λ : GW.Operators.PositiveCutoff) :
      B (cutoffCommonSourceSolution 1 e 0 p (by norm_num) he g hg hs Λ) =
        cutoffGroundSourceEnergy e p he g hg hs Λ := by
    rw [cutoffCommonGroundSourceSolution_eq]
    simpa only [B] using highEnergyCoordinateChange_cancel (-p) (-(0 : GW.Space)) 1
      (cutoffGroundSourceEnergy e p he g hg hs Λ)
  have hsing : B (singularCommonSourceSolution 1 e 0 p (by norm_num) he g hg hs) =
      auxiliaryGroundSourceEnergy e p he g hg hs := by
    rw [singularCommonGroundSourceSolution_eq]
    simpa only [B] using highEnergyCoordinateChange_cancel (-p) (-(0 : GW.Space)) 1
      (auxiliaryGroundSourceEnergy e p he g hg hs)
  simpa only [Function.comp_def,hcut,hsing] using h

theorem cutoffGroundSourceNumber_tendsto :
    Tendsto (cutoffGroundSourceNumber e p he g hg hs) atTop
      (𝓝 (groundSourceNumber e p he g hg hs)) := by
  let N : HighEnergySpace (-p) 1 →L[ℂ] NumberFormSpace :=
    (energyNumberCoordinates (-p)).comp (HighEnergySpace (-p) 1).subtypeL
  exact (N.continuous.tendsto (auxiliaryGroundSourceEnergy e p he g hg hs)).comp
    (cutoffGroundSourceEnergy_tendsto e p he g hg hs)

theorem cutoffGroundSourceAnnihilation_tendsto :
    Tendsto (fun Λ => annihilationField (cutoffGroundSourceNumber e p he g hg hs Λ)) atTop
      (𝓝 (annihilationField (groundSourceNumber e p he g hg hs))) :=
  (annihilationField.continuous.tendsto (groundSourceNumber e p he g hg hs)).comp
    (cutoffGroundSourceNumber_tendsto e p he g hg hs)

theorem cutoffGroundSourceVector_tendsto :
    Tendsto (fun Λ => energyEmbedding (-p)
      (cutoffGroundSourceEnergy e p he g hg hs Λ : EnergySpace (-p))) atTop
      (𝓝 (auxiliaryGroundSourceVector e p he g hg hs)) := by
  let J : HighEnergySpace (-p) 1 →L[ℂ] GW.Fock.Carrier :=
    (energyEmbedding (-p)).comp (HighEnergySpace (-p) 1).subtypeL
  exact (J.continuous.tendsto (auxiliaryGroundSourceEnergy e p he g hg hs)).comp
    (cutoffGroundSourceEnergy_tendsto e p he g hg hs)

end Froehlich
