import Froehlich.Nodes.UV01SourceLoads
import Froehlich.Nodes.RS02SourceTransport

/-! The actual sources in fixed graph coordinates are independent of the
moving momentum. No cutoff ground energy or auxiliary source is introduced. -/
noncomputable section
namespace Froehlich

theorem cutoffFiberSourceLoad_coordinateChange (g Λ : ℝ) (P Q : GW.Space) (u : EnergySpace Q) :
    cutoffFiberSourceLoad g P Λ (energyCoordinateChange P Q u) = cutoffFiberSourceLoad g Q Λ u := by
  change fockWeightedSourceLoad P _ _ (energyCoordinateChange P Q u) = fockWeightedSourceLoad Q _ _ u
  rw [fockWeightedSourceLoad_integral,fockWeightedSourceLoad_integral,energyCoordinateChange_intertwines]

theorem cutoffCommonSourceLoad_eq (g : ℝ) (p0 p : GW.Space) (n : ℕ) (Λ : ℝ) :
    cutoffCommonSourceLoad g p0 p n Λ = cutoffHighFiberSourceLoad g (-p0) n Λ := by
  apply ContinuousLinearMap.ext
  intro u
  change cutoffFiberSourceLoad g (-p) Λ
    (energyCoordinateChange (-p) (-p0) (u : EnergySpace (-p0))) = cutoffFiberSourceLoad g (-p0) Λ u
  exact cutoffFiberSourceLoad_coordinateChange g Λ (-p) (-p0) u

theorem singularCommonSourceLoad_eq (g : ℝ) (p0 p : GW.Space) (n : ℕ) :
    singularCommonSourceLoad g p0 p n = singularHighFiberSourceLoad g (-p0) n := by
  apply ContinuousLinearMap.ext
  intro u
  change fiberSourceLoad g (-p)
    (energyCoordinateChange (-p) (-p0) (u : EnergySpace (-p0))) = fiberSourceLoad g (-p0) u
  exact fiberSourceLoad_coordinateChange g (-p) (-p0) u

theorem cutoffCommonSourceLoad_reference_error (g Λ : ℝ) (p0 p : GW.Space) (n : ℕ)
    (hΛ : max 1 (2*‖p0‖) ≤ Λ) :
    ‖cutoffCommonSourceLoad g p0 p n Λ - singularCommonSourceLoad g p0 p n‖ ≤
      Real.sqrt (56*GW.Model.unitBallVolume)*|g|/Real.sqrt Λ := by
  rw [cutoffCommonSourceLoad_eq,singularCommonSourceLoad_eq]
  exact cutoffHighFiberSourceLoad_error g ‖p0‖ Λ (-p0) n (by simp only [norm_neg]; exact le_rfl) hΛ

end Froehlich
