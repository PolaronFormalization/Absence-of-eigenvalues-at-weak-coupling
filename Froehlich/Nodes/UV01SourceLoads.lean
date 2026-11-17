import Froehlich.Nodes.UV01CommonEnergy
import Froehlich.Nodes.LD01

/-! The literal cutoff form source, restricted to the original high domain.
The reference-graph load is its pullback by the physical identity map. -/
noncomputable section
namespace Froehlich

def cutoffHighFiberSourceLoad (g : ℝ) (P : GW.Space) (n : ℕ) (Λ : ℝ) :
    ConjugateLoad (HighEnergySpace P n) :=
  (cutoffFiberSourceLoad g P Λ).comp (HighEnergySpace P n).subtypeL

def singularHighFiberSourceLoad (g : ℝ) (P : GW.Space) (n : ℕ) :
    ConjugateLoad (HighEnergySpace P n) :=
  (fiberSourceLoad g P).comp (HighEnergySpace P n).subtypeL

theorem cutoffHighFiberSourceLoad_error (g R Λ : ℝ) (P : GW.Space) (n : ℕ)
    (hP : ‖P‖ ≤ R) (hΛ : max 1 (2*R) ≤ Λ) :
    ‖cutoffHighFiberSourceLoad g P n Λ - singularHighFiberSourceLoad g P n‖ ≤
      Real.sqrt (56*GW.Model.unitBallVolume)*|g|/Real.sqrt Λ := by
  have hrestrict : ‖cutoffHighFiberSourceLoad g P n Λ - singularHighFiberSourceLoad g P n‖ ≤
      ‖cutoffFiberSourceLoad g P Λ - fiberSourceLoad g P‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    change ‖(cutoffFiberSourceLoad g P Λ - fiberSourceLoad g P) (u : EnergySpace P)‖ ≤ _
    exact (cutoffFiberSourceLoad g P Λ - fiberSourceLoad g P).le_opNorm u
  exact hrestrict.trans (cutoffFiberSourceLoad_error g R Λ P hP hΛ)

def cutoffCommonSourceLoad (g : ℝ) (p0 p : GW.Space) (n : ℕ) (Λ : ℝ) :
    ConjugateLoad (HighEnergySpace (-p0) n) :=
  (cutoffHighFiberSourceLoad g (-p) n Λ).comp (highEnergyCoordinateChange (-p) (-p0) n)

def singularCommonSourceLoad (g : ℝ) (p0 p : GW.Space) (n : ℕ) :
    ConjugateLoad (HighEnergySpace (-p0) n) :=
  (singularHighFiberSourceLoad g (-p) n).comp (highEnergyCoordinateChange (-p) (-p0) n)

theorem cutoffCommonSourceLoad_error (g R Λ : ℝ) (p0 p : GW.Space) (n : ℕ)
    (hp : ‖p‖ ≤ R) (hΛ : max 1 (2*R) ≤ Λ) :
    ‖cutoffCommonSourceLoad g p0 p n Λ - singularCommonSourceLoad g p0 p n‖ ≤
      (Real.sqrt (56*GW.Model.unitBallVolume)*|g|/Real.sqrt Λ) *
        momentumChangeConstant (-p) (-p0) := by
  let D := cutoffHighFiberSourceLoad g (-p) n Λ - singularHighFiberSourceLoad g (-p) n
  let B := highEnergyCoordinateChange (-p) (-p0) n
  have hid : cutoffCommonSourceLoad g p0 p n Λ - singularCommonSourceLoad g p0 p n = D.comp B := by
    apply ContinuousLinearMap.ext
    intro u
    rfl
  rw [hid]
  calc
    _ ≤ ‖D‖*‖B‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (Real.sqrt (56*GW.Model.unitBallVolume)*|g|/Real.sqrt Λ)*‖B‖ :=
      mul_le_mul_of_nonneg_right (cutoffHighFiberSourceLoad_error g R Λ (-p) n
        (by simpa only [norm_neg] using hp) hΛ) (norm_nonneg B)
    _ ≤ _ := mul_le_mul_of_nonneg_left (highEnergyCoordinateChange_norm_le (-p) (-p0) n)
      (by positivity)

end Froehlich
