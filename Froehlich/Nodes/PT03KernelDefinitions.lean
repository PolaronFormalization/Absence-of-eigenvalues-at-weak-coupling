import Froehlich.Nodes.RS01AuxiliaryFields
import Froehlich.Nodes.UV01Fields

set_option autoImplicit false

/-! PT03's literal scalar kernels on the retained full Fock carrier.
These definitions make no threshold-form identity claim. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

def thresholdKernelJ (P q r : GW.Space) : ℂ :=
  ⟪GW.Fock.vacuum-auxiliaryGroundSourceVector e q he g hg hs,
    auxiliaryZ e (P+q+r) he g hg hs (GW.Fock.vacuum-auxiliaryGroundSourceVector e r he g hg hs)⟫_ℂ +
  ⟪auxiliaryGroundSourceVector e q he g hg hs,
    auxiliaryX e he g hg hs P (auxiliaryGroundSourceVector e r he g hg hs)⟫_ℂ

def thresholdKernelC (P q r : GW.Space) : ℂ :=
  (((1+e-‖P‖^2)⁻¹ : ℝ) : ℂ)-thresholdKernelJ e he g hg hs P q r

def cutoffThresholdSourceVector (Λ : GW.Operators.PositiveCutoff) (q : GW.Space) : GW.Fock.Carrier :=
  energyEmbedding (-q) (cutoffGroundSourceEnergy e q he g hg hs Λ : EnergySpace (-q))

def cutoffThresholdKernelJ (Λ : GW.Operators.PositiveCutoff) (P q r : GW.Space) : ℂ :=
  ⟪GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ q,
    cutoffAuxiliaryZ e (P+q+r) he Λ g hg hs (GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ r)⟫_ℂ +
  ⟪cutoffThresholdSourceVector e he g hg hs Λ q,
    cutoffAuxiliaryX e he Λ g hg hs P (cutoffThresholdSourceVector e he g hg hs Λ r)⟫_ℂ

def cutoffThresholdKernelC (Λ : GW.Operators.PositiveCutoff) (P q r : GW.Space) : ℂ :=
  (((1+e-‖P‖^2)⁻¹ : ℝ) : ℂ)-cutoffThresholdKernelJ e he g hg hs Λ P q r

include he in
theorem thresholdKernel_denominator_lower (P : GW.Space) (hP : ‖P‖ ≤ 1/4) :
    (11/16 : ℝ) ≤ 1+e-‖P‖^2 := by
  have hsq : ‖P‖^2 ≤ (1/4 : ℝ)^2 :=
    (sq_le_sq₀ (norm_nonneg P) (by norm_num)).mpr hP
  have he0 := he.1
  nlinarith

include he in
theorem thresholdKernel_denominator_inv_bound (P : GW.Space) (hP : ‖P‖ ≤ 1/4) :
    |(1+e-‖P‖^2)⁻¹| ≤ (16/11 : ℝ) := by
  have h := thresholdKernel_denominator_lower e he P hP
  have hd : 0 < 1+e-‖P‖^2 := (by norm_num : (0:ℝ)<11/16).trans_le h
  rw [abs_inv,abs_of_pos hd]
  have hi := (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<11/16) h)
  norm_num only [one_div,inv_div] at hi
  exact hi

end Froehlich
