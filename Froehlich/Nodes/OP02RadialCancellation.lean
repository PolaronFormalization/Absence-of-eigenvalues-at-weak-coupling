import Froehlich.Nodes.OP02RadialMap
import Froehlich.Nodes.OP01KernelSymbols
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

theorem wDensity_radial_cancel (P q : GW.Space) (hq : q ≠ 0) :
    wDensity P q*‖q‖ = ‖q+P‖⁻¹ := by
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  unfold wDensity
  rw [one_div,mul_inv_rev,mul_assoc,inv_mul_cancel₀ hn,mul_one]

theorem wDensity_radial_cancel_complex (P q : GW.Space) (hq : q ≠ 0) :
    (wDensity P q : ℂ)*(‖q‖ : ℂ) = ((‖q+P‖⁻¹ : ℝ) : ℂ) := by
  rw [←Complex.ofReal_mul,wDensity_radial_cancel P q hq]

theorem thresholdSource_radial_pairing (g : ℝ) (P q : GW.Space) (hq : q ≠ 0) (z : ℂ) :
    (starRingEnd ℂ) (thresholdSource g P q)*((‖q‖ : ℂ)*z) = (fiberFormFactor g (q+P) : ℂ)*z := by
  simp only [thresholdSource,map_mul,Complex.conj_ofReal]
  calc
    _ = (g : ℂ)*((wDensity P q : ℂ)*(‖q‖ : ℂ))*z := by ring
    _ = _ := by
      rw [wDensity_radial_cancel_complex P q hq]
      simp only [fiberFormFactor,Complex.ofReal_div,Complex.ofReal_inv,Complex.ofReal_mul,div_eq_mul_inv]

def translatedHilbertSource (g : ℝ) (P : GW.Space) (hP : P ≠ 0) : GW.OnePhonon :=
  (thresholdSource_memLp g P hP).toLp (thresholdSource g P)

theorem translatedHilbertSource_ae (g : ℝ) (P : GW.Space) (hP : P ≠ 0) :
    translatedHilbertSource g P hP =ᵐ[volume] thresholdSource g P := MemLp.coeFn_toLp _

/-- All energy-space inputs are allowed. The L2 source is asserted ONLY
at nonzero P, and the sole radial cancellation excludes the null point q=0. -/
theorem translatedLinearSource_eq_hilbert_radial (g : ℝ) (P : GW.Space) (hP : P ≠ 0)
    (f : OneParticleEnergySpace 0) :
    translatedLinearSource g P f = ⟪translatedHilbertSource g P hP,oneParticleRadialMap f⟫_ℂ := by
  rw [translatedLinearSource_integral,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [translatedHilbertSource_ae g P hP,oneParticleRadialMap_ae f,
    (volume : Measure GW.Space).ae_ne 0] with q ht hu hq
  rw [ht,hu,RCLike.inner_apply']
  have h := thresholdSource_radial_pairing g P q hq (oneParticleEnergyEmbedding 0 f q)
  linear_combination -h

end Froehlich
