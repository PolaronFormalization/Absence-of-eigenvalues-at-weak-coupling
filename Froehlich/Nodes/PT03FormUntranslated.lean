import Froehlich.Nodes.PT03FormThreshold
import Froehlich.Nodes.PT03FormSingularKernel
import Froehlich.Nodes.PT03FormVacuumProduct
import Froehlich.Nodes.PT03BoundsFullDiagonal
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-! Assembly on the actual unshifted one-particle form domain. The vacuum
term and the proved high-sector correction give precisely C=d⁻¹−J. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem vacuum_sub_kernelJ_integral (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4) (f h : OneParticleEnergySpace P) :
    (((1+e-‖P‖^2)⁻¹ : ℝ) : ℂ)*⟪f,onePhononSourceOperator g P h⟫_ℂ -
      (∫ x : GW.Space × GW.Space, thresholdJProduct e he g hg hs P f h x ∂volume.prod volume) =
    ∫ x : GW.Space × GW.Space,
      (starRingEnd ℂ) (oneParticleEnergyEmbedding P f x.1)*(fiberFormFactor g x.1 : ℂ)*
        thresholdKernelC e he g hg hs P (x.1-P) (x.2-P)*(fiberFormFactor g x.2 : ℂ)*
          oneParticleEnergyEmbedding P h x.2 ∂volume.prod volume := by
  let c : ℂ := (((1+e-‖P‖^2)⁻¹ : ℝ) : ℂ)
  have hV := onePhononSourceOperator_product_integral g P f h
  have hJ := thresholdKernelJ_form_integrable e he g hg hs P hP f h
  simp only [thresholdJProduct]
  rw [hV.2,←integral_const_mul,←integral_sub (hV.1.const_mul c) hJ]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only [thresholdKernelC,c]
    ring

theorem untranslatedThresholdForm_kernel_formula (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)
    (f h : OneParticleEnergySpace P) :
    untranslatedThresholdForm e he g hquarter heLower hquadratic P hP f h =
      (∫ k : GW.Space, (starRingEnd ℂ) (oneParticleEnergyEmbedding P f k)*
        ((‖k-P‖^2+auxiliarySelfEnergy e (k-P) he g hg hs-e : ℝ) : ℂ)*oneParticleEnergyEmbedding P h k) +
      ∫ x : GW.Space × GW.Space,
        (starRingEnd ℂ) (oneParticleEnergyEmbedding P f x.1)*(fiberFormFactor g x.1 : ℂ)*
          thresholdKernelC e he g hg hs P (x.1-P) (x.2-P)*(fiberFormFactor g x.2 : ℂ)*
            oneParticleEnergyEmbedding P h x.2 ∂volume.prod volume := by
  have hFull := (thresholdFullDiagonal_integrable_and_combine e he g hg hs P f h).2
  have hC := vacuum_sub_kernelJ_integral e he g hg hs P hP f h
  rw [untranslatedThresholdForm_components,
    (oneParticle_threshold_free_integral e P f h).2,
    thresholdCorrection_kernel_formula e he g hg hs P hP hquarter heLower hquadratic f h]
  linear_combination hFull+hC

end Froehlich
