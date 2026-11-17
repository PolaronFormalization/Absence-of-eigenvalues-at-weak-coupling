import Froehlich.Nodes.OP02RadialCancellation
import Froehlich.Nodes.OP01KernelSymmetries

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

theorem radialWeightedSource_factor (g : ℝ) (P q : GW.Space) (hq : q ≠ 0) :
    (g : ℂ)*(wDensity P q : ℂ)*(‖q‖ : ℂ) = (fiberFormFactor g (q+P) : ℂ) := by
  simpa only [thresholdSource,map_mul,Complex.conj_ofReal,mul_one] using
    thresholdSource_radial_pairing g P q hq (1 : ℂ)

private theorem op02_remainder_scalar (g : ℝ) (P q r : GW.Space) (hq : q ≠ 0) (hr : r ≠ 0)
    (a : ℝ) (z w : ℂ) :
    ((g^2 : ℝ) : ℂ)*((starRingEnd ℂ) ((‖q‖ : ℂ)*z)*
      (((wDensity P q : ℂ)*(a : ℂ)*(wDensity P r : ℂ))*((‖r‖ : ℂ)*w))) =
    (starRingEnd ℂ) z*(fiberFormFactor g (q+P) : ℂ)*(a : ℂ)*(fiberFormFactor g (r+P) : ℂ)*w := by
  calc
    _ = (starRingEnd ℂ) z*((g : ℂ)*(wDensity P q : ℂ)*(‖q‖ : ℂ))*(a : ℂ)*
        ((g : ℂ)*(wDensity P r : ℂ)*(‖r‖ : ℂ))*w := by
      simp only [map_mul,Complex.conj_ofReal,Complex.ofReal_pow]
      ring
    _ = _ := by rw [radialWeightedSource_factor g P q hq,radialWeightedSource_factor g P r hr]

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

theorem radialRemainder_inner_integral (f h : OneParticleEnergySpace 0) :
    Integrable (fun x : GW.Space × GW.Space =>
      (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
        (remainderKernel e he g hg hs P x.1 x.2 : ℂ)*(fiberFormFactor g (x.2+P) : ℂ)*
          oneParticleEnergyEmbedding 0 h x.2) (volume.prod volume) ∧
    ((g^2 : ℝ) : ℂ)*⟪oneParticleRadialMap f,thresholdIntegralOperator e he g hg hs P hP (oneParticleRadialMap h)⟫_ℂ =
      ∫ x : GW.Space × GW.Space,
        (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
          (remainderKernel e he g hg hs P x.1 x.2 : ℂ)*(fiberFormFactor g (x.2+P) : ℂ)*
            oneParticleEnergyEmbedding 0 h x.2 ∂volume.prod volume := by
  let a := kernelDensityMajorant P
  let ha := kernelDensityMajorant_memLp P hP
  let k := boundedThresholdKernel e he g hg hs P
  let hk := boundedThresholdKernel_measurable e he g hg hs P
  let M := integralKernelMajorantConstant
  let hb := integralKernelMajorantConstant_bound e he g hg hs P hP
  let uf := oneParticleRadialMap f
  let uh := oneParticleRadialMap h
  have hi := (kernelPairing_integrable a ha k hk M hb uf uh).const_mul ((g^2 : ℝ) : ℂ)
  have hF := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure GW.Space))
    (ν := (volume : Measure GW.Space))).ae (oneParticleRadialMap_ae f)
  have hH := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure GW.Space))
    (ν := (volume : Measure GW.Space))).ae (oneParticleRadialMap_ae h)
  have hQ := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure GW.Space))
    (ν := (volume : Measure GW.Space))).ae ((volume : Measure GW.Space).ae_ne 0)
  have hR := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure GW.Space))
    (ν := (volume : Measure GW.Space))).ae ((volume : Measure GW.Space).ae_ne 0)
  have hp : (fun x : GW.Space × GW.Space => ((g^2 : ℝ) : ℂ)*((starRingEnd ℂ) (uf x.1)*(k x.1 x.2*uh x.2))) =ᵐ[volume.prod volume]
      (fun x : GW.Space × GW.Space =>
        (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
          (remainderKernel e he g hg hs P x.1 x.2 : ℂ)*(fiberFormFactor g (x.2+P) : ℂ)*
            oneParticleEnergyEmbedding 0 h x.2) := by
    filter_upwards [hF,hH,hQ,hR] with x hf hh hq hr
    change ((g^2 : ℝ) : ℂ)*((starRingEnd ℂ) (oneParticleRadialMap f x.1)*
      (boundedThresholdKernel e he g hg hs P x.1 x.2*oneParticleRadialMap h x.2)) = _
    rw [hf,hh]
    exact op02_remainder_scalar g P x.1 x.2 hq hr (remainderKernel e he g hg hs P x.1 x.2)
      (oneParticleEnergyEmbedding 0 f x.1) (oneParticleEnergyEmbedding 0 h x.2)
  have hInner : ⟪uf,thresholdIntegralOperator e he g hg hs P hP uh⟫_ℂ =
      ∫ x : GW.Space × GW.Space,(starRingEnd ℂ) (uf x.1)*(k x.1 x.2*uh x.2) ∂volume.prod volume :=
    kernelIntegralOperator_inner a ha k hk M hb (kernelDensityMajorant_nonnegative P)
      integralKernelMajorantConstant_positive.le uf uh
  refine ⟨hi.congr hp,?_⟩
  rw [hInner]
  exact (integral_const_mul _ _).symm.trans (integral_congr_ae hp)

end Froehlich
