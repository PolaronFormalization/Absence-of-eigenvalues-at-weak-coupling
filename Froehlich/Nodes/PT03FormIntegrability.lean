import Froehlich.Nodes.LD01
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

/-! The singular kernel's scalar majorant is integrable on the product
space. Only weighted one-particle form inputs are used. -/
noncomputable section
open MeasureTheory
namespace Froehlich

theorem formSource_product_norm_integrable (g : ℝ) (P : GW.Space)
    (f : OneParticleEnergySpace P) :
    Integrable (fun k => ‖oneParticleEnergyEmbedding P f k‖ *
      ‖(fiberFormFactor g k : ℂ)‖) volume := by
  have h := (weightedSource_pairing_integrable (oneParticleEnergyWeight P)
    (oneParticleEnergyWeight_measurable P) (oneParticleEnergyWeight_ge_one P)
    (fun k => (fiberFormFactor g k : ℂ)) (fiberSource_quotient_memLp g P) f).norm
  simpa only [oneParticleEnergyEmbedding,norm_mul,Complex.star_def,Complex.norm_conj] using h

theorem formSource_double_majorant_integrable (g : ℝ) (P : GW.Space)
    (f h : OneParticleEnergySpace P) (C : ℝ) :
    Integrable (fun x : GW.Space × GW.Space =>
      C * ((‖oneParticleEnergyEmbedding P f x.1‖ * ‖(fiberFormFactor g x.1 : ℂ)‖) *
        (‖oneParticleEnergyEmbedding P h x.2‖ * ‖(fiberFormFactor g x.2 : ℂ)‖)))
      (volume.prod volume) :=
  ((formSource_product_norm_integrable g P f).mul_prod
    (formSource_product_norm_integrable g P h)).const_mul C

theorem formSource_bounded_kernel_integrable (g : ℝ) (P : GW.Space)
    (f h : OneParticleEnergySpace P) (J : GW.Space × GW.Space → ℂ) (C : ℝ)
    (hJ : ∀ x, ‖J x‖ ≤ C)
    (hmeas : AEStronglyMeasurable (fun x : GW.Space × GW.Space =>
      (starRingEnd ℂ) (oneParticleEnergyEmbedding P f x.1) * (fiberFormFactor g x.1 : ℂ) *
        J x * (fiberFormFactor g x.2 : ℂ) * oneParticleEnergyEmbedding P h x.2)
      (volume.prod volume)) :
    Integrable (fun x : GW.Space × GW.Space =>
      (starRingEnd ℂ) (oneParticleEnergyEmbedding P f x.1) * (fiberFormFactor g x.1 : ℂ) *
        J x * (fiberFormFactor g x.2 : ℂ) * oneParticleEnergyEmbedding P h x.2)
      (volume.prod volume) := by
  apply (formSource_double_majorant_integrable g P f h C).mono' hmeas
  exact Filter.Eventually.of_forall fun x => by
    simp only [norm_mul,Complex.star_def,Complex.norm_conj]
    calc
      _ = ((‖oneParticleEnergyEmbedding P f x.1‖ * ‖(fiberFormFactor g x.1 : ℂ)‖) *
          (‖oneParticleEnergyEmbedding P h x.2‖ * ‖(fiberFormFactor g x.2 : ℂ)‖)) * ‖J x‖ := by ring
      _ ≤ ((‖oneParticleEnergyEmbedding P f x.1‖ * ‖(fiberFormFactor g x.1 : ℂ)‖) *
          (‖oneParticleEnergyEmbedding P h x.2‖ * ‖(fiberFormFactor g x.2 : ℂ)‖)) * C :=
        mul_le_mul_of_nonneg_left (hJ x) (by positivity)
      _ = _ := by ring

end Froehlich
