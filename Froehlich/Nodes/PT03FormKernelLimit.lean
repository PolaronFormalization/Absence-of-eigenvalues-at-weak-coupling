import Froehlich.Nodes.PT03FormKernelIntegrability
import Froehlich.Nodes.PT03KernelConvergence
import Froehlich.Nodes.PT03BoundsCutoffCoefficient
import Froehlich.Nodes.PT03BoundsDiagonalLimit

set_option autoImplicit false

/-! Cutoff removal in the absolutely convergent scalar product integral,
along the full positive-cutoff filter and on the true Q1 domain. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space)

def thresholdJProduct (f h : OneParticleEnergySpace P) (x : GW.Space × GW.Space) : ℂ :=
  (starRingEnd ℂ) (oneParticleEnergyEmbedding P f x.1) * (fiberFormFactor g x.1 : ℂ) *
    thresholdKernelJ e he g hg hs P (x.1-P) (x.2-P) * (fiberFormFactor g x.2 : ℂ) *
      oneParticleEnergyEmbedding P h x.2

def cutoffThresholdJProduct (Λ : GW.Operators.PositiveCutoff)
    (f h : OneParticleEnergySpace P) (x : GW.Space × GW.Space) : ℂ :=
  (starRingEnd ℂ) (oneParticleEnergyEmbedding P f x.1) * (cutoffFormFactor g Λ.val x.1 : ℂ) *
    cutoffThresholdKernelJ e he g hg hs Λ P (x.1-P) (x.2-P) * (cutoffFormFactor g Λ.val x.2 : ℂ) *
      oneParticleEnergyEmbedding P h x.2

private theorem pt03_cutoffJProduct_bound (C : ℝ) (hC : 0 ≤ C)
    (hJ : ∀ (Λ : GW.Operators.PositiveCutoff) (q r : GW.Space),
      ‖cutoffThresholdKernelJ e he g hg hs Λ P q r‖ ≤ C)
    (Λ : GW.Operators.PositiveCutoff) (f h : OneParticleEnergySpace P) (x : GW.Space × GW.Space) :
    ‖cutoffThresholdJProduct e he g hg hs P Λ f h x‖ ≤
      C * ((‖oneParticleEnergyEmbedding P f x.1‖ * ‖(fiberFormFactor g x.1 : ℂ)‖) *
        (‖oneParticleEnergyEmbedding P h x.2‖ * ‖(fiberFormFactor g x.2 : ℂ)‖)) := by
  have h1 := pt03_cutoffCoefficient_norm_le g Λ x.1
  have h2 := pt03_cutoffCoefficient_norm_le g Λ x.2
  have hj := hJ Λ (x.1-P) (x.2-P)
  have ha := mul_le_mul h1 hj (norm_nonneg _) (norm_nonneg (fiberFormFactor g x.1 : ℂ))
  have hb := mul_le_mul ha h2 (norm_nonneg _)
    (mul_nonneg (norm_nonneg (fiberFormFactor g x.1 : ℂ)) hC)
  have hc := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hb (norm_nonneg (oneParticleEnergyEmbedding P h x.2)))
    (norm_nonneg (oneParticleEnergyEmbedding P f x.1))
  calc
    _ = ‖oneParticleEnergyEmbedding P f x.1‖ *
        ((‖(cutoffFormFactor g Λ.val x.1 : ℂ)‖ *
          ‖cutoffThresholdKernelJ e he g hg hs Λ P (x.1-P) (x.2-P)‖ *
            ‖(cutoffFormFactor g Λ.val x.2 : ℂ)‖) * ‖oneParticleEnergyEmbedding P h x.2‖) := by
      simp only [cutoffThresholdJProduct,norm_mul,Complex.norm_conj]
      ring
    _ ≤ _ := hc
    _ = _ := by ring

theorem cutoffThresholdKernel_integral_tendsto (hP : ‖P‖ ≤ 1/4)
    (f h : OneParticleEnergySpace P) :
    Tendsto (fun Λ : GW.Operators.PositiveCutoff =>
      ∫ x : GW.Space × GW.Space, cutoffThresholdJProduct e he g hg hs P Λ f h x ∂volume.prod volume)
      atTop (𝓝 (∫ x : GW.Space × GW.Space, thresholdJProduct e he g hg hs P f h x ∂volume.prod volume)) := by
  letI : (atTop : Filter GW.Operators.PositiveCutoff).IsCountablyGenerated :=
    pt03_positiveCutoff_atTop_countablyGenerated
  obtain ⟨C,hC,hBound⟩ := thresholdKernels_uniform_bound
  let M := fun x : GW.Space × GW.Space =>
    C * ((‖oneParticleEnergyEmbedding P f x.1‖ * ‖(fiberFormFactor g x.1 : ℂ)‖) *
      (‖oneParticleEnergyEmbedding P h x.2‖ * ‖(fiberFormFactor g x.2 : ℂ)‖))
  have hM : Integrable M (volume.prod volume) := formSource_double_majorant_integrable g P f h C
  apply tendsto_integral_filter_of_dominated_convergence M
  · exact Eventually.of_forall fun Λ =>
      (cutoffThresholdKernelJ_form_integrable e he g hg hs P hP Λ f h).aestronglyMeasurable
  · exact Eventually.of_forall fun Λ => Eventually.of_forall fun x =>
      pt03_cutoffJProduct_bound e he g hg hs P C hC.le
        (fun Λ q r => ((hBound g e he hg hs P q r hP).2.2 Λ).1) Λ f h x
  · exact hM
  · exact Eventually.of_forall fun x => by
      have hv1 := pt03_cutoffCoefficient_tendsto g x.1
      have hv2 := pt03_cutoffCoefficient_tendsto g x.2
      have hJ := cutoffThresholdKernelJ_tendsto e he g hg hs P (x.1-P) (x.2-P)
      have hf0 : Tendsto (fun _ : GW.Operators.PositiveCutoff =>
          (starRingEnd ℂ) (oneParticleEnergyEmbedding P f x.1)) atTop
          (𝓝 ((starRingEnd ℂ) (oneParticleEnergyEmbedding P f x.1))) := tendsto_const_nhds
      have hh0 : Tendsto (fun _ : GW.Operators.PositiveCutoff => oneParticleEnergyEmbedding P h x.2)
          atTop (𝓝 (oneParticleEnergyEmbedding P h x.2)) := tendsto_const_nhds
      have hlim := (((hf0.mul hv1).mul hJ).mul hv2).mul hh0
      simpa only [cutoffThresholdJProduct,thresholdJProduct] using hlim

end Froehlich
