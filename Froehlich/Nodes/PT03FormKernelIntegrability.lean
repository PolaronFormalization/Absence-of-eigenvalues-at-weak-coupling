import Froehlich.Nodes.PT03FormIntegrability
import Froehlich.Nodes.PT03KernelMeasurability
import Froehlich.Nodes.PT03BoundsKernels

set_option autoImplicit false

/-! Absolute product integrability of the actual singular and cutoff
kernels on the genuine one-particle energy domain. -/
noncomputable section
open MeasureTheory
namespace Froehlich

private theorem pt03_form_kernel_measurable (g : ℝ) (P : GW.Space)
    (f h : OneParticleEnergySpace P) (J : GW.Space × GW.Space → ℂ) (hJ : Measurable J) :
    AEStronglyMeasurable (fun x : GW.Space × GW.Space =>
      (starRingEnd ℂ) (oneParticleEnergyEmbedding P f x.1) * (fiberFormFactor g x.1 : ℂ) *
        J x * (fiberFormFactor g x.2 : ℂ) * oneParticleEnergyEmbedding P h x.2)
      (volume.prod volume) := by
  have hv : AEStronglyMeasurable (fun k : GW.Space => (fiberFormFactor g k : ℂ)) volume :=
    (Complex.continuous_ofReal.measurable.comp (fiberFormFactor_measurable g)).aestronglyMeasurable
  exact (((((Complex.conjCLE.continuous.comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable (oneParticleEnergyEmbedding P f))).comp_fst).mul hv.comp_fst).mul
      hJ.aestronglyMeasurable).mul hv.comp_snd).mul
        (Lp.aestronglyMeasurable (oneParticleEnergyEmbedding P h)).comp_snd

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

include hP in
theorem thresholdKernelJ_form_integrable (f h : OneParticleEnergySpace P) :
    Integrable (fun x : GW.Space × GW.Space =>
      (starRingEnd ℂ) (oneParticleEnergyEmbedding P f x.1) * (fiberFormFactor g x.1 : ℂ) *
        thresholdKernelJ e he g hg hs P (x.1-P) (x.2-P) * (fiberFormFactor g x.2 : ℂ) *
          oneParticleEnergyEmbedding P h x.2) (volume.prod volume) := by
  obtain ⟨C,hC,hBound⟩ := thresholdKernels_uniform_bound
  let J := fun x : GW.Space × GW.Space => thresholdKernelJ e he g hg hs P (x.1-P) (x.2-P)
  have ht : Continuous (fun x : GW.Space × GW.Space => (P,(x.1-P,x.2-P))) := by fun_prop
  have hJ : Measurable J := ((thresholdKernelJ_continuous e he g hg hs).comp ht).measurable
  exact formSource_bounded_kernel_integrable g P f h J C
    (fun x => (hBound g e he hg hs P (x.1-P) (x.2-P) hP).1)
    (pt03_form_kernel_measurable g P f h J hJ)

include hP in
theorem thresholdKernelC_form_integrable (f h : OneParticleEnergySpace P) :
    Integrable (fun x : GW.Space × GW.Space =>
      (starRingEnd ℂ) (oneParticleEnergyEmbedding P f x.1) * (fiberFormFactor g x.1 : ℂ) *
        thresholdKernelC e he g hg hs P (x.1-P) (x.2-P) * (fiberFormFactor g x.2 : ℂ) *
          oneParticleEnergyEmbedding P h x.2) (volume.prod volume) := by
  obtain ⟨C,hC,hBound⟩ := thresholdKernels_uniform_bound
  let J := fun x : GW.Space × GW.Space => thresholdKernelC e he g hg hs P (x.1-P) (x.2-P)
  have ht : Continuous (fun x : GW.Space × GW.Space => (P,(x.1-P,x.2-P))) := by fun_prop
  have hComposed := (thresholdKernelC_measurable e he g hg hs).comp ht.measurable
  have hJ : Measurable J := by
    simpa only [Function.comp_def,J] using hComposed
  have hb : ∀ x : GW.Space × GW.Space, ‖J x‖ ≤ C :=
    fun x => (hBound g e he hg hs P (x.1-P) (x.2-P) hP).2.1
  have hm := pt03_form_kernel_measurable g P f h J hJ
  have hI := formSource_bounded_kernel_integrable g P f h J C hb hm
  simpa only [J] using hI

include hP in
theorem cutoffThresholdKernelJ_form_integrable (Λ : GW.Operators.PositiveCutoff)
    (f h : OneParticleEnergySpace P) :
    Integrable (fun x : GW.Space × GW.Space =>
      (starRingEnd ℂ) (oneParticleEnergyEmbedding P f x.1) * (cutoffFormFactor g Λ.val x.1 : ℂ) *
        cutoffThresholdKernelJ e he g hg hs Λ P (x.1-P) (x.2-P) * (cutoffFormFactor g Λ.val x.2 : ℂ) *
          oneParticleEnergyEmbedding P h x.2) (volume.prod volume) := by
  obtain ⟨C,hC,hBound⟩ := thresholdKernels_uniform_bound
  let J := fun x : GW.Space × GW.Space => cutoffThresholdKernelJ e he g hg hs Λ P (x.1-P) (x.2-P)
  have ht : Continuous (fun x : GW.Space × GW.Space => (P,(x.1-P,x.2-P))) := by fun_prop
  have hJ : Measurable J := ((cutoffThresholdKernelJ_continuous e he g hg hs Λ).comp ht).measurable
  let b := fun k : GW.Space => if ‖k‖ ≤ Λ.val then (1 : ℂ) else 0
  have hb : Measurable b := Measurable.ite (measurableSet_le measurable_norm measurable_const)
    measurable_const measurable_const
  let K := fun x : GW.Space × GW.Space => b x.1 * J x * b x.2
  have hK : Measurable K := ((hb.comp measurable_fst).mul hJ).mul (hb.comp measurable_snd)
  have hKC (x : GW.Space × GW.Space) : ‖K x‖ ≤ C := by
    by_cases h1 : ‖x.1‖ ≤ Λ.val
    · by_cases h2 : ‖x.2‖ ≤ Λ.val
      · simpa only [K,b,if_pos h1,if_pos h2,one_mul,mul_one] using
          ((hBound g e he hg hs P (x.1-P) (x.2-P) hP).2.2 Λ).1
      · simpa only [K,b,if_pos h1,if_neg h2,mul_zero,norm_zero] using hC.le
    · simp only [K,b,if_neg h1,zero_mul,norm_zero]
      exact hC.le
  have hbase := formSource_bounded_kernel_integrable g P f h K C hKC
    (pt03_form_kernel_measurable g P f h K hK)
  have hmask (k : GW.Space) : (cutoffFormFactor g Λ.val k : ℂ) = (fiberFormFactor g k : ℂ) * b k := by
    by_cases hk : ‖k‖ ≤ Λ.val <;> simp only [cutoffFormFactor,b,hk,ite_true,ite_false,mul_one,mul_zero,Complex.ofReal_zero]
  apply hbase.congr
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [hmask,hmask]
    dsimp only [K]
    ring

end Froehlich
