import Froehlich.Nodes.KE02
import Froehlich.Nodes.PT03KernelMeasurability

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Froehlich

def kernelDensityMajorant (P q : GW.Space) : ℝ := omega q*wDensity P q

def boundedThresholdKernel (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P q r : GW.Space) : ℂ :=
  (wDensity P q : ℂ)*(remainderKernel e he g hg hs P q r : ℂ)*(wDensity P r : ℂ)

def kernelSourceCoefficient (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P q : GW.Space) : ℂ :=
  (g : ℂ)*(wDensity P q : ℂ)*(kernelPsi e he g hg hs P q : ℂ)

theorem kernelDensityMajorant_nonnegative (P q : GW.Space) : 0 ≤ kernelDensityMajorant P q :=
  mul_nonneg (omega_nonneg q) (wDensity_nonneg P q)

theorem kernelDensityMajorant_measurable (P : GW.Space) : Measurable (kernelDensityMajorant P) :=
  omega_measurable.mul (wDensity_measurable P)

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

private theorem op01_realKernel_measurable (P : GW.Space) :
    Measurable (fun qr : GW.Space × GW.Space => (thresholdKernelC e he g hg hs P qr.1 qr.2).re) := by
  have hm : Measurable (fun qr : GW.Space × GW.Space => (P,qr)) :=
    (measurable_const : Measurable (fun _ : GW.Space × GW.Space => P)).prodMk measurable_id
  have h := (thresholdKernelC_measurable e he g hg hs).comp hm
  have hc : Measurable (fun qr : GW.Space × GW.Space => thresholdKernelC e he g hg hs P qr.1 qr.2) := by
    simpa only [Function.comp_def] using! h
  exact Complex.continuous_re.measurable.comp hc

theorem kernelPsi_measurable (P : GW.Space) : Measurable (kernelPsi e he g hg hs P) := by
  have h := (op01_realKernel_measurable e he g hg hs P).comp
    (measurable_id.prodMk (measurable_const : Measurable (fun _ : GW.Space => (0 : GW.Space))))
  have hc : Measurable (fun q : GW.Space => (thresholdKernelC e he g hg hs P q 0).re) := by
    simpa only [Function.comp_def] using! h
  exact hc.sub measurable_const

theorem remainderKernel_measurable (P : GW.Space) :
    Measurable (Function.uncurry (remainderKernel e he g hg hs P)) := by
  have hC := op01_realKernel_measurable e he g hg hs P
  have hq := hC.comp (measurable_fst.prodMk (measurable_const : Measurable (fun _ : GW.Space × GW.Space => (0 : GW.Space))))
  have hr := hC.comp ((measurable_const : Measurable (fun _ : GW.Space × GW.Space => (0 : GW.Space))).prodMk measurable_snd)
  have h := ((hC.sub hq).sub hr).add (measurable_const : Measurable (fun _ : GW.Space × GW.Space => (thresholdKernelC e he g hg hs P 0 0).re))
  have hf : Function.uncurry (remainderKernel e he g hg hs P) =
      (fun qr : GW.Space × GW.Space => (thresholdKernelC e he g hg hs P qr.1 qr.2).re-
        (thresholdKernelC e he g hg hs P qr.1 0).re-(thresholdKernelC e he g hg hs P 0 qr.2).re+
        (thresholdKernelC e he g hg hs P 0 0).re) := by
    funext qr
    exact remainderKernel_double_difference e he g hg hs P qr.1 qr.2
  rw [hf]
  simpa only [Function.comp_def] using! h

theorem boundedThresholdKernel_measurable (P : GW.Space) : Measurable (Function.uncurry (boundedThresholdKernel e he g hg hs P)) := by
  have hw := Complex.continuous_ofReal.measurable.comp (wDensity_measurable P)
  exact ((hw.comp measurable_fst).mul
    (Complex.continuous_ofReal.measurable.comp (remainderKernel_measurable e he g hg hs P))).mul (hw.comp measurable_snd)

theorem kernelSourceCoefficient_measurable (P : GW.Space) : Measurable (kernelSourceCoefficient e he g hg hs P) :=
  ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp (wDensity_measurable P))).mul
    (Complex.continuous_ofReal.measurable.comp (kernelPsi_measurable e he g hg hs P)))

theorem boundedThresholdKernel_product_majorant : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P q r : GW.Space), ‖P‖ ≤ 1/4 →
      ‖boundedThresholdKernel e he g hg hs P q r‖ ≤ C*kernelDensityMajorant P q*kernelDensityMajorant P r := by
  obtain ⟨C,hC,hB⟩ := remainderKernel_uniform_bound
  refine ⟨C,hC,?_⟩
  intro e he g hg hs P q r hP
  simp only [boundedThresholdKernel,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (wDensity_nonneg P q),abs_of_nonneg (wDensity_nonneg P r)]
  calc
    _ ≤ wDensity P q*(C*omega q*omega r)*wDensity P r :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hB e he g hg hs P q r hP)
        (wDensity_nonneg P q)) (wDensity_nonneg P r)
    _ = _ := by unfold kernelDensityMajorant; ring

end Froehlich
