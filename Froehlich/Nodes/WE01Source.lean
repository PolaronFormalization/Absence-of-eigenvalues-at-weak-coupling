import Froehlich.Nodes.WE01Operator

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

def weightedKernelBoundConstant : ℝ := normalizedWeightedKernel_majorant.choose

theorem weightedKernelBoundConstant_positive : 0 < weightedKernelBoundConstant :=
  normalizedWeightedKernel_majorant.choose_spec.1

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

def weightedKernelOperator :
    Lp ℝ ⊤ (volume : Measure GW.Space) →L[ℝ] Lp ℝ ⊤ (volume : Measure GW.Space) :=
  weightedLinftyOperator e he g hg hs P hP weightedKernelBoundConstant
    weightedKernelBoundConstant_positive.le
    (fun q r => normalizedWeightedKernel_majorant.choose_spec.2 e he g hg hs P q r hP)

theorem weightedKernelOperator_ae (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    weightedKernelOperator e he g hg hs P hP f =ᵐ[volume]
      normalizedWeightedIntegral e he g hg hs P f :=
  weightedLinftyOperator_ae e he g hg hs P hP weightedKernelBoundConstant
    weightedKernelBoundConstant_positive.le
    (fun q r => normalizedWeightedKernel_majorant.choose_spec.2 e he g hg hs P q r hP) f

theorem weightedKernelOperator_norm_uniform : ∃ CW : ℝ, 0 < CW ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
      ‖weightedKernelOperator e he g hg hs P hP‖ ≤ CW := by
  obtain ⟨CI,hCI,hI⟩ := weightedKernelDensity_integral_uniform
  refine ⟨weightedKernelBoundConstant*CI,mul_pos weightedKernelBoundConstant_positive hCI,?_⟩
  intro e he g hg hs P hP
  exact (weightedLinftyOperator_norm_le e he g hg hs P hP weightedKernelBoundConstant
    weightedKernelBoundConstant_positive.le
    (fun q r => normalizedWeightedKernel_majorant.choose_spec.2 e he g hg hs P q r hP)).trans
    (mul_le_mul_of_nonneg_left (hI P hP) weightedKernelBoundConstant_positive.le)

/-- The raw formula, not a point-value assertion about the native quotient representative. -/
def normalizedKernelPsi (q : GW.Space) : ℝ :=
  if q = 0 then 0 else kernelPsi e he g hg hs P q/omega q

theorem normalizedKernelPsi_zero : normalizedKernelPsi e he g hg hs P 0 = 0 := by
  simp [normalizedKernelPsi]

theorem normalizedKernelPsi_measurable : Measurable (normalizedKernelPsi e he g hg hs P) :=
  Measurable.ite (measurableSet_singleton 0) measurable_const
    ((kernelPsi_measurable e he g hg hs P).div omega_measurable)

theorem normalizedKernelPsi_bound_uniform : ∃ CW : ℝ, 0 < CW ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P q : GW.Space), ‖P‖ ≤ 1/4 →
      ‖normalizedKernelPsi e he g hg hs P q‖ ≤ CW := by
  obtain ⟨C,hC,hB⟩ := kernelPsi_uniform_bound
  refine ⟨C*(5/4 : ℝ),by positivity,?_⟩
  intro e he g hg hs P q hP
  by_cases hq : q = 0
  · rw [hq,normalizedKernelPsi_zero,norm_zero]
    positivity
  · have ho : 0 < omega q := lt_min (norm_pos_iff.mpr hq) zero_lt_one
    have hb : |kernelPsi e he g hg hs P q|/omega q ≤ C*(omega q+‖P‖) := by
      apply (div_le_iff₀ ho).mpr
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hB e he g hg hs P q hP
    have hs' : omega q+‖P‖ ≤ (5/4 : ℝ) := by linarith [omega_le_one q]
    simp only [normalizedKernelPsi,ite_eq_right hq,Real.norm_eq_abs,abs_div,abs_of_pos ho]
    exact hb.trans (mul_le_mul_of_nonneg_left hs' hC.le)

include hP in
theorem normalizedKernelPsi_memLp : MemLp (normalizedKernelPsi e he g hg hs P) ⊤ volume := by
  obtain ⟨CW,hCW,hB⟩ := normalizedKernelPsi_bound_uniform
  exact memLp_top_of_bound (normalizedKernelPsi_measurable e he g hg hs P).aestronglyMeasurable CW
    (Eventually.of_forall (fun q => hB e he g hg hs P q hP))

def weightedKernelSource : Lp ℝ ⊤ (volume : Measure GW.Space) :=
  (normalizedKernelPsi_memLp e he g hg hs P hP).toLp (normalizedKernelPsi e he g hg hs P)

theorem weightedKernelSource_ae : weightedKernelSource e he g hg hs P hP =ᵐ[volume]
    normalizedKernelPsi e he g hg hs P := MemLp.coeFn_toLp _

theorem weightedKernelSource_norm_uniform : ∃ CW : ℝ, 0 < CW ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
      ‖weightedKernelSource e he g hg hs P hP‖ ≤ CW := by
  obtain ⟨CW,hCW,hB⟩ := normalizedKernelPsi_bound_uniform
  refine ⟨CW,hCW,?_⟩
  intro e he g hg hs P hP
  apply linftyReal_norm_le_of_ae_bound _ CW hCW.le
  filter_upwards [weightedKernelSource_ae e he g hg hs P hP] with q hq
  rw [hq]
  exact hB e he g hg hs P q hP

end Froehlich
