import Froehlich.Nodes.OP01KernelSymbols

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Froehlich

/-- The real normalized kernel on the existing Lebesgue space. The entire
row at q=0 is prescribed to vanish. -/
def normalizedWeightedKernel (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (P q r : GW.Space) : ℝ :=
  if q = 0 then 0 else
    (remainderKernel e he g hg hs P q r/omega q)*muDensity P r*omega r

/-- The only integration density required, including at P=0. -/
def weightedKernelDensity (P r : GW.Space) : ℝ := (omega r)^2*muDensity P r

theorem weightedKernelDensity_nonnegative (P r : GW.Space) :
    0 ≤ weightedKernelDensity P r := mul_nonneg (sq_nonneg _) (muDensity_nonneg P r)

theorem weightedKernelDensity_integrable (P : GW.Space) (hP : ‖P‖ ≤ 1/4) :
    Integrable (weightedKernelDensity P) volume := by
  obtain ⟨CI,hCI,hB⟩ := omega_moments_uniform
  exact (hB P hP).1.1

theorem weightedKernelDensity_integral_uniform : ∃ CI : ℝ, 0 < CI ∧
    ∀ P : GW.Space, ‖P‖ ≤ 1/4 → ∫ r, weightedKernelDensity P r ≤ CI := by
  obtain ⟨CI,hCI,hB⟩ := omega_moments_uniform
  exact ⟨CI,hCI,fun P hP => (hB P hP).1.2⟩

theorem normalizedWeightedKernel_measurable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) :
    Measurable (Function.uncurry (normalizedWeightedKernel e he g hg hs P)) := by
  have hF := remainderKernel_measurable e he g hg hs P
  have hq : Measurable (fun qr : GW.Space × GW.Space => omega qr.1) :=
    omega_measurable.comp measurable_fst
  have hr : Measurable (fun qr : GW.Space × GW.Space => omega qr.2) :=
    omega_measurable.comp measurable_snd
  have hm : Measurable (fun qr : GW.Space × GW.Space => muDensity P qr.2) :=
    (muDensity_measurable P).comp measurable_snd
  exact Measurable.ite ((measurableSet_singleton 0).preimage measurable_fst)
    measurable_const (((hF.div hq).mul hm).mul hr)

theorem normalizedWeightedKernel_majorant : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P q r : GW.Space), ‖P‖ ≤ 1/4 →
      ‖normalizedWeightedKernel e he g hg hs P q r‖ ≤ C*weightedKernelDensity P r := by
  obtain ⟨C,hC,hB⟩ := remainderKernel_uniform_bound
  refine ⟨C,hC,?_⟩
  intro e he g hg hs P q r hP
  by_cases hq : q = 0
  · simp only [normalizedWeightedKernel,ite_eq_left hq,norm_zero]
    exact mul_nonneg hC.le (weightedKernelDensity_nonnegative P r)
  · have ho : 0 < omega q := lt_min (norm_pos_iff.mpr hq) zero_lt_one
    have hdiv : |remainderKernel e he g hg hs P q r/omega q| ≤ C*omega r := by
      rw [abs_div,abs_of_pos ho]
      apply (div_le_iff₀ ho).mpr
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hB e he g hg hs P q r hP
    simp only [normalizedWeightedKernel,ite_eq_right hq,norm_mul,Real.norm_eq_abs,
      abs_of_nonneg (muDensity_nonneg P r),abs_of_nonneg (omega_nonneg r)]
    calc
      _ ≤ (C*omega r)*muDensity P r*omega r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdiv (muDensity_nonneg P r)) (omega_nonneg r)
      _ = _ := by unfold weightedKernelDensity; ring

end Froehlich
