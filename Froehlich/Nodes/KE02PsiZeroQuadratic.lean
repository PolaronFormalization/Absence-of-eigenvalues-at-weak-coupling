import Froehlich.Nodes.KE02QSliceRegularity
import Froehlich.Nodes.KE02Vanishing
import Froehlich.Nodes.CA03Even
import Froehlich.Nodes.AN03

set_option autoImplicit false
noncomputable section
namespace Froehlich

theorem kernelPsi_zero_quadratic_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (q : GW.Space),
      |kernelPsi e he g hg hs 0 q| ≤ C*(omega q)^2 := by
  obtain ⟨M,hM,hB⟩ := kernelRealQSlice_iterated_uniform
  refine ⟨2*M,by positivity,?_⟩
  intro e he g hg hs q
  let F := kernelRealQSlice e he g hg hs 0 0
  have hF : ContDiff ℝ 3 F := kernelRealQSlice_contDiff e he g hg hs 0 0 (by simp)
  have hEven : Function.Even F := by
    intro p
    have h := congrArg Complex.re (thresholdKernelC_reflection e he g hg hs 0 p 0)
    simpa only [neg_zero,F,kernelRealQSlice,kernelRealQRSlice] using h
  have hH (p : GW.Space) : ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ M := by
    have h := hB e he g hg hs 0 (by simp) 2 (by norm_num) 0 p
    rw [←norm_iteratedFDeriv_fderiv (n := 1),norm_iteratedFDeriv_one] at h
    exact h
  have hTaylor := even_norm_sub_le_quadratic F hEven
    (hF.of_le (by norm_num) : ContDiff ℝ 2 F) M hH q
  have hNorm (p : GW.Space) : |F p| ≤ M := by
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hB e he g hg hs 0 (by simp) 0 (by norm_num) 0 p
  have hf : kernelPsi e he g hg hs 0 q = F q-F 0 := rfl
  have hLarge : |F q-F 0| ≤ 2*M := by
    have hn := norm_sub_le (F q) (F 0)
    simp only [Real.norm_eq_abs] at hn
    exact hn.trans (by linarith [hNorm q,hNorm 0])
  rw [hf]
  by_cases hq : ‖q‖ ≤ 1
  · rw [omega,min_eq_left hq]
    have hp : 0 ≤ M*‖q‖^2 := mul_nonneg hM.le (sq_nonneg _)
    nlinarith
  · rw [omega,min_eq_right (le_of_lt (lt_of_not_ge hq)),one_pow,mul_one]
    exact hLarge

end Froehlich
