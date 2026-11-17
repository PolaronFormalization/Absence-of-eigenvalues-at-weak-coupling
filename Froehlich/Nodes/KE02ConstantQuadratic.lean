import Froehlich.Nodes.KE02ConstantRegularity
import Froehlich.Nodes.KE01KernelReflection
import Froehlich.Nodes.CA03Local

set_option autoImplicit false
noncomputable section
namespace Froehlich

theorem kernelConstant_quadratic_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space), ‖P‖ ≤ 1/4 →
      |kernelConstant e he g hg hs P-kernelConstant e he g hg hs 0| ≤ C*‖P‖^2 := by
  obtain ⟨C,hC,hB⟩ := kernelConstant_iterated_uniform
  refine ⟨C,hC,?_⟩
  intro e he g hg hs P hP
  have hsegment (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖t • P‖ ≤ 1/4 := by
    have hnorm : ‖t • P‖ ≤ ‖P‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
      nlinarith [norm_nonneg P,ht.2]
    exact hnorm.trans hP
  have hAt (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ContDiffAt ℝ 3 (kernelConstant e he g hg hs) (t • P) :=
    kernelConstant_contDiffAt e he g hg hs _ (by linarith [hsegment t ht])
  have hH (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖fderiv ℝ (fderiv ℝ (kernelConstant e he g hg hs)) (t • P)‖ ≤ C := by
    have h := hB e he g hg hs 2 (by norm_num) (t • P) (hsegment t ht)
    rw [←norm_iteratedFDeriv_fderiv (n := 1),norm_iteratedFDeriv_one] at h
    exact h
  have hquad := even_norm_sub_le_quadratic_on_segment (kernelConstant e he g hg hs)
    (kernelConstant_even e he g hg hs) P C
    ((kernelConstant_contDiffAt e he g hg hs 0 (by simp)).differentiableAt (by norm_num))
    (fun t ht => (hAt t ht).differentiableAt (by norm_num))
    (fun t ht => ((hAt t ht).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)) hH
  have hnonneg : 0 ≤ C*‖P‖^2 := mul_nonneg hC.le (sq_nonneg _)
  exact hquad.trans (by linarith)

end Froehlich
