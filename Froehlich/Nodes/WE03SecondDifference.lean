import Froehlich.Nodes.KE02
import Froehlich.Nodes.KE02QSliceRegularity
import Froehlich.Nodes.CA01GeneralTaylor

set_option autoImplicit false
noncomputable section
namespace Froehlich

/-- Two genuine Taylor remainders cancel the actual derivative at zero.
No differentiability under an integral is involved. -/
theorem real_symmetric_secondDifference_bound
    (F : GW.Space → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ M) (q : GW.Space) :
    |F q+F (-q)-2*F 0| ≤ M*‖q‖^2 := by
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hdd : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hp := norm_remainder_of_second_fderiv F 0 q M
    (fun _ _ => hd _) (fun _ _ => hdd _) (fun _ _ => hH _)
  have hm := norm_remainder_of_second_fderiv F 0 (-q) M
    (fun _ _ => hd _) (fun _ _ => hdd _) (fun _ _ => hH _)
  simp only [zero_add,Real.norm_eq_abs,norm_neg,map_neg] at hp hm
  have htriangle := abs_add_le (F q-F 0-fderiv ℝ F 0 q)
    (F (-q)-F 0+fderiv ℝ F 0 q)
  have heq : (F q-F 0-fderiv ℝ F 0 q)+(F (-q)-F 0+fderiv ℝ F 0 q) =
      F q+F (-q)-2*F 0 := by ring
  rw [heq] at htriangle
  have hm' : |F (-q)-F 0+fderiv ℝ F 0 q| ≤ M*‖q‖^2/2 := by
    simpa only [sub_neg_eq_add] using hm
  linarith

theorem remainderKernel_q_contDiff
    (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P r : GW.Space) (hP : ‖P‖ < 1/3) :
    ContDiff ℝ 2 (fun q => remainderKernel e he g hg hs P q r) := by
  have hr := kernelRealQSlice_contDiff e he g hg hs P r hP
  have hz := kernelRealQSlice_contDiff e he g hg hs P 0 hP
  have h := ((hr.sub hz).sub
    (contDiff_const : ContDiff ℝ 3 (fun _ : GW.Space => (thresholdKernelC e he g hg hs P 0 r).re))).add
    (contDiff_const : ContDiff ℝ 3 (fun _ : GW.Space => (thresholdKernelC e he g hg hs P 0 0).re))
  have hfun : (fun q => kernelRealQSlice e he g hg hs P r q-kernelRealQSlice e he g hg hs P 0 q-
      (thresholdKernelC e he g hg hs P 0 r).re+(thresholdKernelC e he g hg hs P 0 0).re) =
      (fun q => remainderKernel e he g hg hs P q r) := by
    funext q
    exact (remainderKernel_double_difference e he g hg hs P q r).symm
  have h' : ContDiff ℝ 3 (fun q => remainderKernel e he g hg hs P q r) := by
    simpa only [Pi.sub_def,Pi.add_def,hfun] using h
  exact h'.of_le (by norm_num)

/-- The source's actual symmetric remainder difference, uniformly before
coupling and the integration variable r. -/
theorem remainderKernel_zero_symmetricDifference_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (q r : GW.Space),
      |remainderKernel e he g hg hs 0 q r+remainderKernel e he g hg hs 0 (-q) r| ≤ C*‖q‖^2*omega r := by
  obtain ⟨C,hC,hB⟩ := remainderKernel_qDerivatives_uniform
  refine ⟨C,hC,?_⟩
  intro e he g hg hs q r
  have hH (x : GW.Space) :
      ‖fderiv ℝ (fderiv ℝ (fun p => remainderKernel e he g hg hs 0 p r)) x‖ ≤ C*omega r := by
    have h := hB e he g hg hs 0 x r (by simp)
    linarith [norm_nonneg (fderiv ℝ (fun p => remainderKernel e he g hg hs 0 p r) x)]
  have h := real_symmetric_secondDifference_bound (fun p => remainderKernel e he g hg hs 0 p r)
    (remainderKernel_q_contDiff e he g hg hs 0 r (by simp)) (C*omega r) hH q
  simpa only [remainderKernel_left_zero,mul_zero,zero_mul,sub_zero,mul_assoc,mul_comm,mul_left_comm] using h

end Froehlich
