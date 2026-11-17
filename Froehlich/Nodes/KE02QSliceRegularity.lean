import Froehlich.Nodes.KE02QRSliceRegularity

set_option autoImplicit false
noncomputable section
namespace Froehlich

def kernelQSection : GW.Space →L[ℝ] GW.Space × GW.Space :=
  (ContinuousLinearMap.id ℝ GW.Space).prod (0 : GW.Space →L[ℝ] GW.Space)

theorem kernelQSection_affine (r q : GW.Space) : ((0 : GW.Space),r)+kernelQSection q = (q,r) := by
  apply Prod.ext
  · change 0+q=q; exact zero_add q
  · change r+0=r; exact add_zero r

theorem kernelQSection_norm : ‖kernelQSection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  change ‖(q,(0 : GW.Space))‖ ≤ 1*‖q‖
  simp only [Prod.norm_def,norm_zero,max_eq_left (norm_nonneg q),one_mul,le_refl]

def kernelRealQSlice (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P r q : GW.Space) : ℝ :=
  kernelRealQRSlice e he g hg hs P (q,r)

theorem kernelRealQSlice_contDiff (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (P r : GW.Space) (hP : ‖P‖ < 1/3) :
    ContDiff ℝ 3 (kernelRealQSlice e he g hg hs P r) := by
  have h := (kernelRealQRSlice_contDiff e he g hg hs P hP).comp
    (contDiff_id.prodMk (contDiff_const : ContDiff ℝ 3 (fun _ : GW.Space => r)))
  simpa only [Function.comp_def,id_eq,kernelRealQSlice] using! h

theorem kernelRealQSlice_iterated_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space), ‖P‖ ≤ 1/4 →
      ∀ k ≤ 3,∀ r q : GW.Space,
      ‖iteratedFDeriv ℝ k (kernelRealQSlice e he g hg hs P r) q‖ ≤ C := by
  obtain ⟨C,hC,hB⟩ := kernelRealQRSlice_iterated_uniform
  refine ⟨C,hC,?_⟩
  intro e he g hg hs P hP k hk r q
  let F := kernelRealQRSlice e he g hg hs P
  have hF : ContDiff ℝ 3 F := kernelRealQRSlice_contDiff e he g hg hs P (by linarith)
  have hn := iteratedFDeriv_comp_affine_norm_le_at ((0 : GW.Space),r) kernelQSection F k q
    (hF.of_le (by exact_mod_cast hk)).contDiffAt
  have hpoint : ‖iteratedFDeriv ℝ k F (((0 : GW.Space),r)+kernelQSection q)‖ ≤ C := by
    rw [kernelQSection_affine]
    exact hB e he g hg hs P hP k hk (q,r)
  have hpow : ‖kernelQSection‖^k ≤ 1 := pow_le_one₀ (norm_nonneg _) kernelQSection_norm
  have hf : (fun z => F (((0 : GW.Space),r)+kernelQSection z)) = kernelRealQSlice e he g hg hs P r := by
    funext z
    rw [kernelQSection_affine]
    rfl
  rw [hf] at hn
  exact hn.trans ((mul_le_mul hpoint hpow (pow_nonneg (norm_nonneg _) k) hC.le).trans_eq (mul_one _))

end Froehlich
