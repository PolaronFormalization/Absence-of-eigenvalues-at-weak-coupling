import Froehlich.Nodes.KE01PhysicalDerivativeBounds
import Froehlich.Nodes.KE01CanonicalNormAffineChain

set_option autoImplicit false
noncomputable section
namespace Froehlich

def kernelQRSection : (GW.Space × GW.Space) →L[ℝ] GW.Space × (GW.Space × GW.Space) :=
  (0 : (GW.Space × GW.Space) →L[ℝ] GW.Space).prod
    (ContinuousLinearMap.id ℝ (GW.Space × GW.Space))

theorem kernelQRSection_apply (qr : GW.Space × GW.Space) : kernelQRSection qr = (0,qr) := rfl

theorem kernelQR_affine_apply (P : GW.Space) (qr : GW.Space × GW.Space) :
    (P,((0 : GW.Space),0))+kernelQRSection qr = (P,qr) := by
  apply Prod.ext
  · change P+0=P; exact add_zero P
  · change (0 : GW.Space × GW.Space)+qr=qr; exact zero_add qr

def kernelRealQRSlice (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (qr : GW.Space × GW.Space) : ℝ :=
  (thresholdKernelC e he g hg hs P qr.1 qr.2).re

theorem kernelRealQRSlice_contDiff (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (P : GW.Space) (hP : ‖P‖ < 1/3) :
    ContDiff ℝ 3 (kernelRealQRSlice e he g hg hs P) := by
  rw [contDiff_iff_contDiffAt]
  intro qr
  have hAt := thresholdKernelC_contDiffAt e he g hg hs (P,qr) hP
  have ha : ContDiff ℝ 3 (fun z : GW.Space × GW.Space => (P,((0 : GW.Space),0))+kernelQRSection z) :=
    contDiff_const.add kernelQRSection.contDiff
  have hAt' : ContDiffAt ℝ 3 (fun u : GW.Space × (GW.Space × GW.Space) =>
      thresholdKernelC e he g hg hs u.1 u.2.1 u.2.2)
      ((P,((0 : GW.Space),0))+kernelQRSection qr) := by
    rw [kernelQR_affine_apply]
    exact hAt
  have h := Complex.reCLM.contDiff.contDiffAt.comp qr (hAt'.comp qr ha.contDiffAt)
  simpa only [Function.comp_def,kernelQR_affine_apply,Complex.reCLM_apply,kernelRealQRSlice] using! h

theorem kernelRealQRSlice_iterated_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space), ‖P‖ ≤ 1/4 →
      ∀ k ≤ 3,∀ qr : GW.Space × GW.Space,
      ‖iteratedFDeriv ℝ k (kernelRealQRSlice e he g hg hs P) qr‖ ≤ C := by
  obtain ⟨C,hC,hB⟩ := thresholdKernelC_product_iterated_uniform
  let L := kernelQRSection
  let A := (1+‖L‖)^3
  let M := 1+‖Complex.reCLM‖
  have hA : 0 < A := by dsimp [A]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨C*A*M,by positivity,?_⟩
  intro e he g hg hs P hP k hk qr
  let F := fun u : GW.Space × (GW.Space × GW.Space) => thresholdKernelC e he g hg hs u.1 u.2.1 u.2.2
  let a : GW.Space × (GW.Space × GW.Space) := (P,((0 : GW.Space),0))
  have hpoint (z : GW.Space × GW.Space) : a+L z = (P,z) := kernelQR_affine_apply P z
  have hAt : ContDiffAt ℝ k F (a+L qr) := by
    rw [hpoint]
    exact (thresholdKernelC_contDiffAt e he g hg hs (P,qr) (by linarith)).of_le (by exact_mod_cast hk)
  have hn := iteratedFDeriv_comp_affine_norm_le_at a L F k qr hAt
  have hp : ‖L‖^k ≤ A := by
    dsimp [A]
    interval_cases k <;> norm_num <;>
      nlinarith [norm_nonneg L,sq_nonneg ‖L‖,pow_nonneg (norm_nonneg L) 3]
  have hFN : ‖iteratedFDeriv ℝ k F (a+L qr)‖ ≤ C := by
    rw [hpoint]
    exact hB e he g hg hs k hk (P,qr) hP
  have hpre : ‖iteratedFDeriv ℝ k (fun z => F (a+L z)) qr‖ ≤ C*A :=
    hn.trans (mul_le_mul hFN hp (pow_nonneg (norm_nonneg L) k) hC.le)
  have hd : ContDiffAt ℝ k (fun z : GW.Space × GW.Space => F (a+L z)) qr :=
    hAt.comp qr (contDiffAt_const.add L.contDiff.contDiffAt)
  have hpost := Complex.reCLM.norm_iteratedFDeriv_comp_left
    (f := fun z : GW.Space × GW.Space => F (a+L z)) (x := qr) hd (n := k) le_rfl
  have hf : Complex.reCLM ∘ (fun z => F (a+L z)) = kernelRealQRSlice e he g hg hs P := by
    funext z
    change Complex.reCLM (F (a+L z)) = _
    rw [hpoint]
    rfl
  have hpost' : ‖iteratedFDeriv ℝ k (kernelRealQRSlice e he g hg hs P) qr‖ ≤
      ‖Complex.reCLM‖*‖iteratedFDeriv ℝ k (fun z => F (a+L z)) qr‖ := by
    simp only [Function.comp_def,Complex.reCLM_apply] at hf hpost
    rw [hf] at hpost
    exact hpost
  refine hpost'.trans ((mul_le_mul_of_nonneg_left hpre (norm_nonneg Complex.reCLM)).trans ?_)
  have hNM : ‖Complex.reCLM‖ ≤ M := by dsimp [M]; linarith
  simpa only [mul_comm,mul_left_comm,mul_assoc] using
    mul_le_mul_of_nonneg_right hNM (mul_nonneg hC.le hA.le)

end Froehlich
