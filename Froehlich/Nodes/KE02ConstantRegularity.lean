import Froehlich.Nodes.KE01PhysicalDerivativeBounds
import Froehlich.Nodes.KE01KernelDefinitions
import Froehlich.Nodes.KE01CanonicalNormLocalChain

set_option autoImplicit false
noncomputable section
namespace Froehlich

def kernelZeroSection : GW.Space →L[ℝ] GW.Space × (GW.Space × GW.Space) :=
  (ContinuousLinearMap.id ℝ GW.Space).prod
    ((0 : GW.Space →L[ℝ] GW.Space).prod (0 : GW.Space →L[ℝ] GW.Space))

theorem kernelZeroSection_apply (P : GW.Space) : kernelZeroSection P = (P,(0,0)) := rfl

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

theorem kernelConstant_contDiffAt (P : GW.Space) (hP : ‖P‖ < 1/3) :
    ContDiffAt ℝ 3 (kernelConstant e he g hg hs) P := by
  have hF := thresholdKernelC_contDiffAt e he g hg hs (kernelZeroSection P) hP
  have h := Complex.reCLM.contDiff.contDiffAt.comp P (hF.comp P kernelZeroSection.contDiff.contDiffAt)
  simpa only [Function.comp_def,kernelZeroSection_apply,Complex.reCLM_apply,kernelConstant] using! h

theorem kernelConstant_iterated_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (k : ℕ) (hk : k ≤ 3)
      (P : GW.Space), ‖P‖ ≤ 1/4 →
      ‖iteratedFDeriv ℝ k (kernelConstant e he g hg hs) P‖ ≤ C := by
  obtain ⟨C,hC,hB⟩ := thresholdKernelC_product_iterated_uniform
  let L := kernelZeroSection
  let A := (1+‖L‖)^3
  let M := 1+‖Complex.reCLM‖
  have hA : 0 < A := by dsimp [A]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨C*A*M,by positivity,?_⟩
  intro e he g hg hs k hk P hP
  let F := fun u : GW.Space × (GW.Space × GW.Space) => thresholdKernelC e he g hg hs u.1 u.2.1 u.2.2
  have hAt : ContDiffAt ℝ k F (L P) :=
    (thresholdKernelC_contDiffAt e he g hg hs (L P) (by change ‖P‖ < 1/3; linarith)).of_le (by exact_mod_cast hk)
  have hpre := iteratedFDeriv_comp_linear_norm_le_at L F k P hAt
  have hp : ‖L‖^k ≤ A := by
    dsimp [A]
    interval_cases k <;> norm_num <;>
      nlinarith [norm_nonneg L,sq_nonneg ‖L‖,pow_nonneg (norm_nonneg L) 3]
  have hFN : ‖iteratedFDeriv ℝ k F (L P)‖ ≤ C := hB e he g hg hs k hk (L P) hP
  have hpreN : ‖iteratedFDeriv ℝ k (F ∘ L) P‖ ≤ C*A :=
    hpre.trans (mul_le_mul hFN hp (pow_nonneg (norm_nonneg L) k) hC.le)
  have hpost := Complex.reCLM.norm_iteratedFDeriv_comp_left (x := P)
    (hAt.comp P L.contDiff.contDiffAt) (n := k) le_rfl
  have hf : Complex.reCLM ∘ (F ∘ L) = kernelConstant e he g hg hs := by
    funext p
    rfl
  have hpost' : ‖iteratedFDeriv ℝ k (kernelConstant e he g hg hs) P‖ ≤
      ‖Complex.reCLM‖*‖iteratedFDeriv ℝ k (F ∘ L) P‖ := by
    simpa only [hf] using! hpost
  refine hpost'.trans ((mul_le_mul_of_nonneg_left hpreN (norm_nonneg Complex.reCLM)).trans ?_)
  have hNM : ‖Complex.reCLM‖ ≤ M := by dsimp [M]; linarith
  simpa only [mul_comm,mul_left_comm,mul_assoc] using
    mul_le_mul_of_nonneg_right hNM (mul_nonneg hC.le hA.le)

end Froehlich
