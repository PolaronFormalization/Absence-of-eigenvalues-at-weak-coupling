import Froehlich.Nodes.CA03LocalRectangularBounds
import Froehlich.Nodes.KE01PhysicalDerivativeBounds
import Froehlich.Nodes.KE02Vanishing

set_option autoImplicit false
noncomputable section
namespace Froehlich

theorem kernelMomentumDifferences_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space), ‖P‖ ≤ 1/4 →
      (∀ q : GW.Space, |kernelPsi e he g hg hs P q-kernelPsi e he g hg hs 0 q| ≤ C*‖P‖*omega q) ∧
      ∀ q r : GW.Space, |remainderKernel e he g hg hs P q r-remainderKernel e he g hg hs 0 q r| ≤
        C*‖P‖*omega q*omega r := by
  obtain ⟨M,hM,hB⟩ := thresholdKernelC_product_iterated_uniform
  let A := (1+‖rectangularQRInclusion‖)^2
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨4*A*M,by positivity,?_⟩
  intro e he g hg hs P hP
  let F := fun u : GW.Space × (GW.Space × GW.Space) => thresholdKernelC e he g hg hs u.1 u.2.1 u.2.2
  have hF (t : GW.Space × (GW.Space × GW.Space)) (ht : t ∈ rectangularMomentumSlab) :
      ContDiffAt ℝ 3 F t :=
    thresholdKernelC_contDiffAt e he g hg hs t (by
      have ht' : ‖t.1‖ ≤ 1/4 := ht
      linarith)
  have hFB (k : ℕ) (hk : k ≤ 3) (t : GW.Space × (GW.Space × GW.Space))
      (ht : t ∈ rectangularMomentumSlab) : ‖iteratedFDeriv ℝ k F t‖ ≤ M :=
    hB e he g hg hs k hk t ht
  constructor
  · intro q
    have h := norm_rectangular_momentum_q F M hM.le hF hFB P q hP
    have hEq : finiteDifference (P,((0 : GW.Space),0))
        (finiteDifference ((0 : GW.Space),(q,0)) F) 0 =
        ((kernelPsi e he g hg hs P q-kernelPsi e he g hg hs 0 q : ℝ) : ℂ) := by
      simp only [finiteDifference,F,Prod.mk_add_mk,Prod.fst_zero,Prod.snd_zero,zero_add,add_zero,kernelPsi,kernelConstant,
        Complex.ofReal_sub,thresholdKernelC_ofReal_re]
    rw [hEq,Complex.norm_real,Real.norm_eq_abs] at h
    have hcoef : 2*A*M ≤ 4*A*M := by nlinarith [mul_nonneg hA.le hM.le]
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (norm_nonneg P)) (omega_nonneg q))
  · intro q r
    have h := norm_rectangular_momentum_qr F M hM.le hF hFB P q r hP
    have hEq : finiteDifference (P,((0 : GW.Space),0))
        (finiteDifference ((0 : GW.Space),(q,0))
          (finiteDifference ((0 : GW.Space),(0,r)) F)) 0 =
        ((remainderKernel e he g hg hs P q r-remainderKernel e he g hg hs 0 q r : ℝ) : ℂ) := by
      simp only [finiteDifference,F,Prod.mk_add_mk,Prod.fst_zero,Prod.snd_zero,zero_add,add_zero,remainderKernel_double_difference,
        Complex.ofReal_sub,Complex.ofReal_add,thresholdKernelC_ofReal_re]
      ring
    rw [hEq,Complex.norm_real,Real.norm_eq_abs] at h
    exact h

end Froehlich
