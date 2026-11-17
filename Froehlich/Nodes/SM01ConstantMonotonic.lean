import Froehlich.Nodes.KE02
import Froehlich.Nodes.AN03

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Froehlich

/-- Increasing the common KE02 constant preserves all six actual estimates and zeros. -/
theorem KE02FixedReference_mono (C C' e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hCC : C ≤ C') (h : KE02FixedReference C e he g hg hs) :
    KE02FixedReference C' e he g hg hs := by
  refine ⟨?_,h.2⟩
  intro P hP
  obtain ⟨hc,hpsi,hpsid,hF,hFd,hDer⟩ := h.1 P hP
  refine ⟨hc.trans (mul_le_mul_of_nonneg_right hCC (sq_nonneg _)),?_,?_,?_,?_,?_⟩
  · intro q
    exact (hpsi q).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC (omega_nonneg q))
      (add_nonneg (omega_nonneg q) (norm_nonneg P)))
  · intro q
    exact (hpsid q).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC (norm_nonneg P)) (omega_nonneg q))
  · intro q r
    exact (hF q r).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC (omega_nonneg q)) (omega_nonneg r))
  · intro q r
    exact (hFd q r).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC (norm_nonneg P))
        (omega_nonneg q)) (omega_nonneg r))
  · intro q r
    exact (hDer q r).trans (mul_le_mul_of_nonneg_right hCC (omega_nonneg r))

/-- The three literal AN03 bounds with one numerical constant.
Only the unweighted convolution excludes zero momentum. -/
def SM01IntegralConstant (I : ℝ) : Prop :=
  (∀ P : GW.Space, ‖P‖ ≤ 1/4 →
    (Integrable (weightedMuDensity P) volume ∧ (∫ q : GW.Space,weightedMuDensity P q) ≤ I) ∧
    (Integrable (weightedMuDifference P) volume ∧ (∫ q : GW.Space,weightedMuDifference P q) ≤ I*‖P‖)) ∧
  ∀ P : GW.Space, P ≠ 0 →
    Integrable (muDensity P) volume ∧ (∫ q : GW.Space,muDensity P q) ≤ I/‖P‖

theorem SM01IntegralConstant_mono (I I' : ℝ) (hII : I ≤ I')
    (h : SM01IntegralConstant I) : SM01IntegralConstant I' := by
  constructor
  · intro P hP
    obtain ⟨hw,hd⟩ := h.1 P hP
    exact ⟨⟨hw.1,hw.2.trans hII⟩,
      ⟨hd.1,hd.2.trans (mul_le_mul_of_nonneg_right hII (norm_nonneg P))⟩⟩
  · intro P hP
    have hu := h.2 P hP
    exact ⟨hu.1,hu.2.trans (div_le_div_of_nonneg_right hII (norm_nonneg P))⟩

theorem sm01_integralConstant_exists : ∃ I : ℝ, 0 < I ∧ SM01IntegralConstant I :=
  moving_singularity_estimates

end Froehlich
