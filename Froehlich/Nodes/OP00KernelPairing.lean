import Froehlich.Nodes.OP00KernelOperator

set_option autoImplicit false

/-! Absolute product integrability and the literal Fubini pairing formula. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

variable (a : GW.Space → ℝ) (ha : MemLp a 2 volume)
  (k : GW.Space → GW.Space → ℂ) (hk : Measurable (Function.uncurry k))
  (M : ℝ) (hb : ∀ q r, ‖k q r‖ ≤ M*a q*a r)

include ha hk hb in
theorem kernelPairing_integrable (f h : GW.OnePhonon) :
    Integrable (fun z : GW.Space × GW.Space => (starRingEnd ℂ) (f z.1)*(k z.1 z.2*h z.2))
      ((volume : Measure GW.Space).prod volume) := by
  have hi := ((kernelMajorant_product_integrable a ha f).mul_prod
    (kernelMajorant_product_integrable a ha h)).const_mul M
  have hm : AEStronglyMeasurable
      (fun z : GW.Space × GW.Space => (starRingEnd ℂ) (f z.1)*(k z.1 z.2*h z.2))
      ((volume : Measure GW.Space).prod volume) :=
    ((Complex.conjCLE.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)).comp_fst).mul
      (hk.aestronglyMeasurable.mul (Lp.aestronglyMeasurable h).comp_snd)
  apply hi.mono' hm
  exact Filter.Eventually.of_forall (fun z => by
    simp only [norm_mul,RCLike.norm_conj]
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hb z.1 z.2) (norm_nonneg (h z.2))) (norm_nonneg (f z.1))
    exact hh.trans_eq (by ring))

theorem kernelIntegralOperator_inner (ha0 : ∀ q, 0 ≤ a q) (hM : 0 ≤ M) (f h : GW.OnePhonon) :
    ⟪f,kernelIntegralOperator a ha ha0 k hk M hM hb h⟫_ℂ =
      ∫ z : GW.Space × GW.Space, (starRingEnd ℂ) (f z.1)*(k z.1 z.2*h z.2) := by
  rw [L2.inner_def]
  calc
    _ = ∫ q, (starRingEnd ℂ) (f q)*(∫ r, k q r*h r) := by
      apply integral_congr_ae
      filter_upwards [kernelIntegralOperator_ae a ha ha0 k hk M hM hb h] with q hq
      rw [hq]
      simp only [RCLike.inner_apply',kernelRowIntegral]
    _ = ∫ q, ∫ r, (starRingEnd ℂ) (f q)*(k q r*h r) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun q => (integral_const_mul _ _).symm)
    _ = _ := (integral_prod _ (kernelPairing_integrable a ha k hk M hb f h)).symm

end Froehlich
