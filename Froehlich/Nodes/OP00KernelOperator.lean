import Froehlich.Nodes.OP00KernelRows

set_option autoImplicit false

/-! The actual one-particle L2 operator for a global product majorant.
Nonnegativity of the majorant constant is an internal construction interface. -/
noncomputable section
open MeasureTheory
namespace Froehlich

variable (a : GW.Space → ℝ) (ha : MemLp a 2 volume) (ha0 : ∀ q, 0 ≤ a q)
  (k : GW.Space → GW.Space → ℂ) (hk : Measurable (Function.uncurry k))
  (M : ℝ) (hM : 0 ≤ M) (hb : ∀ q r, ‖k q r‖ ≤ M*a q*a r)

include ha hk hb in
theorem kernelRowIntegral_memLp (f : GW.OnePhonon) : MemLp (kernelRowIntegral k f) 2 volume := by
  apply (ha.const_mul (M*(∫ r, a r*‖f r‖))).mono'
    (kernelRowIntegral_aestronglyMeasurable k hk f)
  exact Filter.Eventually.of_forall (fun q =>
    (kernelRowIntegral_norm_le a ha k hk M hb f q).trans_eq (by ring))

def kernelIntegralVector (f : GW.OnePhonon) : GW.OnePhonon :=
  (kernelRowIntegral_memLp a ha k hk M hb f).toLp (kernelRowIntegral k f)

theorem kernelIntegralVector_ae (f : GW.OnePhonon) :
    kernelIntegralVector a ha k hk M hb f =ᵐ[volume] kernelRowIntegral k f :=
  MemLp.coeFn_toLp _

include ha0 hM in
theorem kernelIntegralVector_norm_le (f : GW.OnePhonon) :
    ‖kernelIntegralVector a ha k hk M hb f‖ ≤ (M*‖ha.toLp a‖^2)*‖f‖ := by
  have h1 : ‖kernelIntegralVector a ha k hk M hb f‖ ≤
      (M*(∫ r, a r*‖f r‖))*‖ha.toLp a‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [kernelIntegralVector_ae a ha k hk M hb f,MemLp.coeFn_toLp ha] with q hq haq
    rw [hq,haq,Real.norm_eq_abs,abs_of_nonneg (ha0 q)]
    exact (kernelRowIntegral_norm_le a ha k hk M hb f q).trans_eq (by ring)
  have h2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (kernelMajorant_cauchy a ha f) hM) (norm_nonneg (ha.toLp a))
  exact h1.trans (h2.trans_eq (by ring))

private theorem kernelIntegralVector_add (f h : GW.OnePhonon) :
    kernelIntegralVector a ha k hk M hb (f+h) =
      kernelIntegralVector a ha k hk M hb f+kernelIntegralVector a ha k hk M hb h := by
  apply Lp.ext
  filter_upwards [kernelIntegralVector_ae a ha k hk M hb (f+h),
    kernelIntegralVector_ae a ha k hk M hb f,kernelIntegralVector_ae a ha k hk M hb h,
    Lp.coeFn_add (kernelIntegralVector a ha k hk M hb f) (kernelIntegralVector a ha k hk M hb h)] with q hq hf hh hadd
  rw [hq,hadd,Pi.add_apply,hf,hh]
  unfold kernelRowIntegral
  have heq : (fun r => k q r*(f+h) r) =ᵐ[volume] (fun r => k q r*f r+k q r*h r) := by
    filter_upwards [Lp.coeFn_add f h] with r hr
    rw [hr,Pi.add_apply,mul_add]
  rw [integral_congr_ae heq,integral_add
    (kernelRow_integrable a ha k hk M hb f q) (kernelRow_integrable a ha k hk M hb h q)]

private theorem kernelIntegralVector_smul (c : ℂ) (f : GW.OnePhonon) :
    kernelIntegralVector a ha k hk M hb (c • f) = c • kernelIntegralVector a ha k hk M hb f := by
  apply Lp.ext
  filter_upwards [kernelIntegralVector_ae a ha k hk M hb (c • f),
    kernelIntegralVector_ae a ha k hk M hb f,
    Lp.coeFn_smul c (kernelIntegralVector a ha k hk M hb f)] with q hq hf hsmul
  rw [hq,hsmul,Pi.smul_apply,hf]
  unfold kernelRowIntegral
  have heq : (fun r => k q r*(c • f) r) =ᵐ[volume] (fun r => c*(k q r*f r)) := by
    filter_upwards [Lp.coeFn_smul c f] with r hr
    rw [hr,Pi.smul_apply]
    change k q r*(c*f r) = c*(k q r*f r)
    ring
  rw [integral_congr_ae heq,integral_const_mul]
  rfl

def kernelIntegralLinearMap : GW.OnePhonon →ₗ[ℂ] GW.OnePhonon where
  toFun := kernelIntegralVector a ha k hk M hb
  map_add' := kernelIntegralVector_add a ha k hk M hb
  map_smul' := kernelIntegralVector_smul a ha k hk M hb

def kernelIntegralOperator : GW.OnePhonon →L[ℂ] GW.OnePhonon :=
  (kernelIntegralLinearMap a ha k hk M hb).mkContinuous (M*‖ha.toLp a‖^2)
    (kernelIntegralVector_norm_le a ha ha0 k hk M hM hb)

theorem kernelIntegralOperator_ae (f : GW.OnePhonon) :
    kernelIntegralOperator a ha ha0 k hk M hM hb f =ᵐ[volume] kernelRowIntegral k f :=
  kernelIntegralVector_ae a ha k hk M hb f

theorem kernelIntegralOperator_norm_le :
    ‖kernelIntegralOperator a ha ha0 k hk M hM hb‖ ≤ M*‖ha.toLp a‖^2 := by
  exact LinearMap.mkContinuous_norm_le _ (mul_nonneg hM (sq_nonneg _))
    (kernelIntegralVector_norm_le a ha ha0 k hk M hM hb)

end Froehlich
