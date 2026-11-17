import Froehlich.Nodes.GW01
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

/-! OP00: actual scalar kernel rows, before descending to the bounded L2 map. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

def kernelRowIntegral (k : GW.Space → GW.Space → ℂ) (f : GW.OnePhonon) (q : GW.Space) : ℂ :=
  ∫ r, k q r*f r

theorem kernelMajorant_product_integrable (a : GW.Space → ℝ)
    (ha : MemLp a 2 volume) (f : GW.OnePhonon) :
    Integrable (fun r => a r*‖f r‖) := by
  simpa only [Pi.mul_apply] using! ha.integrable_mul (Lp.memLp f).norm

theorem kernelMajorant_cauchy (a : GW.Space → ℝ) (ha : MemLp a 2 volume)
    (f : GW.OnePhonon) : ∫ r, a r*‖f r‖ ≤ ‖ha.toLp a‖*‖f‖ := by
  let hN := (Lp.memLp f).norm
  let A : Lp ℝ 2 (volume : Measure GW.Space) := ha.toLp a
  let B : Lp ℝ 2 (volume : Measure GW.Space) := hN.toLp (fun r => ‖f r‖)
  have hBN : ‖B‖ = (eLpNorm (fun r => ‖f r‖) 2 volume).toReal := by
    simpa only [B] using! Lp.norm_toLp (fun r => ‖f r‖) hN
  have hB : ‖B‖ = ‖f‖ := by
    refine hBN.trans ?_
    have hn : eLpNorm (fun r : GW.Space => ‖f r‖) 2 volume =
        eLpNorm (fun r : GW.Space => f r) 2 volume :=
      eLpNorm_norm (fun r : GW.Space => f r) (Lp.aestronglyMeasurable f)
    exact (congrArg ENNReal.toReal hn).trans (Lp.norm_def f).symm
  have hEq : (∫ r, a r*‖f r‖) = ⟪A,B⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp ha,MemLp.coeFn_toLp hN] with r hr hn
    simpa only [A,B,Real.inner_apply,hr,hn]
  calc
    _ = ⟪A,B⟫_ℝ := hEq
    _ ≤ ‖⟪A,B⟫_ℝ‖ := le_abs_self _
    _ ≤ ‖A‖*‖B‖ := norm_inner_le_norm A B
    _ = _ := by rw [hB]

theorem kernelRowIntegral_aestronglyMeasurable (k : GW.Space → GW.Space → ℂ)
    (hk : Measurable (Function.uncurry k)) (f : GW.OnePhonon) :
    AEStronglyMeasurable (kernelRowIntegral k f) volume := by
  have h : AEStronglyMeasurable (fun z : GW.Space × GW.Space => k z.1 z.2*f z.2)
      ((volume : Measure GW.Space).prod volume) :=
    hk.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f).comp_snd
  exact h.integral_prod_right'

theorem kernelRow_integrable (a : GW.Space → ℝ) (ha : MemLp a 2 volume)
    (k : GW.Space → GW.Space → ℂ) (hk : Measurable (Function.uncurry k)) (M : ℝ)
    (hbound : ∀ q r, ‖k q r‖ ≤ M*a q*a r) (f : GW.OnePhonon) (q : GW.Space) :
    Integrable (fun r => k q r*f r) := by
  have hmajor : Integrable (fun r => (M*a q)*(a r*‖f r‖)) :=
    (kernelMajorant_product_integrable a ha f).const_mul _
  have hmeas : AEStronglyMeasurable (fun r => k q r*f r) volume :=
    (hk.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f)
  apply hmajor.mono' hmeas
  exact Filter.Eventually.of_forall (fun r => by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hbound q r) (norm_nonneg (f r))).trans_eq (by ring))

theorem kernelRowIntegral_norm_le (a : GW.Space → ℝ) (ha : MemLp a 2 volume)
    (k : GW.Space → GW.Space → ℂ) (hk : Measurable (Function.uncurry k)) (M : ℝ)
    (hbound : ∀ q r, ‖k q r‖ ≤ M*a q*a r) (f : GW.OnePhonon) (q : GW.Space) :
    ‖kernelRowIntegral k f q‖ ≤ (M*a q)*(∫ r, a r*‖f r‖) := by
  have hrow := kernelRow_integrable a ha k hk M hbound f q
  have hmajor := (kernelMajorant_product_integrable a ha f).const_mul (M*a q)
  have hnorm (r : GW.Space) : ‖k q r*f r‖ ≤ (M*a q)*(a r*‖f r‖) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hbound q r) (norm_nonneg (f r))).trans_eq (by ring)
  calc
    _ ≤ ∫ r, ‖k q r*f r‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ r, (M*a q)*(a r*‖f r‖) := integral_mono hrow.norm hmajor hnorm
    _ = _ := integral_const_mul _ _

end Froehlich
