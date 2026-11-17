import Froehlich.Nodes.AN01
import Froehlich.Nodes.GW05

/-! The radial majorant for the finite-cutoff Lieb--Yamazaki vectors.
The retained exterior fourth-power estimate supplies its actual L² bound. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Froehlich

def lyRadialTail (g L : ℝ) (k : GW.Space) : ℂ :=
  if L < ‖k‖ then ((g / ‖k‖^2 : ℝ) : ℂ) else 0

theorem lyRadialTail_measurable (g L : ℝ) : Measurable (lyRadialTail g L) := by
  unfold lyRadialTail
  exact Measurable.ite (measurableSet_lt measurable_const measurable_norm)
    (Complex.continuous_ofReal.measurable.comp (measurable_const.div (measurable_norm.pow_const 2))) measurable_const

theorem lyRadialTail_lintegral (g L : ℝ) :
    (∫⁻ k : GW.Space, ENNReal.ofReal (‖lyRadialTail g L k‖^2) ∂volume) =
      GW.Model.coefficientDTailENN (g^2) L := by
  unfold GW.Model.coefficientDTailENN
  rw [← lintegral_indicator (GW.Model.highRegion_measurable L)]
  apply lintegral_congr
  intro k
  by_cases hk : L < ‖k‖
  · rw [Set.indicator_of_mem hk]
    simp only [lyRadialTail, if_pos hk, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      GW.Model.v_sq (sq_nonneg g)]
    congr 1
    rw [div_pow, div_div, ← pow_add, ← pow_mul]
  · rw [Set.indicator_of_notMem hk]
    simp only [lyRadialTail, if_neg hk, norm_zero, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero]

theorem lyRadialTail_memLp (g L : ℝ) (hL : 0 < L) :
    MemLp (lyRadialTail g L) 2 (volume : Measure GW.Space) := by
  have hm : AEStronglyMeasurable (lyRadialTail g L) (volume : Measure GW.Space) :=
    (lyRadialTail_measurable g L).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  refine ⟨hm.norm.pow 2, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mpr
  rw [lyRadialTail_lintegral]
  exact lt_top_iff_ne_top.mpr (GW.Model.coefficientDTailENN_finite (g^2) L (sq_nonneg g) hL)

def lyRadialTailL2 (g L : ℝ) (hL : 0 < L) : GW.OnePhonon :=
  (lyRadialTail_memLp g L hL).toLp _

theorem lyRadialTailL2_ae (g L : ℝ) (hL : 0 < L) :
    lyRadialTailL2 g L hL =ᵐ[volume] lyRadialTail g L :=
  (lyRadialTail_memLp g L hL).coeFn_toLp

theorem lyRadialTailL2_norm_sq (g L : ℝ) (hL : 0 < L) :
    ‖lyRadialTailL2 g L hL‖^2 ≤ 14 * GW.Model.unitBallVolume * g^2 / L := by
  have hB : 0 ≤ 14 * GW.Model.unitBallVolume * g^2 / L :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) GW.Model.unitBallVolume_pos.le)
      (sq_nonneg g)) hL.le
  apply (ENNReal.ofReal_le_ofReal_iff hB).mp
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ), ofReal_integral_eq_lintegral_ofReal
    ((Lp.memLp (lyRadialTailL2 g L hL)).integrable_norm_pow (p := 2) (by norm_num))
    (Eventually.of_forall (fun _ => sq_nonneg _))]
  calc
    _ = ∫⁻ k : GW.Space, ENNReal.ofReal (‖lyRadialTail g L k‖^2) ∂volume :=
      lintegral_congr_ae ((lyRadialTailL2_ae g L hL).mono (fun k hk =>
        congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖^2)) hk))
    _ = GW.Model.coefficientDTailENN (g^2) L := lyRadialTail_lintegral g L
    _ ≤ _ := GW.Model.coefficientDTailENN_bound (g^2) L (sq_nonneg g) hL

end Froehlich
