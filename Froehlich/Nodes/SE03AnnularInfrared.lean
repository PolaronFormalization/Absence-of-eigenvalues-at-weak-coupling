import Froehlich.Nodes.SE03AnnularTest
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Classical
namespace Froehlich

/-- The infrared function is truncated only for an annular L2 test. -/
def se03AnnularInfraredRow (g M : ℝ) : GW.Space → ℂ :=
  (se03Annulus M).indicator (fun q => ((g/‖q‖^2 : ℝ) : ℂ))

theorem se03Annulus_measurable (M : ℝ) : MeasurableSet (se03Annulus M) :=
  (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)

theorem se03AnnularInfraredRow_memLp (g M : ℝ) (hM : 1 ≤ M) :
    MemLp (se03AnnularInfraredRow g M) 2 volume := by
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hfinite : volume (se03Annulus M) ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (measure_mono (show se03Annulus M ⊆ Metric.closedBall 0 M from
      fun q hq => by simpa only [Metric.mem_closedBall,dist_zero_right] using hq.2))
    exact measure_closedBall_lt_top
  have hdom : MemLp ((se03Annulus M).indicator (fun _ : GW.Space => |g| * M^2)) 2 volume :=
    memLp_indicator_const 2 (se03Annulus_measurable M).nullMeasurableSet _ (Or.inr hfinite)
  have hm : AEStronglyMeasurable (se03AnnularInfraredRow g M) volume :=
    ((Complex.continuous_ofReal.measurable.comp
      (measurable_const.div (measurable_norm.pow_const 2))).indicator
        (se03Annulus_measurable M)).aestronglyMeasurable
  apply hdom.mono' hm
  apply Filter.Eventually.of_forall
  intro q
  by_cases hq : q ∈ se03Annulus M
  · have hqp : 0 < ‖q‖ := lt_of_lt_of_le (inv_pos.mpr hMp) hq.1
    have hinv : ‖q‖⁻¹ ≤ M := (inv_le_comm₀ hqp hMp).mpr hq.1
    have hs : (‖q‖⁻¹)^2 ≤ M^2 := by nlinarith [inv_nonneg.mpr hqp.le]
    simp only [se03AnnularInfraredRow,Set.indicator_of_mem hq,Complex.norm_real,Real.norm_eq_abs,
      abs_div,abs_pow,abs_norm,div_eq_mul_inv]
    rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg ‖q‖))]
    simpa only [inv_pow] using mul_le_mul_of_nonneg_left hs (abs_nonneg g)
  · simp only [se03AnnularInfraredRow,Set.indicator_of_notMem hq,norm_zero]
    exact le_rfl

/-- Actual L2 annular representative; no global infrared L2 vector is introduced. -/
def se03AnnularInfraredVector (g M : ℝ) (hM : 1 ≤ M) : GW.OnePhonon :=
  (se03AnnularInfraredRow_memLp g M hM).toLp (se03AnnularInfraredRow g M)

theorem se03AnnularInfraredVector_ae (g M : ℝ) (hM : 1 ≤ M) :
    se03AnnularInfraredVector g M hM =ᵐ[volume] se03AnnularInfraredRow g M :=
  (se03AnnularInfraredRow_memLp g M hM).coeFn_toLp

end Froehlich
