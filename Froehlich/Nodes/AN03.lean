import Froehlich.Nodes.AN01
import Froehlich.Nodes.AN02

/-! AN03 (`lem:singular`): literal moving singularity weights, the source's
three integral estimates with one common constant, and their weighted-moment
and signed complex-source L² consequences. -/

noncomputable section
open MeasureTheory Metric Filter
open scoped ENNReal

namespace Froehlich

def omega (q : GW.Space) : ℝ := min ‖q‖ 1

def muDensity (P q : GW.Space) : ℝ := 1 / (‖q‖ ^ 2 * ‖q + P‖ ^ 2)

def wDensity (P q : GW.Space) : ℝ := 1 / (‖q‖ * ‖q + P‖)

theorem omega_nonneg (q : GW.Space) : 0 ≤ omega q := le_min (norm_nonneg q) zero_le_one
theorem omega_le_norm (q : GW.Space) : omega q ≤ ‖q‖ := min_le_left _ _
theorem omega_le_one (q : GW.Space) : omega q ≤ 1 := min_le_right _ _

theorem omega_measurable : Measurable omega := measurable_norm.min measurable_const

theorem muDensity_nonneg (P q : GW.Space) : 0 ≤ muDensity P q := by
  unfold muDensity
  positivity

theorem wDensity_nonneg (P q : GW.Space) : 0 ≤ wDensity P q := by
  unfold wDensity
  positivity

theorem muDensity_measurable (P : GW.Space) : Measurable (muDensity P) := by
  unfold muDensity
  fun_prop

theorem wDensity_measurable (P : GW.Space) : Measurable (wDensity P) := by
  unfold wDensity
  fun_prop

@[simp] theorem muDensity_zero (P : GW.Space) : muDensity P 0 = 0 := by simp [muDensity]
@[simp] theorem muDensity_neg (P : GW.Space) : muDensity P (-P) = 0 := by simp [muDensity]
@[simp] theorem wDensity_zero (P : GW.Space) : wDensity P 0 = 0 := by simp [wDensity]
@[simp] theorem wDensity_neg (P : GW.Space) : wDensity P (-P) = 0 := by simp [wDensity]

theorem wDensity_sq (P q : GW.Space) : wDensity P q ^ 2 = muDensity P q := by
  simp only [wDensity, muDensity, div_pow, one_pow, mul_pow]

theorem moving_outer_distance (P q : GW.Space) (h : 2 * ‖P‖ ≤ ‖q‖) :
    ‖q‖ / 2 ≤ ‖q + P‖ := by
  have hs := norm_sub_norm_le q (-P)
  simp only [norm_neg, sub_neg_eq_add] at hs
  linarith

theorem muDensity_outer_majorant (P q : GW.Space) (h : 2 * ‖P‖ ≤ ‖q‖) :
    muDensity P q ≤ 4 * ‖q‖ ^ (-(4 : ℝ)) := by
  by_cases hq : q = 0
  · simp [hq]
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hb := moving_outer_distance P q h
  have hbpos : 0 < ‖q + P‖ := by linarith
  have hsq : ‖q‖ ^ 2 ≤ 4 * ‖q + P‖ ^ 2 := by nlinarith [norm_nonneg (q + P)]
  rw [Real.rpow_neg (norm_nonneg q), Real.rpow_ofNat]
  change 1 / (‖q‖ ^ 2 * ‖q + P‖ ^ 2) ≤ 4 / ‖q‖ ^ 4
  apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hn) (sq_pos_of_pos hbpos)) (pow_pos hn 4)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg ‖q‖)]

theorem muDensity_outer_difference (P q : GW.Space) (h : 2 * ‖P‖ ≤ ‖q‖) :
    |muDensity P q - muDensity 0 q| ≤ 10 * ‖P‖ * ‖q‖ ^ (-(5 : ℝ)) := by
  by_cases hq : q = 0
  · simp [hq]
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hb := moving_outer_distance P q h
  have hbpos : 0 < ‖q + P‖ := by linarith
  have hab : |‖q‖ - ‖q + P‖| ≤ ‖P‖ := by
    simpa only [sub_add_cancel_left, norm_neg] using abs_norm_sub_norm_le q (q + P)
  have hsum : ‖q‖ + ‖q + P‖ ≤ (5 / 2 : ℝ) * ‖q‖ := by
    have hu := norm_add_le q P
    linarith
  have hnum : |‖q‖ ^ 2 - ‖q + P‖ ^ 2| ≤ (5 / 2 : ℝ) * ‖P‖ * ‖q‖ := by
    have he : ‖q‖ ^ 2 - ‖q + P‖ ^ 2 = (‖q‖ - ‖q + P‖) * (‖q‖ + ‖q + P‖) := by ring
    rw [he, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    have hm := mul_le_mul hab hsum (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg P)
    nlinarith
  have hdiff : muDensity P q - muDensity 0 q =
      (‖q‖ ^ 2 - ‖q + P‖ ^ 2) / (‖q‖ ^ 4 * ‖q + P‖ ^ 2) := by
    simp only [muDensity, add_zero]
    field_simp [ne_of_gt hn, ne_of_gt hbpos]
  have hden : 0 < ‖q‖ ^ 4 * ‖q + P‖ ^ 2 := by positivity
  rw [hdiff, abs_div, abs_of_pos hden, Real.rpow_neg (norm_nonneg q), Real.rpow_ofNat]
  have hsq : ‖q‖ ^ 2 ≤ 4 * ‖q + P‖ ^ 2 := by nlinarith [norm_nonneg (q + P)]
  calc
    _ ≤ ((5 / 2 : ℝ) * ‖P‖ * ‖q‖) / (‖q‖ ^ 4 * ‖q + P‖ ^ 2) :=
      div_le_div_of_nonneg_right hnum hden.le
    _ ≤ (10 * ‖P‖) / ‖q‖ ^ 5 := by
      apply (div_le_div_iff₀ hden (pow_pos hn 5)).mpr
      have hm := mul_le_mul_of_nonneg_left hsq
        (show 0 ≤ (5 / 2 : ℝ) * ‖P‖ * ‖q‖ ^ 4 by positivity)
      nlinarith
    _ = 10 * ‖P‖ * (‖q‖ ^ 5)⁻¹ := by rw [div_eq_mul_inv]

theorem omega_outer_comparison (P q : GW.Space) (hP : ‖P‖ ≤ 1 / 4)
    (h : 2 * ‖P‖ ≤ ‖q‖) : omega q + ‖P‖ ≤ (3 / 2 : ℝ) * omega q := by
  by_cases hq : ‖q‖ ≤ 1
  · rw [omega, min_eq_left hq]
    linarith
  · rw [omega, min_eq_right (le_of_not_ge hq)]
    linarith

/-- The exact dilation used to reduce local estimates to a unit shift. -/
theorem muDensity_dilation (a : ℝ) (ha : 0 < a) (P q : GW.Space) :
    muDensity (a • P) (a • q) = (a ^ 4)⁻¹ * muDensity P q := by
  simp only [muDensity, ← smul_add, norm_smul, Real.norm_eq_abs, abs_of_pos ha,
    mul_pow, div_eq_mul_inv, mul_inv_rev, one_mul, ← inv_pow]
  ring

theorem muDensity_swap (P q : GW.Space) : muDensity P q = muDensity (-P) (q + P) := by
  simp only [muDensity, add_neg_cancel_right, mul_comm]

theorem muDensity_unit_near_zero (P q : GW.Space) (hP : ‖P‖ = 1)
    (hq : ‖q‖ ≤ 1 / 4) : muDensity P q ≤ 4 * ‖q‖ ^ (-(2 : ℝ)) := by
  by_cases hzero : q = 0
  · simp [hzero]
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hzero
  have hs := norm_sub_norm_le P (-q)
  simp only [hP, norm_neg, sub_neg_eq_add, add_comm P q] at hs
  have hb : 1 / 2 ≤ ‖q + P‖ := by linarith
  have hbpos : 0 < ‖q + P‖ := by linarith
  have hsq : 1 ≤ 4 * ‖q + P‖ ^ 2 := by nlinarith [norm_nonneg (q + P)]
  rw [Real.rpow_neg (norm_nonneg q), Real.rpow_ofNat]
  change 1 / (‖q‖ ^ 2 * ‖q + P‖ ^ 2) ≤ 4 / ‖q‖ ^ 2
  apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hn) (sq_pos_of_pos hbpos)) (sq_pos_of_pos hn)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg ‖q‖)]

theorem muDensity_unit_near_shift (P q : GW.Space) (hP : ‖P‖ = 1)
    (hq : ‖q + P‖ ≤ 1 / 4) : muDensity P q ≤ 4 * ‖q + P‖ ^ (-(2 : ℝ)) := by
  rw [muDensity_swap]
  exact muDensity_unit_near_zero (-P) (q + P) (by simpa only [norm_neg] using hP) hq

theorem muDensity_unit_middle (P q : GW.Space)
    (ha : 1 / 4 ≤ ‖q‖) (hb : 1 / 4 ≤ ‖q + P‖) : muDensity P q ≤ 256 := by
  have hapos : 0 < ‖q‖ := by linarith
  have hbpos : 0 < ‖q + P‖ := by linarith
  have h₁ : 1 ≤ 16 * ‖q‖ ^ 2 := by nlinarith [norm_nonneg q]
  have h₂ : 1 ≤ 16 * ‖q + P‖ ^ 2 := by nlinarith [norm_nonneg (q + P)]
  have hh := mul_le_mul h₁ h₂ (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
  unfold muDensity
  apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hapos) (sq_pos_of_pos hbpos))).mpr
  nlinarith

theorem muDensity_unit_first_integral (P : GW.Space) (hP : ‖P‖ = 1) :
    (∫⁻ q : GW.Space in closedBall 0 (1 / 4 : ℝ), ENNReal.ofReal (muDensity P q)) ≤
      ENNReal.ofReal (7 * GW.Model.unitBallVolume) := by
  have hm : (∫⁻ q : GW.Space in closedBall 0 (1 / 4 : ℝ), ENNReal.ofReal (muDensity P q)) ≤
      ENNReal.ofReal 4 * ∫⁻ q : GW.Space in closedBall 0 (1 / 4 : ℝ),
        ENNReal.ofReal (‖q‖ ^ (-(2 : ℝ))) := by
    have h := setLIntegral_mono' (μ := (volume : Measure GW.Space))
      (s := closedBall 0 (1 / 4 : ℝ))
      (f := fun q => ENNReal.ofReal (muDensity P q))
      (g := fun q => ENNReal.ofReal 4 * ENNReal.ofReal (‖q‖ ^ (-(2 : ℝ)))) measurableSet_closedBall
      (fun q hq => by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        exact ENNReal.ofReal_le_ofReal (muDensity_unit_near_zero P q hP (mem_closedBall_zero_iff.mp hq)))
    rwa [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  have hb := inverse_square_closedBall_bound (1 / 4) (by norm_num)
  have ht : ENNReal.ofReal 4 * (∫⁻ q : GW.Space in closedBall 0 (1 / 4 : ℝ),
      ENNReal.ofReal (‖q‖ ^ (-(2 : ℝ)))) ≤
      ENNReal.ofReal 4 * ENNReal.ofReal (7 * GW.Model.unitBallVolume * (1 / 4)) := by
    simpa only [mul_comm] using mul_le_mul_left hb (ENNReal.ofReal 4)
  apply (hm.trans ht).trans_eq
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  congr 1
  ring

theorem muDensity_unit_second_integral (P : GW.Space) (hP : ‖P‖ = 1) :
    (∫⁻ q : GW.Space in (fun q : GW.Space => q + P) ⁻¹' closedBall 0 (1 / 4 : ℝ),
      ENNReal.ofReal (muDensity P q)) ≤ ENNReal.ofReal (7 * GW.Model.unitBallVolume) := by
  have hs : MeasurableSet ((fun q : GW.Space => q + P) ⁻¹' closedBall 0 (1 / 4 : ℝ)) :=
    measurableSet_closedBall.preimage (measurable_id.add_const P)
  have hm : (∫⁻ q : GW.Space in (fun q : GW.Space => q + P) ⁻¹' closedBall 0 (1 / 4 : ℝ),
      ENNReal.ofReal (muDensity P q)) ≤
      ENNReal.ofReal 4 * ∫⁻ q : GW.Space in closedBall 0 (1 / 4 : ℝ),
        ENNReal.ofReal (‖q‖ ^ (-(2 : ℝ))) := by
    have h := setLIntegral_mono' (μ := (volume : Measure GW.Space)) hs (fun q hq =>
      show ENNReal.ofReal (muDensity P q) ≤
        ENNReal.ofReal 4 * ENNReal.ofReal (‖q + P‖ ^ (-(2 : ℝ))) from by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        exact ENNReal.ofReal_le_ofReal (muDensity_unit_near_shift P q hP (mem_closedBall_zero_iff.mp hq)))
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
    have ht := (space_translation_preserving P).setLIntegral_comp_preimage
      (s := closedBall 0 (1 / 4 : ℝ)) measurableSet_closedBall
      (measurable_norm.pow_const (-(2 : ℝ))).ennreal_ofReal
    rwa [ht] at h
  have hb := inverse_square_closedBall_bound (1 / 4) (by norm_num)
  have ht : ENNReal.ofReal 4 * (∫⁻ q : GW.Space in closedBall 0 (1 / 4 : ℝ),
      ENNReal.ofReal (‖q‖ ^ (-(2 : ℝ)))) ≤
      ENNReal.ofReal 4 * ENNReal.ofReal (7 * GW.Model.unitBallVolume * (1 / 4)) := by
    simpa only [mul_comm] using mul_le_mul_left hb (ENNReal.ofReal 4)
  apply (hm.trans ht).trans_eq
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  congr 1
  ring

def muUnitMiddleRegion (P : GW.Space) : Set GW.Space :=
  closedBall 0 (2 : ℝ) \ (closedBall 0 (1 / 4 : ℝ) ∪
    (fun q : GW.Space => q + P) ⁻¹' closedBall 0 (1 / 4 : ℝ))

theorem muDensity_unit_middle_integral (P : GW.Space) :
    (∫⁻ q : GW.Space in muUnitMiddleRegion P, ENNReal.ofReal (muDensity P q)) ≤
      ENNReal.ofReal (2048 * GW.Model.unitBallVolume) := by
  have hs : MeasurableSet (muUnitMiddleRegion P) :=
    measurableSet_closedBall.diff (measurableSet_closedBall.union
      (measurableSet_closedBall.preimage (measurable_id.add_const P)))
  have hm : (∫⁻ q : GW.Space in muUnitMiddleRegion P, ENNReal.ofReal (muDensity P q)) ≤
      ENNReal.ofReal 256 * volume (muUnitMiddleRegion P) := by
    have h := setLIntegral_mono' (μ := (volume : Measure GW.Space)) hs (fun q hq =>
      show ENNReal.ofReal (muDensity P q) ≤ ENNReal.ofReal 256 from by
        have ha : 1 / 4 ≤ ‖q‖ := by
          by_contra hn
          exact hq.2 (Or.inl (mem_closedBall_zero_iff.mpr (le_of_lt (lt_of_not_ge hn))))
        have hb : 1 / 4 ≤ ‖q + P‖ := by
          by_contra hn
          exact hq.2 (Or.inr (mem_closedBall_zero_iff.mpr (le_of_lt (lt_of_not_ge hn))))
        exact ENNReal.ofReal_le_ofReal (muDensity_unit_middle P q ha hb))
    rwa [lintegral_const, Measure.restrict_apply_univ] at h
  have hμ : volume (muUnitMiddleRegion P) ≤ volume (closedBall (0 : GW.Space) (2 : ℝ)) :=
    measure_mono Set.sdiff_subset
  have ht : ENNReal.ofReal 256 * volume (muUnitMiddleRegion P) ≤
      ENNReal.ofReal 256 * volume (closedBall (0 : GW.Space) (2 : ℝ)) := by
    simpa only [mul_comm] using mul_le_mul_left hμ (ENNReal.ofReal 256)
  apply (hm.trans ht).trans_eq
  rw [GW.Model.spaceClosedBallVolume _ (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 256)]
  congr 1
  ring

theorem muDensity_unit_outer_integral (P : GW.Space) (hP : ‖P‖ = 1) :
    (∫⁻ q : GW.Space in {q | 2 < ‖q‖}, ENNReal.ofReal (muDensity P q)) ≤
      ENNReal.ofReal (28 * GW.Model.unitBallVolume) := by
  have hm : (∫⁻ q : GW.Space in {q | 2 < ‖q‖}, ENNReal.ofReal (muDensity P q)) ≤
      ENNReal.ofReal 4 * ∫⁻ q : GW.Space in {q | 2 < ‖q‖}, ENNReal.ofReal (‖q‖ ^ (-(4 : ℝ))) := by
    have h := setLIntegral_mono' (μ := (volume : Measure GW.Space))
      (s := {q : GW.Space | 2 < ‖q‖}) (measurableSet_lt measurable_const measurable_norm)
      (fun q hq => show ENNReal.ofReal (muDensity P q) ≤
        ENNReal.ofReal 4 * ENNReal.ofReal (‖q‖ ^ (-(4 : ℝ))) from by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        apply ENNReal.ofReal_le_ofReal
        apply muDensity_outer_majorant
        have hh : (2 : ℝ) < ‖q‖ := hq
        rw [hP]
        linarith)
    rwa [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  have hb := GW.Model.exteriorPowerIntegral_four_bound (by norm_num : (0 : ℝ) < 2)
  have ht : ENNReal.ofReal 4 * GW.Model.exteriorPowerIntegral 4 2 ≤
      ENNReal.ofReal 4 * ENNReal.ofReal (14 * GW.Model.unitBallVolume / 2) := by
    simpa only [mul_comm] using mul_le_mul_left hb (ENNReal.ofReal 4)
  calc
    _ ≤ ENNReal.ofReal 4 * (∫⁻ q : GW.Space in {q | 2 < ‖q‖},
        ENNReal.ofReal (‖q‖ ^ (-(4 : ℝ)))) := hm
    _ = ENNReal.ofReal 4 * GW.Model.exteriorPowerIntegral 4 2 := by
      unfold GW.Model.exteriorPowerIntegral GW.Model.radialPowerIntegral
      rfl
    _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal (14 * GW.Model.unitBallVolume / 2) := ht
    _ = ENNReal.ofReal (28 * GW.Model.unitBallVolume) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      congr 1
      ring

theorem muDensity_unit_lintegral (P : GW.Space) (hP : ‖P‖ = 1) :
    (∫⁻ q : GW.Space, ENNReal.ofReal (muDensity P q)) ≤
      ENNReal.ofReal (3000 * GW.Model.unitBallVolume) := by
  let A : Set GW.Space := closedBall 0 (1 / 4 : ℝ)
  let B : Set GW.Space := (fun q : GW.Space => q + P) ⁻¹' closedBall 0 (1 / 4 : ℝ)
  let C : Set GW.Space := muUnitMiddleRegion P
  let D : Set GW.Space := {q | 2 < ‖q‖}
  let f : GW.Space → ℝ≥0∞ := fun q => ENNReal.ofReal (muDensity P q)
  have hcover : Set.univ ⊆ A ∪ B ∪ C ∪ D := by
    intro q _
    by_cases ha : q ∈ A
    · exact Or.inl (Or.inl (Or.inl ha))
    by_cases hb : q ∈ B
    · exact Or.inl (Or.inl (Or.inr hb))
    by_cases hc : ‖q‖ ≤ 2
    · exact Or.inl (Or.inr ⟨mem_closedBall_zero_iff.mpr hc, not_or.mpr ⟨ha,hb⟩⟩)
    · exact Or.inr (lt_of_not_ge hc)
  have hcoverInt : (∫⁻ q, f q ∂(volume : Measure GW.Space)) ≤
      ((∫⁻ q in A, f q ∂volume) + ∫⁻ q in B, f q ∂volume) +
        (∫⁻ q in C, f q ∂volume) + ∫⁻ q in D, f q ∂volume := by
    calc
      _ = ∫⁻ q in Set.univ, f q ∂volume := by simp only [Measure.restrict_univ]
      _ ≤ ∫⁻ q in A ∪ B ∪ C ∪ D, f q ∂volume :=
        lintegral_mono_set (μ := (volume : Measure GW.Space)) (f := f) hcover
      _ ≤ (∫⁻ q in A ∪ B ∪ C, f q ∂volume) + ∫⁻ q in D, f q ∂volume :=
        lintegral_union_le (μ := (volume : Measure GW.Space)) f (A ∪ B ∪ C) D
      _ ≤ ((∫⁻ q in A ∪ B, f q ∂volume) + ∫⁻ q in C, f q ∂volume) + ∫⁻ q in D, f q ∂volume :=
        add_le_add (lintegral_union_le (μ := (volume : Measure GW.Space)) f (A ∪ B) C) (le_refl _)
      _ ≤ _ := add_le_add (add_le_add
        (lintegral_union_le (μ := (volume : Measure GW.Space)) f A B) (le_refl _)) (le_refl _)
  have hb := add_le_add
    (add_le_add (add_le_add (muDensity_unit_first_integral P hP)
      (muDensity_unit_second_integral P hP)) (muDensity_unit_middle_integral P))
      (muDensity_unit_outer_integral P hP)
  apply (hcoverInt.trans hb).trans
  have hv : 0 ≤ GW.Model.unitBallVolume := GW.Model.unitBallVolume_pos.le
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith

theorem muDensity_lintegral (P : GW.Space) (hP : P ≠ 0) :
    (∫⁻ q : GW.Space, ENNReal.ofReal (muDensity P q)) ≤
      ENNReal.ofReal (3000 * GW.Model.unitBallVolume / ‖P‖) := by
  let r : ℝ := ‖P‖
  let ν : GW.Space := r⁻¹ • P
  have hr : 0 < r := norm_pos_iff.mpr hP
  have hν : ‖ν‖ = 1 := by
    change ‖r⁻¹ • P‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact inv_mul_cancel₀ (ne_of_gt hr)
  have hPν : r • ν = P := by
    change r • (r⁻¹ • P) = P
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
  have hd (q : GW.Space) : muDensity P (r • q) = (r ^ 4)⁻¹ * muDensity ν q := by
    simpa only [hPν] using muDensity_dilation r hr ν q
  have hc : 0 ≤ (r ^ 4)⁻¹ := by positivity
  have hs : (∫⁻ q : GW.Space, ENNReal.ofReal (muDensity P (r • q))) =
      ENNReal.ofReal ((r ^ 4)⁻¹) * ∫⁻ q : GW.Space, ENNReal.ofReal (muDensity ν q) := by
    simp_rw [hd, ENNReal.ofReal_mul hc]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hj := space_lintegral_dilation (fun q => ENNReal.ofReal (muDensity P q))
    (muDensity_measurable P).ennreal_ofReal r (ne_of_gt hr)
  rw [abs_of_pos hr] at hj
  have hcancel : ENNReal.ofReal (r ^ 3) * ENNReal.ofReal ((r ^ 3)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hr.le _), mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt hr))]
    norm_num
  have he : (∫⁻ q : GW.Space, ENNReal.ofReal (muDensity P q)) =
      ENNReal.ofReal (r⁻¹) * ∫⁻ q : GW.Space, ENNReal.ofReal (muDensity ν q) := by
    calc
      _ = 1 * ∫⁻ q : GW.Space, ENNReal.ofReal (muDensity P q) := (one_mul _).symm
      _ = (ENNReal.ofReal (r ^ 3) * ENNReal.ofReal ((r ^ 3)⁻¹)) *
          ∫⁻ q : GW.Space, ENNReal.ofReal (muDensity P q) := by rw [hcancel]
      _ = ENNReal.ofReal (r ^ 3) *
          ∫⁻ q : GW.Space, ENNReal.ofReal (muDensity P (r • q)) := by rw [hj, mul_assoc]
      _ = ENNReal.ofReal (r ^ 3) * (ENNReal.ofReal ((r ^ 4)⁻¹) *
          ∫⁻ q : GW.Space, ENNReal.ofReal (muDensity ν q)) := by rw [hs]
      _ = ENNReal.ofReal (r⁻¹) * ∫⁻ q : GW.Space, ENNReal.ofReal (muDensity ν q) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hr.le _)]
        congr 2
        field_simp [ne_of_gt hr]
  rw [he]
  have hu := muDensity_unit_lintegral ν hν
  have ht : ENNReal.ofReal (r⁻¹) * (∫⁻ q : GW.Space, ENNReal.ofReal (muDensity ν q)) ≤
      ENNReal.ofReal (r⁻¹) * ENNReal.ofReal (3000 * GW.Model.unitBallVolume) := by
    simpa only [mul_comm] using mul_le_mul_left hu (ENNReal.ofReal (r⁻¹))
  apply ht.trans_eq
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
  congr 1
  dsimp [r]
  ring

theorem muDensity_integrable_bound (P : GW.Space) (hP : P ≠ 0) :
    Integrable (muDensity P) volume ∧
      (∫ q : GW.Space, muDensity P q) ≤ 3000 * GW.Model.unitBallVolume / ‖P‖ := by
  have hm : AEStronglyMeasurable (muDensity P) volume := (muDensity_measurable P).aestronglyMeasurable
  have hn : 0 ≤ᵐ[volume] muDensity P := Eventually.of_forall (muDensity_nonneg P)
  have h := muDensity_lintegral P hP
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal hn).mpr (h.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hn hm]
  simpa only [ENNReal.toReal_ofReal (show 0 ≤ 3000 * GW.Model.unitBallVolume / ‖P‖ from
    div_nonneg (mul_nonneg (by norm_num) GW.Model.unitBallVolume_pos.le) (norm_nonneg P))]
    using ENNReal.toReal_mono ENNReal.ofReal_ne_top h

/-- The source's common integrable outer majorant: inverse square at the
origin and an integrable inverse power at infinity. -/
def radialEnvelope (β : ℝ) (q : GW.Space) : ℝ :=
  if ‖q‖ ≤ 1 then ‖q‖ ^ (-(2 : ℝ)) else ‖q‖ ^ (-β)

theorem radialEnvelope_nonneg (β : ℝ) (q : GW.Space) : 0 ≤ radialEnvelope β q := by
  unfold radialEnvelope
  split_ifs <;> exact Real.rpow_nonneg (norm_nonneg q) _

theorem radialEnvelope_measurable (β : ℝ) : Measurable (radialEnvelope β) := by
  unfold radialEnvelope
  exact Measurable.ite (measurableSet_le measurable_norm measurable_const)
    (measurable_norm.pow_const _) (measurable_norm.pow_const _)

theorem radialEnvelope_lintegral (β : ℝ) (hβ : 3 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ (∫⁻ q : GW.Space, ENNReal.ofReal (radialEnvelope β q)) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hbound⟩ := exterior_power_bound β hβ
  have hv : 0 ≤ GW.Model.unitBallVolume := GW.Model.unitBallVolume_pos.le
  refine ⟨7 * GW.Model.unitBallVolume + C, by positivity, ?_⟩
  have hi : (∫⁻ q : GW.Space in closedBall 0 (1 : ℝ),
      ENNReal.ofReal (radialEnvelope β q)) ≤ ENNReal.ofReal (7 * GW.Model.unitBallVolume) := by
    have hm := setLIntegral_mono' (μ := (volume : Measure GW.Space))
      (s := closedBall (0 : GW.Space) (1 : ℝ)) measurableSet_closedBall
      (fun q hq => show ENNReal.ofReal (radialEnvelope β q) ≤
        ENNReal.ofReal (‖q‖ ^ (-(2 : ℝ))) from by
        rw [radialEnvelope, if_pos (mem_closedBall_zero_iff.mp hq)])
    apply hm.trans
    simpa only [mul_one] using inverse_square_closedBall_bound 1 zero_lt_one
  have ho : (∫⁻ q : GW.Space in {q | 1 < ‖q‖},
      ENNReal.ofReal (radialEnvelope β q)) ≤ ENNReal.ofReal C := by
    have hm := setLIntegral_mono' (μ := (volume : Measure GW.Space))
      (s := {q : GW.Space | 1 < ‖q‖}) (measurableSet_lt measurable_const measurable_norm)
      (fun q hq => show ENNReal.ofReal (radialEnvelope β q) ≤
        ENNReal.ofReal (‖q‖ ^ (-β)) from by
        rw [radialEnvelope, if_neg (not_le_of_gt hq)])
    apply hm.trans
    have hb := hbound 1 zero_lt_one
    unfold GW.Model.exteriorPowerIntegral GW.Model.radialPowerIntegral at hb
    simpa only [Real.one_rpow, mul_one] using hb
  have hcompl : (closedBall (0 : GW.Space) (1 : ℝ))ᶜ = {q | 1 < ‖q‖} := by ext q; simp
  rw [← lintegral_add_compl (fun q : GW.Space => ENNReal.ofReal (radialEnvelope β q))
    measurableSet_closedBall, hcompl]
  exact (add_le_add hi ho).trans_eq (ENNReal.ofReal_add (by positivity) hC).symm

theorem muDensity_zero_parameter (q : GW.Space) : muDensity 0 q = ‖q‖ ^ (-(4 : ℝ)) := by
  rw [Real.rpow_neg (norm_nonneg q), Real.rpow_ofNat]
  simp only [muDensity, add_zero, one_div]
  congr 1
  ring

theorem omega_sq_inverse_four (q : GW.Space) :
    omega q ^ 2 * ‖q‖ ^ (-(4 : ℝ)) = radialEnvelope 4 q := by
  by_cases hz : q = 0
  · simp [hz, omega, radialEnvelope]
  by_cases hq : ‖q‖ ≤ 1
  · rw [omega, min_eq_left hq, radialEnvelope, if_pos hq]
    simp only [Real.rpow_neg (norm_nonneg q), Real.rpow_ofNat]
    field_simp [norm_ne_zero_iff.mpr hz]
  · rw [omega, min_eq_right (le_of_not_ge hq), radialEnvelope, if_neg hq]
    simp

theorem omega_cube_inverse_five (q : GW.Space) :
    omega q ^ 3 * ‖q‖ ^ (-(5 : ℝ)) = radialEnvelope 5 q := by
  by_cases hz : q = 0
  · simp [hz, omega, radialEnvelope]
  by_cases hq : ‖q‖ ≤ 1
  · rw [omega, min_eq_left hq, radialEnvelope, if_pos hq]
    simp only [Real.rpow_neg (norm_nonneg q), Real.rpow_ofNat]
    field_simp [norm_ne_zero_iff.mpr hz]
  · rw [omega, min_eq_right (le_of_not_ge hq), radialEnvelope, if_neg hq]
    simp

theorem weighted_muDensity_outer (P q : GW.Space) (hP : ‖P‖ ≤ 1 / 4)
    (hq : 2 * ‖P‖ ≤ ‖q‖) :
    omega q * (omega q + ‖P‖) * muDensity P q ≤ 6 * radialEnvelope 4 q := by
  have h₁ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (omega_outer_comparison P q hP hq) (omega_nonneg q))
    (muDensity_nonneg P q)
  have h₂ := mul_le_mul_of_nonneg_left (muDensity_outer_majorant P q hq)
    (show 0 ≤ (3 / 2 : ℝ) * omega q ^ 2 by positivity)
  rw [← omega_sq_inverse_four]
  nlinarith

theorem weighted_difference_outer (P q : GW.Space) (hq : 2 * ‖P‖ ≤ ‖q‖) :
    omega q ^ 3 * |muDensity P q - muDensity 0 q| ≤ 10 * ‖P‖ * radialEnvelope 5 q := by
  have h := mul_le_mul_of_nonneg_left (muDensity_outer_difference P q hq)
    (pow_nonneg (omega_nonneg q) 3)
  calc
    _ ≤ omega q ^ 3 * (10 * ‖P‖ * ‖q‖ ^ (-(5 : ℝ))) := h
    _ = 10 * ‖P‖ * (omega q ^ 3 * ‖q‖ ^ (-(5 : ℝ))) := by ring
    _ = 10 * ‖P‖ * radialEnvelope 5 q := by rw [omega_cube_inverse_five]

theorem weighted_muDensity_inner (P q : GW.Space) (hq : ‖q‖ ≤ 2 * ‖P‖) :
    omega q * (omega q + ‖P‖) * muDensity P q ≤ 6 * ‖P‖ ^ 2 * muDensity P q := by
  have hω : omega q ≤ 2 * ‖P‖ := (omega_le_norm q).trans hq
  have h₁ := mul_le_mul hω (show omega q + ‖P‖ ≤ 3 * ‖P‖ by linarith)
    (add_nonneg (omega_nonneg q) (norm_nonneg P)) (show 0 ≤ 2 * ‖P‖ by positivity)
  have h₂ := mul_le_mul_of_nonneg_right h₁ (muDensity_nonneg P q)
  nlinarith

theorem cubed_weight_muDensity_inner (P q : GW.Space) (hq : ‖q‖ ≤ 2 * ‖P‖) :
    omega q ^ 3 * muDensity P q ≤ 8 * ‖P‖ ^ 3 * muDensity P q := by
  have h := pow_le_pow_left₀ (omega_nonneg q) ((omega_le_norm q).trans hq) 3
  have hm := mul_le_mul_of_nonneg_right h (muDensity_nonneg P q)
  nlinarith

theorem cubed_norm_muDensity_zero (q : GW.Space) :
    ‖q‖ ^ 3 * muDensity 0 q = ‖q‖ ^ (-(1 : ℝ)) := by
  by_cases hz : q = 0
  · simp [hz]
  rw [muDensity_zero_parameter]
  simp only [Real.rpow_neg (norm_nonneg q), Real.rpow_ofNat]
  field_simp [norm_ne_zero_iff.mpr hz]
  simp only [Real.rpow_one, pow_one]

theorem cubed_weight_muDensity_zero (q : GW.Space) :
    omega q ^ 3 * muDensity 0 q ≤ ‖q‖ ^ (-(1 : ℝ)) := by
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (omega_nonneg q) (omega_le_norm q) 3) (muDensity_nonneg 0 q)).trans_eq
    (cubed_norm_muDensity_zero q)

theorem weighted_difference_inner_majorant (P q : GW.Space) (hq : ‖q‖ ≤ 2 * ‖P‖) :
    omega q ^ 3 * |muDensity P q - muDensity 0 q| ≤
      8 * ‖P‖ ^ 3 * muDensity P q + ‖q‖ ^ (-(1 : ℝ)) := by
  have hnonneg := muDensity_nonneg P q
  have hzero := muDensity_nonneg 0 q
  have ht : |muDensity P q - muDensity 0 q| ≤ muDensity P q + muDensity 0 q :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hm := mul_le_mul_of_nonneg_left ht (pow_nonneg (omega_nonneg q) 3)
  have h₁ := cubed_weight_muDensity_inner P q hq
  have h₂ := cubed_weight_muDensity_zero q
  nlinarith

def weightedMuDensity (P q : GW.Space) : ℝ := omega q * (omega q + ‖P‖) * muDensity P q
def weightedMuDifference (P q : GW.Space) : ℝ := omega q ^ 3 * |muDensity P q - muDensity 0 q|

theorem weightedMuDensity_nonneg (P q : GW.Space) : 0 ≤ weightedMuDensity P q := by
  exact mul_nonneg (mul_nonneg (omega_nonneg q) (add_nonneg (omega_nonneg q) (norm_nonneg P)))
    (muDensity_nonneg P q)

theorem weightedMuDifference_nonneg (P q : GW.Space) : 0 ≤ weightedMuDifference P q :=
  mul_nonneg (pow_nonneg (omega_nonneg q) 3) (abs_nonneg _)

theorem weightedMuDensity_measurable (P : GW.Space) : Measurable (weightedMuDensity P) :=
  (omega_measurable.mul (omega_measurable.add_const ‖P‖)).mul (muDensity_measurable P)

theorem weightedMuDifference_measurable (P : GW.Space) : Measurable (weightedMuDifference P) := by
  unfold weightedMuDifference
  have hm : Measurable (fun q : GW.Space => omega q ^ (3 : ℕ) * ‖muDensity P q - muDensity 0 q‖) :=
    (omega_measurable.pow_const (3 : ℕ)).mul (((muDensity_measurable P).sub (muDensity_measurable 0)).norm)
  have he : (fun q : GW.Space => omega q ^ (3 : ℕ) * ‖muDensity P q - muDensity 0 q‖) =
      (fun q : GW.Space => omega q ^ 3 * |muDensity P q - muDensity 0 q|) := by
    funext q
    rw [Real.norm_eq_abs]
  rw [he] at hm
  exact hm

private theorem regional_integral_majorant {f g : GW.Space → ℝ} {s : Set GW.Space}
    (hs : MeasurableSet s) {A B : ℝ} (hA : 0 ≤ A)
    (hfg : ∀ q ∈ s, f q ≤ A * g q)
    (hI : (∫⁻ q : GW.Space, ENNReal.ofReal (g q)) ≤ ENNReal.ofReal B) :
    (∫⁻ q : GW.Space in s, ENNReal.ofReal (f q)) ≤ ENNReal.ofReal (A * B) := by
  have hm := setLIntegral_mono' (μ := (volume : Measure GW.Space)) hs
    (fun q hq => show ENNReal.ofReal (f q) ≤ ENNReal.ofReal A * ENNReal.ofReal (g q) from by
      rw [← ENNReal.ofReal_mul hA]
      exact ENNReal.ofReal_le_ofReal (hfg q hq))
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hm
  have hg : (∫⁻ q : GW.Space in s, ENNReal.ofReal (g q)) ≤
      ∫⁻ q : GW.Space, ENNReal.ofReal (g q) := by
    simpa only [Measure.restrict_univ] using
      (lintegral_mono_set (μ := (volume : Measure GW.Space))
        (f := fun q => ENNReal.ofReal (g q)) (Set.subset_univ s))
  have ht : ENNReal.ofReal A * (∫⁻ q : GW.Space in s, ENNReal.ofReal (g q)) ≤
      ENNReal.ofReal A * ENNReal.ofReal B := by
    simpa only [mul_comm] using mul_le_mul_left (hg.trans hI) (ENNReal.ofReal A)
  exact (hm.trans ht).trans_eq (ENNReal.ofReal_mul hA).symm

theorem inverse_one_closedBall_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
    (∫⁻ q : GW.Space in closedBall 0 R, ENNReal.ofReal (‖q‖ ^ (-(1 : ℝ)))) ≤
      ENNReal.ofReal (C * R ^ 2) := by
  obtain ⟨C, hC, hb⟩ := interior_ball_power_bound 1 (by norm_num)
  refine ⟨4 * C, by positivity, fun R hR => ?_⟩
  have hsub : closedBall (0 : GW.Space) R ⊆ ball 0 (2 * R) :=
    closedBall_subset_ball (by linarith)
  have hm := lintegral_mono_set (μ := (volume : Measure GW.Space))
    (f := fun q => ENNReal.ofReal (‖q‖ ^ (-(1 : ℝ)))) hsub
  apply (hm.trans (hb (2 * R) (by positivity))).trans_eq
  congr 1
  norm_num only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_ofNat]
  ring

theorem weightedMuDensity_lintegral {C4 : ℝ} (hC4 : 0 ≤ C4)
    (hI4 : (∫⁻ q : GW.Space, ENNReal.ofReal (radialEnvelope 4 q)) ≤ ENNReal.ofReal C4)
    (P : GW.Space) (hP : ‖P‖ ≤ 1 / 4) :
    (∫⁻ q : GW.Space, ENNReal.ofReal (weightedMuDensity P q)) ≤
      ENNReal.ofReal (6 * (3000 * GW.Model.unitBallVolume) + 6 * C4) := by
  have hv : 0 ≤ GW.Model.unitBallVolume := GW.Model.unitBallVolume_pos.le
  by_cases hzero : P = 0
  · subst P
    have he (q : GW.Space) : weightedMuDensity 0 q = radialEnvelope 4 q := by
      simp only [weightedMuDensity, norm_zero, add_zero, muDensity_zero_parameter]
      simpa only [pow_two] using omega_sq_inverse_four q
    simp_rw [he]
    exact hI4.trans (ENNReal.ofReal_le_ofReal (by nlinarith))
  have hr : 0 < ‖P‖ := norm_pos_iff.mpr hzero
  have hi : (∫⁻ q : GW.Space in closedBall 0 (2 * ‖P‖),
      ENNReal.ofReal (weightedMuDensity P q)) ≤
        ENNReal.ofReal (6 * (3000 * GW.Model.unitBallVolume) * ‖P‖) := by
    have h := regional_integral_majorant (s := closedBall 0 (2 * ‖P‖))
      (f := weightedMuDensity P) (g := muDensity P) measurableSet_closedBall
      (A := 6 * ‖P‖ ^ 2) (by positivity)
      (fun q hq => weighted_muDensity_inner P q (mem_closedBall_zero_iff.mp hq))
      (muDensity_lintegral P hzero)
    apply h.trans_eq
    congr 1
    field_simp [ne_of_gt hr] <;> ring
  have ho : (∫⁻ q : GW.Space in {q | 2 * ‖P‖ < ‖q‖},
      ENNReal.ofReal (weightedMuDensity P q)) ≤ ENNReal.ofReal (6 * C4) := by
    apply regional_integral_majorant (f := weightedMuDensity P) (g := radialEnvelope 4)
      (s := {q : GW.Space | 2 * ‖P‖ < ‖q‖}) (measurableSet_lt measurable_const measurable_norm)
      (A := 6) (by norm_num) _ hI4
    intro q hq
    exact weighted_muDensity_outer P q hP hq.le
  have hc : (closedBall (0 : GW.Space) (2 * ‖P‖))ᶜ = {q | 2 * ‖P‖ < ‖q‖} := by ext q; simp
  rw [← lintegral_add_compl (fun q : GW.Space => ENNReal.ofReal (weightedMuDensity P q))
    measurableSet_closedBall, hc]
  apply (add_le_add hi ho).trans
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hm := mul_le_mul_of_nonneg_left (show ‖P‖ ≤ 1 by linarith)
    (show 0 ≤ 6 * (3000 * GW.Model.unitBallVolume) by positivity)
  nlinarith

theorem weightedMuDifference_lintegral {C1 C5 : ℝ} (hC1 : 0 ≤ C1) (hC5 : 0 ≤ C5)
    (hI1 : ∀ R : ℝ, 0 < R →
      (∫⁻ q : GW.Space in closedBall 0 R, ENNReal.ofReal (‖q‖ ^ (-(1 : ℝ)))) ≤
        ENNReal.ofReal (C1 * R ^ 2))
    (hI5 : (∫⁻ q : GW.Space, ENNReal.ofReal (radialEnvelope 5 q)) ≤ ENNReal.ofReal C5)
    (P : GW.Space) (hP : ‖P‖ ≤ 1 / 4) :
    (∫⁻ q : GW.Space, ENNReal.ofReal (weightedMuDifference P q)) ≤
      ENNReal.ofReal ((8 * (3000 * GW.Model.unitBallVolume) + 4 * C1 + 10 * C5) * ‖P‖) := by
  have hv : 0 ≤ GW.Model.unitBallVolume := GW.Model.unitBallVolume_pos.le
  by_cases hzero : P = 0
  · subst P
    simp [weightedMuDifference]
  have hr : 0 < ‖P‖ := norm_pos_iff.mpr hzero
  have hi : (∫⁻ q : GW.Space in closedBall 0 (2 * ‖P‖),
      ENNReal.ofReal (weightedMuDifference P q)) ≤
      ENNReal.ofReal ((8 * (3000 * GW.Model.unitBallVolume) + 4 * C1) * ‖P‖ ^ 2) := by
    have hm := setLIntegral_mono' (μ := (volume : Measure GW.Space))
      (s := closedBall (0 : GW.Space) (2 * ‖P‖)) measurableSet_closedBall
      (fun q hq => show ENNReal.ofReal (weightedMuDifference P q) ≤
        ENNReal.ofReal (8 * ‖P‖ ^ 3 * muDensity P q) + ENNReal.ofReal (‖q‖ ^ (-(1 : ℝ))) from by
        rw [← ENNReal.ofReal_add (by positivity [muDensity_nonneg P q])
          (Real.rpow_nonneg (norm_nonneg q) _)]
        exact ENNReal.ofReal_le_ofReal (weighted_difference_inner_majorant P q (mem_closedBall_zero_iff.mp hq)))
    have hmf : Measurable (fun q : GW.Space => ENNReal.ofReal (8 * ‖P‖ ^ 3 * muDensity P q)) :=
      (measurable_const.mul (muDensity_measurable P)).ennreal_ofReal
    rw [lintegral_add_left hmf] at hm
    have hb : (∫⁻ q : GW.Space in closedBall 0 (2 * ‖P‖),
        ENNReal.ofReal (8 * ‖P‖ ^ 3 * muDensity P q)) ≤
        ENNReal.ofReal (8 * (3000 * GW.Model.unitBallVolume) * ‖P‖ ^ 2) := by
      have h := regional_integral_majorant (f := fun q => 8 * ‖P‖ ^ 3 * muDensity P q)
        (g := muDensity P) (s := closedBall 0 (2 * ‖P‖)) measurableSet_closedBall
        (A := 8 * ‖P‖ ^ 3) (by positivity) (fun _ _ => le_refl _) (muDensity_lintegral P hzero)
      apply h.trans_eq
      congr 1
      field_simp [ne_of_gt hr] <;> ring
    have hi1 := hI1 (2 * ‖P‖) (by positivity)
    apply (hm.trans (add_le_add hb hi1)).trans_eq
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have ho : (∫⁻ q : GW.Space in {q | 2 * ‖P‖ < ‖q‖},
      ENNReal.ofReal (weightedMuDifference P q)) ≤ ENNReal.ofReal (10 * ‖P‖ * C5) := by
    apply regional_integral_majorant (f := weightedMuDifference P) (g := radialEnvelope 5)
      (s := {q : GW.Space | 2 * ‖P‖ < ‖q‖}) (measurableSet_lt measurable_const measurable_norm)
      (A := 10 * ‖P‖) (by positivity) _ hI5
    intro q hq
    exact weighted_difference_outer P q hq.le
  have hc : (closedBall (0 : GW.Space) (2 * ‖P‖))ᶜ = {q | 2 * ‖P‖ < ‖q‖} := by ext q; simp
  rw [← lintegral_add_compl (fun q : GW.Space => ENNReal.ofReal (weightedMuDifference P q))
    measurableSet_closedBall, hc]
  apply (add_le_add hi ho).trans
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hsq : ‖P‖ ^ 2 ≤ ‖P‖ := by nlinarith [norm_nonneg P]
  have hm := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ 8 * (3000 * GW.Model.unitBallVolume) + 4 * C1 by positivity)
  nlinarith

private theorem nonnegative_real_integral_bound (f : GW.Space → ℝ) (hm : Measurable f)
    (hn : ∀ q, 0 ≤ f q) {B : ℝ} (hB : 0 ≤ B)
    (hI : (∫⁻ q : GW.Space, ENNReal.ofReal (f q)) ≤ ENNReal.ofReal B) :
    Integrable f volume ∧ (∫ q : GW.Space, f q) ≤ B := by
  have hp : 0 ≤ᵐ[volume] f := Eventually.of_forall hn
  refine ⟨⟨hm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal hp).mpr (hI.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hp hm.aestronglyMeasurable]
  simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hI

/-- All three source estimates use one finite constant, chosen before momentum.
The two weighted estimates include zero and boundary momentum; the unweighted
convolution bound holds at every nonzero momentum. -/
theorem moving_singularity_estimates : ∃ CI : ℝ, 0 < CI ∧
    (∀ P : GW.Space, ‖P‖ ≤ 1 / 4 →
      (Integrable (weightedMuDensity P) volume ∧ (∫ q : GW.Space, weightedMuDensity P q) ≤ CI) ∧
      (Integrable (weightedMuDifference P) volume ∧ (∫ q : GW.Space, weightedMuDifference P q) ≤ CI * ‖P‖)) ∧
    (∀ P : GW.Space, P ≠ 0 → Integrable (muDensity P) volume ∧
      (∫ q : GW.Space, muDensity P q) ≤ CI / ‖P‖) := by
  obtain ⟨C1, hC1, hI1⟩ := inverse_one_closedBall_bound
  obtain ⟨C4, hC4, hI4⟩ := radialEnvelope_lintegral 4 (by norm_num)
  obtain ⟨C5, hC5, hI5⟩ := radialEnvelope_lintegral 5 (by norm_num)
  let Cμ : ℝ := 3000 * GW.Model.unitBallVolume
  let Cw : ℝ := 6 * Cμ + 6 * C4
  let Cd : ℝ := 8 * Cμ + 4 * C1 + 10 * C5
  let CI : ℝ := 1 + Cμ + Cw + Cd
  have hμ : 0 ≤ Cμ := mul_nonneg (by norm_num) GW.Model.unitBallVolume_pos.le
  have hw : 0 ≤ Cw := by dsimp [Cw]; positivity
  have hd : 0 ≤ Cd := by dsimp [Cd]; positivity
  have hCI : 0 < CI := by dsimp [CI]; positivity
  have hwCI : Cw ≤ CI := by dsimp [CI]; linarith
  have hdCI : Cd ≤ CI := by dsimp [CI]; linarith
  have hμCI : Cμ ≤ CI := by dsimp [CI]; linarith
  refine ⟨CI, hCI, ?_, ?_⟩
  · intro P hP
    constructor
    · apply nonnegative_real_integral_bound (weightedMuDensity P)
        (weightedMuDensity_measurable P) (weightedMuDensity_nonneg P) hCI.le
      exact (weightedMuDensity_lintegral hC4 hI4 P hP).trans
        (ENNReal.ofReal_le_ofReal hwCI)
    · apply nonnegative_real_integral_bound (weightedMuDifference P)
        (weightedMuDifference_measurable P) (weightedMuDifference_nonneg P)
        (mul_nonneg hCI.le (norm_nonneg P))
      exact (weightedMuDifference_lintegral hC1 hC5 hI1 hI5 P hP).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hdCI (norm_nonneg P)))
  · intro P hP
    exact ⟨(muDensity_integrable_bound P hP).1,
      (muDensity_integrable_bound P hP).2.trans (div_le_div_of_nonneg_right hμCI (norm_nonneg P))⟩

theorem omega_moments_uniform : ∃ CI : ℝ, 0 < CI ∧ ∀ P : GW.Space, ‖P‖ ≤ 1 / 4 →
    (Integrable (fun q => omega q ^ 2 * muDensity P q) volume ∧
      (∫ q : GW.Space, omega q ^ 2 * muDensity P q) ≤ CI) ∧
    (Integrable (fun q => omega q ^ 3 * muDensity P q) volume ∧
      (∫ q : GW.Space, omega q ^ 3 * muDensity P q) ≤ CI) := by
  obtain ⟨CI, hCI, hw, _⟩ := moving_singularity_estimates
  refine ⟨CI, hCI, fun P hP => ?_⟩
  have hweighted := (hw P hP).1
  have hb2 (q : GW.Space) : omega q ^ 2 * muDensity P q ≤ weightedMuDensity P q := by
    have hs : omega q ^ 2 ≤ omega q * (omega q + ‖P‖) := by
      nlinarith [mul_nonneg (omega_nonneg q) (norm_nonneg P)]
    exact mul_le_mul_of_nonneg_right hs (muDensity_nonneg P q)
  have hm2 : Measurable (fun q : GW.Space => omega q ^ 2 * muDensity P q) :=
    (omega_measurable.pow_const (2 : ℕ)).mul (muDensity_measurable P)
  have hi2 : Integrable (fun q : GW.Space => omega q ^ 2 * muDensity P q) volume :=
    hweighted.1.mono' hm2.aestronglyMeasurable (Eventually.of_forall (fun q => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (muDensity_nonneg P q))]
      exact hb2 q))
  have hb3 (q : GW.Space) : omega q ^ 3 * muDensity P q ≤ omega q ^ 2 * muDensity P q := by
    have hs := mul_le_mul_of_nonneg_left (omega_le_one q) (sq_nonneg (omega q))
    have hp : omega q ^ 3 ≤ omega q ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hp (muDensity_nonneg P q)
  have hm3 : Measurable (fun q : GW.Space => omega q ^ 3 * muDensity P q) :=
    (omega_measurable.pow_const (3 : ℕ)).mul (muDensity_measurable P)
  have hi3 : Integrable (fun q : GW.Space => omega q ^ 3 * muDensity P q) volume :=
    hi2.mono' hm3.aestronglyMeasurable (Eventually.of_forall (fun q => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (omega_nonneg q) 3) (muDensity_nonneg P q))]
      exact hb3 q))
  have hbound2 := (integral_mono hi2 hweighted.1 hb2).trans hweighted.2
  exact ⟨⟨hi2, hbound2⟩, ⟨hi3, (integral_mono hi3 hi2 hb3).trans hbound2⟩⟩

theorem wDensity_memLp (P : GW.Space) (hP : P ≠ 0) : MemLp (wDensity P) 2 volume := by
  apply (memLp_two_iff_integrable_sq (wDensity_measurable P).aestronglyMeasurable).mpr
  have he : (fun q : GW.Space => wDensity P q ^ 2) = muDensity P := funext (wDensity_sq P)
  rw [he]
  exact (muDensity_integrable_bound P hP).1

/-- Complex-valued signed source, on the actual momentum measure space. -/
def thresholdSource (g : ℝ) (P q : GW.Space) : ℂ := (g : ℂ) * (wDensity P q : ℂ)

def zeroMomentumSource (g : ℝ) (q : GW.Space) : ℂ := (g : ℂ) / ((‖q‖ ^ 2 : ℝ) : ℂ)

theorem thresholdSource_memLp (g : ℝ) (P : GW.Space) (hP : P ≠ 0) :
    MemLp (thresholdSource g P) 2 volume := by
  change MemLp (fun q : GW.Space => (g : ℂ) * (wDensity P q : ℂ)) 2 volume
  exact ((wDensity_memLp P hP).ofReal).const_mul (g : ℂ)

theorem thresholdSource_zero (g : ℝ) (q : GW.Space) : thresholdSource g 0 q = zeroMomentumSource g q := by
  unfold thresholdSource wDensity zeroMomentumSource
  rw [add_zero, show ‖q‖ * ‖q‖ = ‖q‖ ^ 2 by ring, Complex.ofReal_div, Complex.ofReal_one]
  exact mul_one_div (g : ℂ) (((‖q‖ ^ 2 : ℝ) : ℂ))

theorem zeroMomentumSource_real (g : ℝ) (q : GW.Space) :
    zeroMomentumSource g q = ((g / ‖q‖ ^ 2 : ℝ) : ℂ) := by
  simp only [zeroMomentumSource, Complex.ofReal_div]

theorem signed_inverse_square_not_memLp (g : ℝ) (hg : g ≠ 0) :
    ¬ MemLp (fun q : GW.Space => g / ‖q‖ ^ 2) 2 volume := by
  intro h
  have hs := h.integrable_sq.const_mul ((g ^ 2)⁻¹)
  have he : (fun q : GW.Space => (g ^ 2)⁻¹ * (g / ‖q‖ ^ 2) ^ 2) =
      (fun q : GW.Space => ‖q‖ ^ (-(4 : ℝ))) := by
    funext q
    by_cases hq : q = 0
    · simp [hq]
    rw [Real.rpow_neg (norm_nonneg q), Real.rpow_ofNat]
    field_simp [hg, norm_ne_zero_iff.mpr hq]
  rw [he] at hs
  exact fourth_power_not_integrableOn_ball 1 zero_lt_one hs.integrableOn

theorem zeroMomentumSource_not_memLp (g : ℝ) (hg : g ≠ 0) :
    ¬ MemLp (zeroMomentumSource g) 2 volume := by
  intro h
  have hr := h.re
  have he : (fun q : GW.Space => RCLike.re (zeroMomentumSource g q)) =
      (fun q : GW.Space => g / ‖q‖ ^ 2) := by
    funext q
    rw [zeroMomentumSource_real]
    simp only [RCLike.re_eq_complex_re, Complex.ofReal_re]
  rw [he] at hr
  exact signed_inverse_square_not_memLp g hg hr

theorem zeroMomentumSource_scalar_eq_zero (g : ℝ) (hg : g ≠ 0) (a : ℂ)
    (h : MemLp (fun q : GW.Space => a * zeroMomentumSource g q) 2 volume) : a = 0 := by
  by_contra ha
  have hh := h.const_mul a⁻¹
  have he : (fun q : GW.Space => a⁻¹ * (a * zeroMomentumSource g q)) = zeroMomentumSource g := by
    funext q
    rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  rw [he] at hh
  exact zeroMomentumSource_not_memLp g hg hh

end Froehlich
