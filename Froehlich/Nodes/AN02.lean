import Froehlich.Nodes.AN01

/-! AN02 (`lem:shiftedsource`): the source norm density, its uniform all-shift
integral estimate, and the bounded-momentum ultraviolet tail. -/

noncomputable section
open MeasureTheory Metric Filter
open scoped ENNReal

namespace Froehlich

def shiftedSourceDensity (p k : GW.Space) : ℝ :=
  1 / (‖k‖ ^ 2 * (1 + ‖k + p‖ ^ 2))

theorem shiftedSourceDensity_nonneg (p k : GW.Space) :
    0 ≤ shiftedSourceDensity p k := by unfold shiftedSourceDensity; positivity

theorem shiftedSourceDensity_measurable (p : GW.Space) :
    Measurable (shiftedSourceDensity p) := by
  unfold shiftedSourceDensity
  fun_prop

theorem shiftedSourceDensity_le_inverse_square (p k : GW.Space) :
    shiftedSourceDensity p k ≤ ‖k‖ ^ (-(2 : ℝ)) := by
  by_cases hk : k = 0
  · simp [shiftedSourceDensity, hk]
  have hn : 0 < ‖k‖ := norm_pos_iff.mpr hk
  rw [Real.rpow_neg (norm_nonneg k), Real.rpow_ofNat]
  unfold shiftedSourceDensity
  have hd : ‖k‖ ^ 2 ≤ ‖k‖ ^ 2 * (1 + ‖k + p‖ ^ 2) := by
    nlinarith [sq_nonneg ‖k + p‖]
  simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hn) hd

/-- The outer-region estimate prescribed by the source proof. -/
theorem shiftedSourceDensity_tail_pointwise (p k : GW.Space)
    (hpk : 2 * ‖p‖ ≤ ‖k‖) :
    shiftedSourceDensity p k ≤ 4 * ‖k‖ ^ (-(4 : ℝ)) := by
  by_cases hk : k = 0
  · simp [shiftedSourceDensity, hk]
  have hn : 0 < ‖k‖ := norm_pos_iff.mpr hk
  have hs : ‖k‖ - ‖p‖ ≤ ‖k + p‖ := by
    simpa only [norm_neg, sub_neg_eq_add] using norm_sub_norm_le k (-p)
  have hhalf : ‖k‖ / 2 ≤ ‖k + p‖ := by linarith
  have hsq : ‖k‖ ^ 2 ≤ 4 * ‖k + p‖ ^ 2 := by
    nlinarith [norm_nonneg (k + p)]
  have hden : 0 < ‖k‖ ^ 2 * (1 + ‖k + p‖ ^ 2) := by positivity
  rw [Real.rpow_neg (norm_nonneg k), Real.rpow_ofNat]
  change 1 / (‖k‖ ^ 2 * (1 + ‖k + p‖ ^ 2)) ≤ 4 / ‖k‖ ^ 4
  apply (div_le_div_iff₀ hden (pow_pos hn 4)).mpr
  nlinarith [mul_nonneg (sq_nonneg ‖k‖) (show 0 ≤ 4 * ‖k + p‖ ^ 2 - ‖k‖ ^ 2 by linarith)]

theorem shiftedSourceDensity_tail_lintegral (p : GW.Space) (Λ : ℝ)
    (hΛ : 0 < Λ) (hp : 2 * ‖p‖ ≤ Λ) :
    (∫⁻ k : GW.Space in {k | Λ < ‖k‖}, ENNReal.ofReal (shiftedSourceDensity p k)) ≤
      ENNReal.ofReal (56 * GW.Model.unitBallVolume / Λ) := by
  have hm : (∫⁻ k : GW.Space in {k | Λ < ‖k‖},
      ENNReal.ofReal (shiftedSourceDensity p k)) ≤
        ∫⁻ k : GW.Space in {k | Λ < ‖k‖},
          ENNReal.ofReal 4 * ENNReal.ofReal (‖k‖ ^ (-(4 : ℝ))) := by
    apply setLIntegral_mono' (measurableSet_lt measurable_const measurable_norm)
    intro k hk
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    exact ENNReal.ofReal_le_ofReal (shiftedSourceDensity_tail_pointwise p k (hp.trans hk.le))
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hm
  have hb := GW.Model.exteriorPowerIntegral_four_bound hΛ
  have ht := mul_le_mul_left hb (ENNReal.ofReal 4)
  have ht' : ENNReal.ofReal 4 * GW.Model.exteriorPowerIntegral 4 Λ ≤
      ENNReal.ofReal 4 * ENNReal.ofReal (14 * GW.Model.unitBallVolume / Λ) := by
    simpa only [mul_comm] using ht
  calc
    _ ≤ ENNReal.ofReal 4 * (∫⁻ k : GW.Space in {k | Λ < ‖k‖},
        ENNReal.ofReal (‖k‖ ^ (-(4 : ℝ)))) := hm
    _ = ENNReal.ofReal 4 * GW.Model.exteriorPowerIntegral 4 Λ := by
      unfold GW.Model.exteriorPowerIntegral GW.Model.radialPowerIntegral
      rfl
    _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal (14 * GW.Model.unitBallVolume / Λ) := ht'
    _ = ENNReal.ofReal (56 * GW.Model.unitBallVolume / Λ) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      congr 1
      ring

theorem shiftedSourceDensity_integrableOn_of_bound (p : GW.Space) (s : Set GW.Space)
    {B : ℝ} (hB : 0 ≤ B)
    (h : (∫⁻ k : GW.Space in s, ENNReal.ofReal (shiftedSourceDensity p k)) ≤
      ENNReal.ofReal B) :
    IntegrableOn (shiftedSourceDensity p) s volume ∧
      (∫ k : GW.Space in s, shiftedSourceDensity p k) ≤ B := by
  have hm : AEStronglyMeasurable (shiftedSourceDensity p) (volume.restrict s) :=
    (shiftedSourceDensity_measurable p).aestronglyMeasurable
  have hn : 0 ≤ᵐ[volume.restrict s] shiftedSourceDensity p :=
    Eventually.of_forall (shiftedSourceDensity_nonneg p)
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal hn).mpr (h.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hn hm]
  simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h

theorem shiftedSourceDensity_tail (R : ℝ) (p : GW.Space) (hp : ‖p‖ ≤ R)
    (Λ : ℝ) (hΛ : max 1 (2 * R) ≤ Λ) :
    IntegrableOn (shiftedSourceDensity p) {k | Λ < ‖k‖} volume ∧
      (∫ k : GW.Space in {k | Λ < ‖k‖}, shiftedSourceDensity p k) ≤
        56 * GW.Model.unitBallVolume / Λ := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hΛ)
  apply shiftedSourceDensity_integrableOn_of_bound
  · exact div_nonneg (mul_nonneg (by norm_num) GW.Model.unitBallVolume_pos.le) hΛpos.le
  · apply shiftedSourceDensity_tail_lintegral p Λ hΛpos
    exact (mul_le_mul_of_nonneg_left hp (by norm_num)).trans ((le_max_right _ _).trans hΛ)

theorem inverse_square_closedBall_bound (R : ℝ) (hR : 0 < R) :
    (∫⁻ k : GW.Space in closedBall 0 R, ENNReal.ofReal (‖k‖ ^ (-(2 : ℝ)))) ≤
      ENNReal.ofReal (7 * GW.Model.unitBallVolume * R) := by
  apply le_trans _ (GW.Model.interiorPowerIntegral_two_bound hR)
  apply lintegral_mono_set'
  have hzero : ∀ᵐ k : GW.Space ∂volume, k ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hzero] with k hk
  intro hb
  exact ⟨norm_pos_iff.mpr hk, mem_closedBall_zero_iff.mp hb⟩

/-- First source region: the shifted denominator is at least half the radius. -/
theorem shiftedSourceDensity_left_majorant (p k : GW.Space) {r : ℝ}
    (hr : 0 < r) (hb : r / 2 ≤ ‖k + p‖) :
    shiftedSourceDensity p k ≤ (4 / r ^ 2) * ‖k‖ ^ (-(2 : ℝ)) := by
  by_cases hk : k = 0
  · simp [shiftedSourceDensity, hk]
  have hn : 0 < ‖k‖ := norm_pos_iff.mpr hk
  have hs : r ^ 2 ≤ 4 * ‖k + p‖ ^ 2 := by nlinarith [norm_nonneg (k + p)]
  have hden : 0 < ‖k‖ ^ 2 * (1 + ‖k + p‖ ^ 2) := by positivity
  rw [Real.rpow_neg (norm_nonneg k), Real.rpow_ofNat]
  change 1 / (‖k‖ ^ 2 * (1 + ‖k + p‖ ^ 2)) ≤ _
  calc
    _ ≤ 4 / (r ^ 2 * ‖k‖ ^ 2) := by
      apply (div_le_div_iff₀ hden (mul_pos (sq_pos_of_pos hr) (sq_pos_of_pos hn))).mpr
      nlinarith [mul_nonneg (sq_nonneg ‖k‖) (show 0 ≤ 4 * ‖k + p‖ ^ 2 - r ^ 2 by linarith)]
    _ = (4 / r ^ 2) * (‖k‖ ^ 2)⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Second source region, away from its one null singular point. -/
theorem shiftedSourceDensity_right_majorant (p k : GW.Space) {r : ℝ}
    (hr : 0 < r) (ha : r / 2 ≤ ‖k‖) (hk : k + p ≠ 0) :
    shiftedSourceDensity p k ≤ (4 / r ^ 2) * ‖k + p‖ ^ (-(2 : ℝ)) := by
  have hn : 0 < ‖k + p‖ := norm_pos_iff.mpr hk
  have hn₀ : 0 < ‖k‖ := by linarith
  have hs : r ^ 2 ≤ 4 * ‖k‖ ^ 2 := by nlinarith [norm_nonneg k]
  have hden : 0 < ‖k‖ ^ 2 * (1 + ‖k + p‖ ^ 2) := by positivity
  rw [Real.rpow_neg (norm_nonneg (k + p)), Real.rpow_ofNat]
  change 1 / (‖k‖ ^ 2 * (1 + ‖k + p‖ ^ 2)) ≤ _
  calc
    _ ≤ 4 / (r ^ 2 * ‖k + p‖ ^ 2) := by
      apply (div_le_div_iff₀ hden (mul_pos (sq_pos_of_pos hr) (sq_pos_of_pos hn))).mpr
      nlinarith [mul_nonneg (sq_nonneg ‖k + p‖) (show 0 ≤ 4 * ‖k‖ ^ 2 - r ^ 2 by linarith)]
    _ = (4 / r ^ 2) * (‖k + p‖ ^ 2)⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The remaining bounded region has neither of the two local singularities. -/
theorem shiftedSourceDensity_middle_majorant (p k : GW.Space) {r : ℝ}
    (hr : 0 < r) (ha : r / 2 ≤ ‖k‖) (hb : r / 2 ≤ ‖k + p‖) :
    shiftedSourceDensity p k ≤ 16 / r ^ 4 := by
  have hn : 0 < ‖k‖ := by linarith
  have hden : 0 < ‖k‖ ^ 2 * (1 + ‖k + p‖ ^ 2) := by positivity
  have hs₁ : r ^ 2 ≤ 4 * ‖k‖ ^ 2 := by nlinarith [norm_nonneg k]
  have hs₂ : r ^ 2 ≤ 4 * ‖k + p‖ ^ 2 := by nlinarith [norm_nonneg (k + p)]
  have hs := mul_le_mul hs₁ hs₂ (sq_nonneg r) (by positivity)
  unfold shiftedSourceDensity
  apply (div_le_div_iff₀ hden (pow_pos hr 4)).mpr
  nlinarith [hs, mul_nonneg (sq_nonneg ‖k‖) (sq_nonneg ‖k + p‖)]

theorem shiftedSourceDensity_first_region_geometry (p k : GW.Space)
    (hk : ‖k‖ ≤ ‖p‖ / 2) : ‖p‖ / 2 ≤ ‖k + p‖ := by
  have h := norm_sub_norm_le p (-k)
  simp only [norm_neg, sub_neg_eq_add] at h
  rw [add_comm p k] at h
  linarith

theorem shiftedSourceDensity_second_region_geometry (p k : GW.Space)
    (hk : ‖k + p‖ ≤ ‖p‖ / 2) : ‖p‖ / 2 ≤ ‖k‖ := by
  have h : ‖p‖ ≤ ‖k + p‖ + ‖k‖ := by
    have h := norm_sub_le (k + p) k
    simpa only [add_sub_cancel_left] using h
  linarith

theorem shiftedSourceDensity_first_region_lintegral (p : GW.Space) (hp : 0 < ‖p‖) :
    (∫⁻ k : GW.Space in closedBall 0 (‖p‖ / 2),
      ENNReal.ofReal (shiftedSourceDensity p k)) ≤
      ENNReal.ofReal (14 * GW.Model.unitBallVolume / ‖p‖) := by
  have hcoeff : 0 ≤ 4 / ‖p‖ ^ 2 := by positivity
  have hm : (∫⁻ k : GW.Space in closedBall 0 (‖p‖ / 2),
      ENNReal.ofReal (shiftedSourceDensity p k)) ≤
        ∫⁻ k : GW.Space in closedBall 0 (‖p‖ / 2),
          ENNReal.ofReal (4 / ‖p‖ ^ 2) * ENNReal.ofReal (‖k‖ ^ (-(2 : ℝ))) := by
    apply setLIntegral_mono' measurableSet_closedBall
    intro k hk
    rw [← ENNReal.ofReal_mul hcoeff]
    exact ENNReal.ofReal_le_ofReal (shiftedSourceDensity_left_majorant p k hp
      (shiftedSourceDensity_first_region_geometry p k (mem_closedBall_zero_iff.mp hk)))
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hm
  have hb := inverse_square_closedBall_bound (‖p‖ / 2) (by linarith)
  have hmul : ENNReal.ofReal (4 / ‖p‖ ^ 2) *
      (∫⁻ k : GW.Space in closedBall 0 (‖p‖ / 2), ENNReal.ofReal (‖k‖ ^ (-(2 : ℝ)))) ≤
      ENNReal.ofReal (4 / ‖p‖ ^ 2) *
        ENNReal.ofReal (7 * GW.Model.unitBallVolume * (‖p‖ / 2)) := by
    simpa only [mul_comm] using mul_le_mul_left hb (ENNReal.ofReal (4 / ‖p‖ ^ 2))
  apply (hm.trans hmul).trans_eq
  rw [← ENNReal.ofReal_mul hcoeff]
  congr 1
  field_simp [ne_of_gt hp]
  ring

theorem shiftedSourceDensity_second_region_lintegral (p : GW.Space) (hp : 0 < ‖p‖) :
    (∫⁻ k : GW.Space in (fun k : GW.Space => k + p) ⁻¹' closedBall 0 (‖p‖ / 2),
      ENNReal.ofReal (shiftedSourceDensity p k)) ≤
      ENNReal.ofReal (14 * GW.Model.unitBallVolume / ‖p‖) := by
  have hcoeff : 0 ≤ 4 / ‖p‖ ^ 2 := by positivity
  have hs : MeasurableSet ((fun k : GW.Space => k + p) ⁻¹' closedBall 0 (‖p‖ / 2)) :=
    measurableSet_closedBall.preimage (measurable_id.add_const p)
  have hzero : ∀ᵐ k : GW.Space ∂volume, k ≠ 0 := by rw [ae_iff]; simp
  have hz := (space_translation_preserving p).quasiMeasurePreserving.ae hzero
  have hm : (∫⁻ k : GW.Space in (fun k : GW.Space => k + p) ⁻¹' closedBall 0 (‖p‖ / 2),
      ENNReal.ofReal (shiftedSourceDensity p k)) ≤
        ∫⁻ k : GW.Space in (fun k : GW.Space => k + p) ⁻¹' closedBall 0 (‖p‖ / 2),
          ENNReal.ofReal (4 / ‖p‖ ^ 2) * ENNReal.ofReal (‖k + p‖ ^ (-(2 : ℝ))) := by
    apply setLIntegral_mono_ae' hs
    filter_upwards [hz] with k hk
    intro hball
    rw [← ENNReal.ofReal_mul hcoeff]
    exact ENNReal.ofReal_le_ofReal (shiftedSourceDensity_right_majorant p k hp
      (shiftedSourceDensity_second_region_geometry p k (mem_closedBall_zero_iff.mp hball)) hk)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hm
  have ht := (space_translation_preserving p).setLIntegral_comp_preimage
    (s := closedBall 0 (‖p‖ / 2)) measurableSet_closedBall
    (measurable_norm.pow_const (-(2 : ℝ))).ennreal_ofReal
  rw [ht] at hm
  have hb := inverse_square_closedBall_bound (‖p‖ / 2) (by linarith)
  have hmul : ENNReal.ofReal (4 / ‖p‖ ^ 2) *
      (∫⁻ k : GW.Space in closedBall 0 (‖p‖ / 2), ENNReal.ofReal (‖k‖ ^ (-(2 : ℝ)))) ≤
      ENNReal.ofReal (4 / ‖p‖ ^ 2) *
        ENNReal.ofReal (7 * GW.Model.unitBallVolume * (‖p‖ / 2)) := by
    simpa only [mul_comm] using mul_le_mul_left hb (ENNReal.ofReal (4 / ‖p‖ ^ 2))
  apply (hm.trans hmul).trans_eq
  rw [← ENNReal.ofReal_mul hcoeff]
  congr 1
  field_simp [ne_of_gt hp]
  ring

def shiftedSourceMiddleRegion (p : GW.Space) : Set GW.Space :=
  closedBall 0 (2 * ‖p‖) \ (closedBall 0 (‖p‖ / 2) ∪
    (fun k : GW.Space => k + p) ⁻¹' closedBall 0 (‖p‖ / 2))

theorem shiftedSourceDensity_middle_region_lintegral (p : GW.Space) (hp : 0 < ‖p‖) :
    (∫⁻ k : GW.Space in shiftedSourceMiddleRegion p,
      ENNReal.ofReal (shiftedSourceDensity p k)) ≤
      ENNReal.ofReal (128 * GW.Model.unitBallVolume / ‖p‖) := by
  have hcoeff : 0 ≤ 16 / ‖p‖ ^ 4 := by positivity
  have hs : MeasurableSet (shiftedSourceMiddleRegion p) :=
    measurableSet_closedBall.diff (measurableSet_closedBall.union
      (measurableSet_closedBall.preimage (measurable_id.add_const p)))
  have hm : (∫⁻ k : GW.Space in shiftedSourceMiddleRegion p,
      ENNReal.ofReal (shiftedSourceDensity p k)) ≤
        ∫⁻ _k : GW.Space in shiftedSourceMiddleRegion p, ENNReal.ofReal (16 / ‖p‖ ^ 4) := by
    apply setLIntegral_mono' hs
    intro k hk
    have h₁ : ‖p‖ / 2 ≤ ‖k‖ := by
      by_contra h
      exact hk.2 (Or.inl (mem_closedBall_zero_iff.mpr (le_of_lt (lt_of_not_ge h))))
    have h₂ : ‖p‖ / 2 ≤ ‖k + p‖ := by
      by_contra h
      exact hk.2 (Or.inr (mem_closedBall_zero_iff.mpr (le_of_lt (lt_of_not_ge h))))
    exact ENNReal.ofReal_le_ofReal (shiftedSourceDensity_middle_majorant p k hp h₁ h₂)
  rw [lintegral_const, Measure.restrict_apply_univ] at hm
  have hμ : volume (shiftedSourceMiddleRegion p) ≤ volume (closedBall (0 : GW.Space) (2 * ‖p‖)) :=
    measure_mono Set.sdiff_subset
  have hmul : ENNReal.ofReal (16 / ‖p‖ ^ 4) * volume (shiftedSourceMiddleRegion p) ≤
      ENNReal.ofReal (16 / ‖p‖ ^ 4) * volume (closedBall (0 : GW.Space) (2 * ‖p‖)) := by
    simpa only [mul_comm] using mul_le_mul_left hμ (ENNReal.ofReal (16 / ‖p‖ ^ 4))
  apply (hm.trans hmul).trans_eq
  rw [GW.Model.spaceClosedBallVolume _ (by positivity), ← ENNReal.ofReal_mul hcoeff]
  congr 1
  field_simp [ne_of_gt hp]
  ring

theorem shiftedSourceDensity_uniform_lintegral (p : GW.Space) :
    (∫⁻ k : GW.Space, ENNReal.ofReal (shiftedSourceDensity p k)) ≤
      ENNReal.ofReal (1000 * GW.Model.unitBallVolume) := by
  have hv : 0 ≤ GW.Model.unitBallVolume := GW.Model.unitBallVolume_pos.le
  by_cases hp : ‖p‖ ≤ 2
  · have hi : (∫⁻ k : GW.Space in closedBall 0 4,
        ENNReal.ofReal (shiftedSourceDensity p k)) ≤ ENNReal.ofReal (28 * GW.Model.unitBallVolume) := by
      have hm := setLIntegral_mono' (μ := (volume : Measure GW.Space))
        (s := closedBall (0 : GW.Space) (4 : ℝ))
        (f := fun k => ENNReal.ofReal (shiftedSourceDensity p k))
        (g := fun k => ENNReal.ofReal (‖k‖ ^ (-(2 : ℝ)))) measurableSet_closedBall
        (fun k _ => ENNReal.ofReal_le_ofReal (shiftedSourceDensity_le_inverse_square p k))
      apply hm.trans
      calc
        _ ≤ ENNReal.ofReal (7 * GW.Model.unitBallVolume * 4) :=
          inverse_square_closedBall_bound 4 (by norm_num)
        _ = ENNReal.ofReal (28 * GW.Model.unitBallVolume) := by congr 1; ring
    have ht : (∫⁻ k : GW.Space in {k | 4 < ‖k‖},
        ENNReal.ofReal (shiftedSourceDensity p k)) ≤ ENNReal.ofReal (14 * GW.Model.unitBallVolume) := by
      have h := shiftedSourceDensity_tail_lintegral p 4 (by norm_num) (by linarith)
      apply h.trans_eq
      congr 1
      ring
    have hcompl : (closedBall (0 : GW.Space) (4 : ℝ))ᶜ = {k | 4 < ‖k‖} := by ext k; simp
    rw [← lintegral_add_compl (fun k : GW.Space => ENNReal.ofReal (shiftedSourceDensity p k))
      measurableSet_closedBall, hcompl]
    apply (add_le_add hi ht).trans
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  · have hr : 2 < ‖p‖ := lt_of_not_ge hp
    have hpos : 0 < ‖p‖ := by linarith
    let A : Set GW.Space := closedBall 0 (‖p‖ / 2)
    let B : Set GW.Space := (fun k : GW.Space => k + p) ⁻¹' closedBall 0 (‖p‖ / 2)
    let C : Set GW.Space := shiftedSourceMiddleRegion p
    let D : Set GW.Space := {k | 2 * ‖p‖ < ‖k‖}
    let f : GW.Space → ℝ≥0∞ := fun k => ENNReal.ofReal (shiftedSourceDensity p k)
    have hcover : Set.univ ⊆ A ∪ B ∪ C ∪ D := by
      intro k _
      by_cases ha : k ∈ A
      · exact Or.inl (Or.inl (Or.inl ha))
      by_cases hb : k ∈ B
      · exact Or.inl (Or.inl (Or.inr hb))
      by_cases hc : ‖k‖ ≤ 2 * ‖p‖
      · exact Or.inl (Or.inr ⟨mem_closedBall_zero_iff.mpr hc, not_or.mpr ⟨ha, hb⟩⟩)
      · exact Or.inr (lt_of_not_ge hc)
    have hcoverInt : (∫⁻ k, f k ∂(volume : Measure GW.Space)) ≤
        ((∫⁻ k in A, f k ∂volume) + ∫⁻ k in B, f k ∂volume) +
          (∫⁻ k in C, f k ∂volume) + ∫⁻ k in D, f k ∂volume := by
      calc
        (∫⁻ k, f k ∂(volume : Measure GW.Space)) =
            ∫⁻ k in Set.univ, f k ∂volume := by simp only [Measure.restrict_univ]
        _ ≤ ∫⁻ k in A ∪ B ∪ C ∪ D, f k ∂volume :=
          lintegral_mono_set (μ := (volume : Measure GW.Space)) (f := f) hcover
        _ ≤ (∫⁻ k in A ∪ B ∪ C, f k ∂volume) + ∫⁻ k in D, f k ∂volume :=
          lintegral_union_le (μ := (volume : Measure GW.Space)) f (A ∪ B ∪ C) D
        _ ≤ ((∫⁻ k in A ∪ B, f k ∂volume) + ∫⁻ k in C, f k ∂volume) + ∫⁻ k in D, f k ∂volume :=
          add_le_add (lintegral_union_le (μ := (volume : Measure GW.Space)) f (A ∪ B) C) (le_refl _)
        _ ≤ ((∫⁻ k in A, f k ∂volume) + ∫⁻ k in B, f k ∂volume) +
            (∫⁻ k in C, f k ∂volume) + ∫⁻ k in D, f k ∂volume :=
          add_le_add (add_le_add
            (lintegral_union_le (μ := (volume : Measure GW.Space)) f A B) (le_refl _)) (le_refl _)
    have hd : (∫⁻ k : GW.Space in D, f k) ≤ ENNReal.ofReal (28 * GW.Model.unitBallVolume / ‖p‖) := by
      have ht := shiftedSourceDensity_tail_lintegral p (2 * ‖p‖) (by positivity) le_rfl
      apply ht.trans_eq
      congr 1
      field_simp [ne_of_gt hpos]
      ring
    have hsum := add_le_add
      (add_le_add (add_le_add (shiftedSourceDensity_first_region_lintegral p hpos)
        (shiftedSourceDensity_second_region_lintegral p hpos))
        (shiftedSourceDensity_middle_region_lintegral p hpos)) hd
    apply (hcoverInt.trans hsum).trans
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have he : 14 * GW.Model.unitBallVolume / ‖p‖ + 14 * GW.Model.unitBallVolume / ‖p‖ +
        128 * GW.Model.unitBallVolume / ‖p‖ + 28 * GW.Model.unitBallVolume / ‖p‖ =
        184 * GW.Model.unitBallVolume / ‖p‖ := by ring
    rw [he]
    apply (div_le_iff₀ hpos).mpr
    nlinarith

theorem shiftedSourceDensity_uniform : ∃ Cv : ℝ, 0 < Cv ∧ ∀ p : GW.Space,
    Integrable (shiftedSourceDensity p) volume ∧
      (∫ k : GW.Space, shiftedSourceDensity p k) ≤ Cv := by
  refine ⟨1000 * GW.Model.unitBallVolume, mul_pos (by norm_num) GW.Model.unitBallVolume_pos, ?_⟩
  intro p
  have h := shiftedSourceDensity_integrableOn_of_bound p Set.univ
    (B := 1000 * GW.Model.unitBallVolume)
    (mul_nonneg (by norm_num) GW.Model.unitBallVolume_pos.le)
    (by simpa using shiftedSourceDensity_uniform_lintegral p)
  simpa using h

end Froehlich
