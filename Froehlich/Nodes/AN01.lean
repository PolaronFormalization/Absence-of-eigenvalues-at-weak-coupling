import Froehlich.Nodes.AN00
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! AN01 (`lem:powers`). The retained general dyadic estimates supply the
constants; all integrals below use the same Euclidean volume as `GW.Space`. -/

noncomputable section
open MeasureTheory Metric Filter
open scoped ENNReal Topology

namespace Froehlich

theorem interior_power_bound (a : ℝ) (ha : a < 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      GW.Model.interiorPowerIntegral a R ≤ ENNReal.ofReal (C * R ^ (3 - a)) := by
  let A : ℝ := (7 / 8) * GW.Model.unitBallVolume * max 1 ((2 : ℝ) ^ a)
  let q : ℝ := (1 / 2 : ℝ) ^ (3 - a)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg (by norm_num) GW.Model.unitBallVolume_pos.le)
      (le_trans zero_le_one (le_max_left _ _))
  have hq : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  refine ⟨A / (1 - q), div_nonneg hA (sub_pos.mpr hq1).le, ?_⟩
  intro R hR
  rw [GW.Model.interiorPowerIntegral_tsum hR]
  have hm (m : ℕ) : GW.Model.radialPowerIntegral a (GW.Model.interiorAnnulus R m) ≤
      ENNReal.ofReal ((A * R ^ (3 - a)) * q ^ m) := by
    have h := (GW.Model.interiorAnnulus_power_bounds hR a m).2
    change _ ≤ ENNReal.ofReal (A * (R * (1 / 2 : ℝ) ^ m) ^ (3 - a)) at h
    rw [GW.Model.dyadic_power_factor hR.le (by norm_num)] at h
    simpa only [mul_assoc] using h
  apply (tsum_le_tsum hm).trans_eq
  rw [GW.Model.scaled_geometric_tsum
    (mul_nonneg hA (Real.rpow_nonneg hR.le _)) hq hq1]
  congr 1
  ring

theorem exterior_power_bound (a : ℝ) (ha : 3 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      GW.Model.exteriorPowerIntegral a R ≤ ENNReal.ofReal (C * R ^ (3 - a)) := by
  let A : ℝ := 7 * GW.Model.unitBallVolume * max 1 ((2 : ℝ) ^ (-a))
  let q : ℝ := (2 : ℝ) ^ (3 - a)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg (by norm_num) GW.Model.unitBallVolume_pos.le)
      (le_trans zero_le_one (le_max_left _ _))
  have hq : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := by
    apply (Real.rpow_lt_one_iff_of_pos (by norm_num : (0 : ℝ) < 2)).mpr
    exact Or.inl ⟨by norm_num, by linarith⟩
  refine ⟨A / (1 - q), div_nonneg hA (sub_pos.mpr hq1).le, ?_⟩
  intro R hR
  rw [GW.Model.exteriorPowerIntegral_tsum hR]
  have hm (m : ℕ) : GW.Model.radialPowerIntegral a (GW.Model.exteriorAnnulus R m) ≤
      ENNReal.ofReal ((A * R ^ (3 - a)) * q ^ m) := by
    have h := (GW.Model.exteriorAnnulus_power_bounds hR a m).2
    change _ ≤ ENNReal.ofReal (A * (R * (2 : ℝ) ^ m) ^ (3 - a)) at h
    rw [GW.Model.dyadic_power_factor hR.le (by norm_num)] at h
    simpa only [mul_assoc] using h
  apply (tsum_le_tsum hm).trans_eq
  rw [GW.Model.scaled_geometric_tsum
    (mul_nonneg hA (Real.rpow_nonneg hR.le _)) hq hq1]
  congr 1
  ring

/-- The source's open-ball integral follows from the punctured closed-ball
estimate because the omitted point is null. -/
theorem interior_ball_power_bound (a : ℝ) (ha : a < 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      (∫⁻ k : GW.Space in ball 0 R, ENNReal.ofReal (‖k‖ ^ (-a))) ≤
        ENNReal.ofReal (C * R ^ (3 - a)) := by
  obtain ⟨C, hC, h⟩ := interior_power_bound a ha
  refine ⟨C, hC, fun R hR => le_trans ?_ (h R hR)⟩
  apply lintegral_mono_set'
  have hzero : ∀ᵐ k : GW.Space ∂volume, k ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hzero] with k hk
  intro hb
  exact ⟨norm_pos_iff.mpr hk, (mem_ball_zero_iff.mp hb).le⟩

/-- Nonnegative radial-power estimates in extended integrals give both genuine
Bochner integrability and the corresponding real integral bound. -/
theorem radial_power_integrable_of_bound (a : ℝ) (s : Set GW.Space) {B : ℝ}
    (hB : 0 ≤ B)
    (h : (∫⁻ k : GW.Space in s, ENNReal.ofReal (‖k‖ ^ (-a))) ≤ ENNReal.ofReal B) :
    IntegrableOn (fun k : GW.Space => ‖k‖ ^ (-a)) s volume ∧
      (∫ k : GW.Space in s, ‖k‖ ^ (-a)) ≤ B := by
  have hm : AEStronglyMeasurable (fun k : GW.Space => ‖k‖ ^ (-a))
      (volume.restrict s) := (measurable_norm.pow_const (-a)).aestronglyMeasurable
  have hn : 0 ≤ᵐ[volume.restrict s] (fun k : GW.Space => ‖k‖ ^ (-a)) :=
    Eventually.of_forall (fun k => Real.rpow_nonneg (norm_nonneg k) _)
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal hn).mpr (h.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hn hm]
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [ENNReal.toReal_ofReal hB] using ht

theorem interior_power_integrable_bound (a : ℝ) (_ha0 : 0 < a) (ha3 : a < 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      IntegrableOn (fun k : GW.Space => ‖k‖ ^ (-a)) (ball 0 R) volume ∧
        (∫ k : GW.Space in ball 0 R, ‖k‖ ^ (-a)) ≤ C * R ^ (3 - a) := by
  obtain ⟨C, hC, h⟩ := interior_ball_power_bound a ha3
  refine ⟨C, hC, fun R hR => ?_⟩
  exact radial_power_integrable_of_bound a (ball 0 R)
    (mul_nonneg hC (Real.rpow_nonneg hR.le _)) (h R hR)

theorem exterior_power_integrable_bound (a : ℝ) (ha : 3 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      IntegrableOn (fun k : GW.Space => ‖k‖ ^ (-a)) {k | R < ‖k‖} volume ∧
        (∫ k : GW.Space in {k | R < ‖k‖}, ‖k‖ ^ (-a)) ≤ C * R ^ (3 - a) := by
  obtain ⟨C, hC, h⟩ := exterior_power_bound a ha
  refine ⟨C, hC, fun R hR => ?_⟩
  exact radial_power_integrable_of_bound a {k | R < ‖k‖}
    (mul_nonneg hC (Real.rpow_nonneg hR.le _)) (h R hR)

theorem fourth_power_not_integrableOn_ball (R : ℝ) (hR : 0 < R) :
    ¬ IntegrableOn (fun k : GW.Space => ‖k‖ ^ (-(4 : ℝ))) (ball 0 R) volume := by
  intro h
  have hsub : {k : GW.Space | 0 < ‖k‖ ∧ ‖k‖ ≤ R / 2} ⊆ ball 0 R := by
    intro k hk
    apply mem_ball_zero_iff.mpr
    linarith [hk.2]
  have hf := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
    (fun k : GW.Space => Real.rpow_nonneg (norm_nonneg k) (-(4 : ℝ))))).mp
      (h.mono_set hsub).hasFiniteIntegral
  change GW.Model.interiorPowerIntegral 4 (R / 2) < ∞ at hf
  have hc := (GW.Model.interiorPowerIntegral_finite_iff (by linarith : 0 < R / 2) 4).mp hf
  norm_num at hc

theorem fourth_power_not_integrableOn_neighborhood (s : Set GW.Space) (hs : s ∈ 𝓝 0) :
    ¬ IntegrableOn (fun k : GW.Space => ‖k‖ ^ (-(4 : ℝ))) s volume := by
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp hs
  intro h
  exact fourth_power_not_integrableOn_ball R hR (h.mono_set hsub)

end Froehlich
