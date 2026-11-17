import Froehlich.Nodes.CA02AuxiliarySymbols

set_option autoImplicit false

/-! Actual source weights are globally comparable with the nonuniform
factor 1+‖p0-p‖, and locally with the exact source factor two. This makes
fixed-energy families genuine globally defined multiplier maps. -/
noncomputable section
namespace Froehlich

theorem scalarWeightRoot_euclidean_triangle {d : ℕ} (b : ℝ) (hb : 1 ≤ b)
    (x0 x : EuclideanSpace ℝ (Fin d)) :
    scalarWeightRoot b (fun i => x0 i) ≤ scalarWeightRoot b (fun i => x i)+‖x0-x‖ := by
  let w0 := scalarWeightRoot b (fun i => x0 i)
  let w := scalarWeightRoot b (fun i => x i)
  have hw0 : 0 < w0 := scalarWeightRoot_pos b hb _
  have hw : 0 < w := scalarWeightRoot_pos b hb _
  have h0 : w0^2 = ‖x0‖^2+b := by
    rw [scalarWeightRoot_sq b hb,scalarWeightSquare_euclidean]
  have h : w^2 = ‖x‖^2+b := by
    rw [scalarWeightRoot_sq b hb,scalarWeightSquare_euclidean]
  have hx : ‖x‖ ≤ w := by nlinarith [norm_nonneg x]
  have htri : ‖x0‖ ≤ ‖x‖+‖x0-x‖ := norm_le_norm_add_norm_sub' x0 x
  have hsq := (sq_le_sq₀ (norm_nonneg x0) (add_nonneg (norm_nonneg x) (norm_nonneg (x0-x)))).mpr htri
  have hp := mul_nonneg (sub_nonneg.mpr hx) (norm_nonneg (x0-x))
  change w0 ≤ w+‖x0-x‖
  apply (sq_le_sq₀ hw0.le (add_nonneg hw.le (norm_nonneg (x0-x)))).mp
  nlinarith

theorem scalarWeightRoot_euclidean_global_comparison {d : ℕ} (b : ℝ) (hb : 1 ≤ b)
    (x0 x : EuclideanSpace ℝ (Fin d)) :
    scalarWeightRoot b (fun i => x0 i) ≤ (1+‖x0-x‖)*scalarWeightRoot b (fun i => x i) := by
  have ht := scalarWeightRoot_euclidean_triangle b hb x0 x
  have hw := scalarWeightRoot_ge_one b hb (fun i => x i)
  have hp := mul_nonneg (sub_nonneg.mpr hw) (norm_nonneg (x0-x))
  nlinarith

theorem auxiliaryWeight_global_comparison (n m : ℕ) (e : ℝ) (he : e ≤ 0)
    (p0 p : GW.Space) (K : GW.Fock.Coordinates m) :
    auxiliaryWeight n e p0 m K ≤ (1+‖p0-p‖)*auxiliaryWeight n e p m K := by
  by_cases hnm : n ≤ m
  · rw [auxiliaryWeight_eq_scalar_root n m e p0 hnm,auxiliaryWeight_eq_scalar_root n m e p hnm]
    have h := scalarWeightRoot_euclidean_global_comparison ((m : ℝ)+1-(n : ℝ)-e)
      (auxiliaryScalarParameter_ge_one n m e he hnm) (totalMomentum m K+p0) (totalMomentum m K+p)
    simpa only [add_sub_add_left_eq_sub] using h
  · simp only [auxiliaryWeight,if_neg hnm,mul_one]
    linarith [norm_nonneg (p0-p)]

theorem auxiliaryWeight_ratio_bound (n m : ℕ) (e : ℝ) (he : e ≤ 0)
    (p0 p : GW.Space) (K : GW.Fock.Coordinates m) :
    auxiliaryWeight n e p0 m K / auxiliaryWeight n e p m K ≤ 1+‖p0-p‖ := by
  exact (div_le_iff₀ (zero_lt_one.trans_le (auxiliaryWeight_ge_one n m e p he K))).mpr
    (auxiliaryWeight_global_comparison n m e he p0 p K)

theorem auxiliaryWeight_local_comparison (n m : ℕ) (e : ℝ) (he : e ≤ 0)
    (p0 p : GW.Space) (hdist : ‖p0-p‖ ≤ 1) (K : GW.Fock.Coordinates m) :
    auxiliaryWeight n e p0 m K ≤ 2*auxiliaryWeight n e p m K := by
  have h := auxiliaryWeight_global_comparison n m e he p0 p K
  have hp := mul_nonneg (sub_nonneg.mpr hdist)
    (zero_le_one.trans (auxiliaryWeight_ge_one n m e p he K))
  nlinarith

theorem auxiliaryInverseWeightJet_fixed_weight_bound (is : List (Fin 3)) (n m : ℕ)
    (e : ℝ) (he : e ≤ 0) (p0 p : GW.Space) (K : GW.Fock.Coordinates m) :
    |auxiliaryWeight n e p0 m K * auxiliaryInverseWeightJet is n e p m K| ≤
      scalarDerivativeCoefficientBound is.length*(1+‖p0-p‖) := by
  have hW := zero_le_one.trans (auxiliaryWeight_ge_one n m e p0 he K)
  rw [abs_mul,abs_of_nonneg hW]
  calc
    _ ≤ auxiliaryWeight n e p0 m K *
        (scalarDerivativeCoefficientBound is.length*(auxiliaryWeight n e p m K)⁻¹) :=
      mul_le_mul_of_nonneg_left (auxiliaryInverseWeightJet_relative_bound is n m e p he K) hW
    _ = scalarDerivativeCoefficientBound is.length*
        (auxiliaryWeight n e p0 m K / auxiliaryWeight n e p m K) := by rw [div_eq_mul_inv]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (auxiliaryWeight_ratio_bound n m e he p0 p K)
      (scalarDerivativeCoefficientBound_nonnegative is.length)

theorem auxiliaryInverseWeightJet_fixed_weight_local_bound (is : List (Fin 3)) (n m : ℕ)
    (e : ℝ) (he : e ≤ 0) (p0 p : GW.Space) (hdist : ‖p0-p‖ ≤ 1) (K : GW.Fock.Coordinates m) :
    |auxiliaryWeight n e p0 m K * auxiliaryInverseWeightJet is n e p m K| ≤
      2*scalarDerivativeCoefficientBound is.length := by
  have h := auxiliaryInverseWeightJet_fixed_weight_bound is n m e he p0 p K
  have hp := mul_nonneg (scalarDerivativeCoefficientBound_nonnegative is.length) (sub_nonneg.mpr hdist)
  nlinarith

end Froehlich
