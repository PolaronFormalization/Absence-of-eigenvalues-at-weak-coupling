import Froehlich.Nodes.CA02CanonicalExpansion
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

/-! Scalar smoothness and the source factor-two local weight comparison.
The distance condition is the Euclidean sum of coordinate squares. -/
noncomputable section
namespace Froehlich
variable {d : ℕ}

theorem scalarWeightSquare_contDiff (b : ℝ) (n : WithTop ENat) :
    ContDiff ℝ n (scalarWeightSquare (d := d) b) := by
  unfold scalarWeightSquare
  apply ContDiff.add
  · apply ContDiff.sum
    intro i hi
    simpa using! (contDiff_apply ℝ (fun _ : Fin d => ℝ) i).pow 2
  · exact contDiff_const

theorem scalarWeightRoot_contDiff (b : ℝ) (hb : 1 ≤ b) (n : WithTop ENat) :
    ContDiff ℝ n (scalarWeightRoot (d := d) b) := by
  exact (scalarWeightSquare_contDiff b n).sqrt
    (fun x => (lt_of_lt_of_le zero_lt_one (scalarWeightSquare_ge_one b hb x)).ne')

theorem scalarInverseRootWeight_contDiff (b : ℝ) (hb : 1 ≤ b) (n : WithTop ENat) :
    ContDiff ℝ n (scalarInverseRootWeight (d := d) b) := by
  exact (contDiff_const : ContDiff ℝ n (fun _ : Fin d → ℝ => (1 : ℝ))).div
    (scalarWeightRoot_contDiff b hb n) (fun x => (scalarWeightRoot_pos b hb x).ne')

theorem scalarInverseRootWeight_le_one (b : ℝ) (hb : 1 ≤ b) (x : Fin d → ℝ) :
    scalarInverseRootWeight b x ≤ 1 := by
  exact (div_le_one (scalarWeightRoot_pos b hb x)).mpr (scalarWeightRoot_ge_one b hb x)

theorem scalarWeightMultiIndex_bound (alpha : Fin d → ℕ) (b : ℝ) (hb : 1 ≤ b)
    (x : Fin d → ℝ) :
    |coordinateMultiPartial alpha (scalarInverseRootWeight b) x| ≤
      scalarDerivativeCoefficientBound (∑ i, alpha i) := by
  have h := scalarWeightMultiIndex_relative_bound alpha b hb x
  have hC := scalarDerivativeCoefficientBound_nonnegative (∑ i, alpha i)
  exact h.trans (by nlinarith [scalarInverseRootWeight_le_one b hb x])

theorem scalarWeightRoot_local_comparison (b : ℝ) (hb : 1 ≤ b) (x y : Fin d → ℝ)
    (hdist : (∑ i, (x i-y i)^2) ≤ 1) :
    scalarWeightRoot b x ≤ 2*scalarWeightRoot b y := by
  have hs : (∑ i, (x i)^2) ≤ ∑ i, (2*(y i)^2+2*(x i-y i)^2) := by
    apply Finset.sum_le_sum
    intro i hi
    nlinarith [sq_nonneg (x i-2*y i)]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  apply (sq_le_sq₀ (scalarWeightRoot_pos b hb x).le
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (scalarWeightRoot_pos b hb y).le)).mp
  rw [mul_pow,scalarWeightRoot_sq b hb x,scalarWeightRoot_sq b hb y]
  dsimp [scalarWeightSquare]
  nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => sq_nonneg (y i))]

theorem scalarWeightRoot_euclidean_comparison (b : ℝ) (hb : 1 ≤ b)
    (x y : EuclideanSpace ℝ (Fin d)) (hdist : ‖x-y‖ ≤ 1) :
    scalarWeightRoot b (fun i => x i) ≤ 2*scalarWeightRoot b (fun i => y i) := by
  apply scalarWeightRoot_local_comparison b hb
  change (∑ i, ((x-y) i)^2) ≤ 1
  rw [← EuclideanSpace.real_norm_sq_eq]
  nlinarith [norm_nonneg (x-y)]

theorem scalarInverseRootWeight_fixed_weight_bound (b : ℝ) (hb : 1 ≤ b) (x0 x : Fin d → ℝ)
    (hdist : (∑ i, (x0 i-x i)^2) ≤ 1) :
    scalarWeightRoot b x0 * scalarInverseRootWeight b x ≤ 2 := by
  change scalarWeightRoot b x0 * (1/scalarWeightRoot b x) ≤ 2
  rw [mul_one_div]
  exact (div_le_iff₀ (scalarWeightRoot_pos b hb x)).mpr (scalarWeightRoot_local_comparison b hb x0 x hdist)

end Froehlich
