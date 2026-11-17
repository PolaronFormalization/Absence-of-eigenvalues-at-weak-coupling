import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! CA02: the scalar free weight and its monomial relative bound.
The denominator (sqrt w)^(2j+1) is the source w^(1/2+j).
No differentiability or operator conclusion is claimed by this helper. -/
noncomputable section
namespace Froehlich
variable {d : ℕ}

def scalarWeightSquare (b : ℝ) (x : Fin d → ℝ) : ℝ := (∑ i, (x i)^2)+b

def scalarWeightRoot (b : ℝ) (x : Fin d → ℝ) : ℝ := Real.sqrt (scalarWeightSquare b x)

def scalarInverseRootWeight (b : ℝ) (x : Fin d → ℝ) : ℝ := 1/scalarWeightRoot b x

def scalarWeightTerm (c : ℝ) (beta : Fin d → ℕ) (j : ℕ) (b : ℝ) (x : Fin d → ℝ) : ℝ :=
  c*(∏ i, (x i)^(beta i))/(scalarWeightRoot b x)^(2*j+1)

theorem scalarWeightSquare_euclidean (b : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    scalarWeightSquare b (fun i => x i) = ‖x‖^2+b := by
  rw [scalarWeightSquare,EuclideanSpace.real_norm_sq_eq]

theorem scalarWeightSquare_ge_one (b : ℝ) (hb : 1 ≤ b) (x : Fin d → ℝ) :
    1 ≤ scalarWeightSquare b x := by
  have hs : 0 ≤ ∑ i, (x i)^2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  dsimp [scalarWeightSquare]
  linarith

theorem scalarWeightRoot_pos (b : ℝ) (hb : 1 ≤ b) (x : Fin d → ℝ) :
    0 < scalarWeightRoot b x :=
  Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (scalarWeightSquare_ge_one b hb x))

theorem scalarWeightRoot_sq (b : ℝ) (hb : 1 ≤ b) (x : Fin d → ℝ) :
    (scalarWeightRoot b x)^2 = scalarWeightSquare b x :=
  Real.sq_sqrt (zero_le_one.trans (scalarWeightSquare_ge_one b hb x))

theorem scalarWeightRoot_ge_one (b : ℝ) (hb : 1 ≤ b) (x : Fin d → ℝ) :
    1 ≤ scalarWeightRoot b x := by
  have hsq := scalarWeightRoot_sq b hb x
  have hl := scalarWeightSquare_ge_one b hb x
  have hp := (scalarWeightRoot_pos b hb x).le
  nlinarith

theorem abs_coordinate_le_scalarWeightRoot (b : ℝ) (hb : 1 ≤ b) (x : Fin d → ℝ) (i : Fin d) :
    |x i| ≤ scalarWeightRoot b x := by
  have hs : (x i)^2 ≤ ∑ j, (x j)^2 :=
    Finset.single_le_sum (fun j hj => sq_nonneg (x j)) (Finset.mem_univ i)
  have hsq := scalarWeightRoot_sq b hb x
  have hp := (scalarWeightRoot_pos b hb x).le
  dsimp [scalarWeightSquare] at hsq
  nlinarith [sq_abs (x i),abs_nonneg (x i)]

theorem scalarWeightTerm_relative_bound (c : ℝ) (beta : Fin d → ℕ) (j : ℕ)
    (b : ℝ) (hb : 1 ≤ b) (x : Fin d → ℝ) (hdegree : (∑ i, beta i) ≤ 2*j) :
    |scalarWeightTerm c beta j b x| ≤ |c| *scalarInverseRootWeight b x := by
  let w := scalarWeightRoot b x
  have hw : 0 < w := scalarWeightRoot_pos b hb x
  have hw1 : 1 ≤ w := scalarWeightRoot_ge_one b hb x
  have hmono : |∏ i, (x i)^(beta i)| ≤ w^(∑ i, beta i) := by
    rw [Finset.abs_prod,← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod₀
    · intro i hi
      exact abs_nonneg _
    · intro i hi
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_coordinate_le_scalarWeightRoot b hb x i) _
  have hpower : |∏ i, (x i)^(beta i)| ≤ w^(2*j) :=
    hmono.trans (pow_le_pow_right₀ hw1 hdegree)
  have hratio : |∏ i, (x i)^(beta i)|/w^(2*j+1) ≤ 1/w := by
    apply (div_le_div_iff₀ (pow_pos hw _) hw).mpr
    simpa only [one_mul,pow_succ] using mul_le_mul_of_nonneg_right hpower hw.le
  have hm := mul_le_mul_of_nonneg_left hratio (abs_nonneg c)
  change |c*(∏ i, (x i)^(beta i))/w^(2*j+1)| ≤ |c| * (1/w)
  rw [abs_div,abs_mul,abs_of_pos (pow_pos hw _),mul_div_assoc]
  exact hm

end Froehlich
