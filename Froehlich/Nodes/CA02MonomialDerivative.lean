import Froehlich.Nodes.CA02ScalarDerivative
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The literal monomial part of the source differentiation algorithm.
Lowering an exponent contributes its natural-number coefficient, including
zero exponents; raising it contributes multiplication by x_i. -/
noncomputable section
namespace Froehlich
variable {d : ℕ}

def coordinateMonomial (beta : Fin d → ℕ) (x : Fin d → ℝ) : ℝ := ∏ i, (x i)^(beta i)

theorem coordinateMonomial_update (beta : Fin d → ℕ) (x : Fin d → ℝ)
    (i : Fin d) (t : ℝ) :
    coordinateMonomial beta (Function.update x i t) =
      t^(beta i) * ∏ k ∈ Finset.univ.erase i, (x k)^(beta k) := by
  rw [coordinateMonomial,← Finset.mul_prod_erase Finset.univ
    (fun k => (Function.update x i t k)^(beta k)) (Finset.mem_univ i)]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

theorem coordinateMonomial_exponent_update (beta : Fin d → ℕ) (x : Fin d → ℝ)
    (i : Fin d) (n : ℕ) :
    coordinateMonomial (Function.update beta i n) x =
      (x i)^n * ∏ k ∈ Finset.univ.erase i, (x k)^(beta k) := by
  rw [coordinateMonomial,← Finset.mul_prod_erase Finset.univ
    (fun k => (x k)^(Function.update beta i n k)) (Finset.mem_univ i)]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

theorem coordinateMonomial_raise (beta : Fin d → ℕ) (x : Fin d → ℝ) (i : Fin d) :
    coordinateMonomial (Function.update beta i (beta i+1)) x = x i * coordinateMonomial beta x := by
  have hb := coordinateMonomial_update beta x i (x i)
  rw [Function.update_eq_self] at hb
  rw [coordinateMonomial_exponent_update,hb,pow_succ]
  ring

theorem coordinateMonomial_hasDerivAt_update (beta : Fin d → ℕ) (x : Fin d → ℝ) (i : Fin d) :
    HasDerivAt (fun t : ℝ => coordinateMonomial beta (Function.update x i t))
      ((beta i : ℝ)*coordinateMonomial (Function.update beta i (beta i-1)) x) (x i) := by
  have hd := (hasDerivAt_mul_const (x := (x i)^(beta i))
    (∏ k ∈ Finset.univ.erase i, (x k)^(beta k))).comp (x i) (hasDerivAt_pow (beta i) (x i))
  convert hd using 1
  · funext t
    exact coordinateMonomial_update beta x i t
  · rw [coordinateMonomial_exponent_update]
    change (beta i : ℝ)*((x i)^(beta i-1) * ∏ k ∈ Finset.univ.erase i, (x k)^(beta k)) =
      (∏ k ∈ Finset.univ.erase i, (x k)^(beta k)) * ((beta i : ℝ)*(x i)^(beta i-1))
    ring

end Froehlich
