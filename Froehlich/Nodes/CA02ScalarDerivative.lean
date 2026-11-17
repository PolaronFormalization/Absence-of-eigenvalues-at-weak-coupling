import Froehlich.Nodes.CA02ScalarWeight
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Exact source interpretation and the first coordinate derivative of
the scalar weight. All derivatives are native real norm derivatives. -/
noncomputable section
namespace Froehlich
variable {d : ℕ}

theorem scalarWeightRoot_denominator (b : ℝ) (hb : 1 ≤ b) (x : Fin d → ℝ) (j : ℕ) :
    (scalarWeightRoot b x)^(2*j+1) = scalarWeightRoot b x * (scalarWeightSquare b x)^j := by
  rw [pow_succ,pow_mul,scalarWeightRoot_sq b hb x,mul_comm]

theorem scalarWeightTerm_eq_source (c : ℝ) (beta : Fin d → ℕ) (j : ℕ)
    (b : ℝ) (hb : 1 ≤ b) (x : Fin d → ℝ) :
    scalarWeightTerm c beta j b x = c*(∏ i, (x i)^(beta i)) *
      (scalarWeightSquare b x)^(-(1/(2 : ℝ))-(j : ℝ)) := by
  have hpos : 0 < scalarWeightSquare b x :=
    lt_of_lt_of_le zero_lt_one (scalarWeightSquare_ge_one b hb x)
  have hp : (scalarWeightSquare b x)^((1/(2 : ℝ))+(j : ℝ)) =
      (scalarWeightRoot b x)^(2*j+1) := by
    rw [Real.rpow_add hpos,← Real.sqrt_eq_rpow,Real.rpow_natCast]
    exact (scalarWeightRoot_denominator b hb x j).symm
  have he : -(1/(2 : ℝ))-(j : ℝ) = -((1/(2 : ℝ))+(j : ℝ)) := by ring
  rw [he,Real.rpow_neg hpos.le,hp]
  exact div_eq_mul_inv _ _

theorem scalarWeightSquare_hasDerivAt_update (b : ℝ) (x : Fin d → ℝ) (i : Fin d) :
    HasDerivAt (fun t : ℝ => scalarWeightSquare b (Function.update x i t)) (2*x i) (x i) := by
  have ht : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      HasDerivAt (fun t : ℝ => (Function.update x i t j)^2)
        (if j = i then 2*x i else 0) (x i) := by
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa [Function.update_self] using hasDerivAt_pow 2 (x i)
    · simpa only [Function.update_of_ne hji,if_neg hji] using (hasDerivAt_const (x i) ((x j)^2))
  have hs := (HasDerivAt.fun_sum ht).add_const b
  simpa only [scalarWeightSquare,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hs

theorem scalarWeightRoot_hasDerivAt_update (b : ℝ) (hb : 1 ≤ b) (x : Fin d → ℝ) (i : Fin d) :
    HasDerivAt (fun t : ℝ => scalarWeightRoot b (Function.update x i t))
      (x i/scalarWeightRoot b x) (x i) := by
  have hp : scalarWeightSquare b (Function.update x i (x i)) ≠ 0 := by
    simpa only [Function.update_eq_self] using
      (lt_of_lt_of_le zero_lt_one (scalarWeightSquare_ge_one b hb x)).ne'
  have hs : HasDerivAt (fun t : ℝ => scalarWeightRoot b (Function.update x i t))
      ((2*x i)/(2*scalarWeightRoot b x)) (x i) := by
    simpa only [scalarWeightRoot,Function.update_eq_self] using
      (scalarWeightSquare_hasDerivAt_update b x i).sqrt hp
  convert hs using 1
  field_simp [(scalarWeightRoot_pos b hb x).ne']

theorem scalarInverseRootWeight_hasDerivAt_update (b : ℝ) (hb : 1 ≤ b)
    (x : Fin d → ℝ) (i : Fin d) :
    HasDerivAt (fun t : ℝ => scalarInverseRootWeight b (Function.update x i t))
      (-x i/(scalarWeightRoot b x)^3) (x i) := by
  have hn : scalarWeightRoot b (Function.update x i (x i)) ≠ 0 := by
    simpa only [Function.update_eq_self] using (scalarWeightRoot_pos b hb x).ne'
  have hd0 := (hasDerivAt_inv hn).comp (x i) (scalarWeightRoot_hasDerivAt_update b hb x i)
  change HasDerivAt (fun t : ℝ => 1/scalarWeightRoot b (Function.update x i t))
    (-x i/(scalarWeightRoot b x)^3) (x i)
  convert hd0 using 1
  · funext t
    exact one_div _
  · rw [Function.update_eq_self]
    field_simp [(scalarWeightRoot_pos b hb x).ne']
    <;> ring

end Froehlich
