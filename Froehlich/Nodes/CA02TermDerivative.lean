import Froehlich.Nodes.CA02MonomialDerivative
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The exact two terms in the source monomial differentiation algorithm.
The lower-exponent term has coefficient zero when beta_i=0. -/
noncomputable section
namespace Froehlich
variable {d : ℕ}

theorem scalarWeightTerm_hasDerivAt_update (c : ℝ) (beta : Fin d → ℕ) (j : ℕ)
    (b : ℝ) (hb : 1 ≤ b) (x : Fin d → ℝ) (i : Fin d) :
    HasDerivAt (fun t : ℝ => scalarWeightTerm c beta j b (Function.update x i t))
      (scalarWeightTerm (c*(beta i : ℝ)) (Function.update beta i (beta i-1)) j b x +
        scalarWeightTerm (-c*(1+2*(j : ℝ))) (Function.update beta i (beta i+1)) (j+1) b x) (x i) := by
  let s : ℝ := -(1/(2 : ℝ))-(j : ℝ)
  have hq : scalarWeightSquare b (Function.update x i (x i)) ≠ 0 := by
    simpa only [Function.update_eq_self] using
      (lt_of_lt_of_le zero_lt_one (scalarWeightSquare_ge_one b hb x)).ne'
  have hp := (scalarWeightSquare_hasDerivAt_update b x i).rpow_const (p := s) (Or.inl hq)
  have hm := coordinateMonomial_hasDerivAt_update beta x i
  have hc := (hasDerivAt_const_mul
    (x := coordinateMonomial beta (Function.update x i (x i))) c).comp (x i) hm
  have hd : HasDerivAt (fun t : ℝ => c*coordinateMonomial beta (Function.update x i t) *
      (scalarWeightSquare b (Function.update x i t))^s)
      ((c*coordinateMonomial beta x) * (2*x i*s*(scalarWeightSquare b x)^(s-1)) +
        (c*((beta i : ℝ)*coordinateMonomial (Function.update beta i (beta i-1)) x)) *
          (scalarWeightSquare b x)^s) (x i) := by
    simpa only [Function.comp_apply,Function.update_eq_self,smul_eq_mul] using hc.fun_smul hp
  have he : (fun t : ℝ => scalarWeightTerm c beta j b (Function.update x i t)) =
      (fun t : ℝ => c*coordinateMonomial beta (Function.update x i t) *
        (scalarWeightSquare b (Function.update x i t))^s) := by
    funext t
    exact scalarWeightTerm_eq_source c beta j b hb (Function.update x i t)
  rw [he]
  convert hd using 1
  rw [scalarWeightTerm_eq_source _ _ _ b hb x,scalarWeightTerm_eq_source _ _ _ b hb x]
  change (c*(beta i : ℝ))*coordinateMonomial (Function.update beta i (beta i-1)) x *
      (scalarWeightSquare b x)^s +
      (-c*(1+2*(j : ℝ)))*coordinateMonomial (Function.update beta i (beta i+1)) x *
        (scalarWeightSquare b x)^(-(1/(2 : ℝ))-((j+1 : ℕ) : ℝ)) = _
  rw [coordinateMonomial_raise]
  have hexp : s-1 = -(1/(2 : ℝ))-((j+1 : ℕ) : ℝ) := by dsimp [s]; push_cast; ring
  rw [hexp]
  dsimp [s]
  push_cast
  ring

end Froehlich
