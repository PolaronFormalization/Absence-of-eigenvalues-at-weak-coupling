import Froehlich.Nodes.RS01Weights

/-! The reverse comparison on the complete original domain. It is global,
including discarded sectors, and uniform over the fixed reference interval. -/
noncomputable section
namespace Froehlich

theorem auxiliaryWeight_le_energyWeight (n m : ℕ) (e : ℝ) (p : GW.Space)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (K : GW.Fock.Coordinates m) :
    auxiliaryWeight n e p m K ≤ Real.sqrt (5/4 : ℝ) * energyWeight (-p) m K := by
  apply (sq_le_sq₀ (zero_le_one.trans (auxiliaryWeight_ge_one n m e p he.2 K))
    (mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans (energyWeight_ge_one (-p) m K)))).mp
  rw [mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5/4),energyWeight_sq]
  by_cases hnm : n ≤ m
  · rw [auxiliaryWeight_sq n m e p he.2 hnm]
    nlinarith [he.1,freeSymbol_nonneg (-p) m K,Nat.cast_nonneg (α := ℝ) n]
  · rw [auxiliaryWeight_below n m e p (Nat.lt_of_not_ge hnm)]
    nlinarith [freeSymbol_nonneg (-p) m K]

end Froehlich
