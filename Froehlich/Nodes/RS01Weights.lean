import Froehlich.Nodes.EN01

/-! RS01's literal auxiliary weight on supported sectors. Below the
sector cutoff it is extended by one only to reuse the retained weighted
Fock graph infrastructure; all supported-sector identities are exact. -/
noncomputable section
open MeasureTheory
namespace Froehlich

def auxiliaryWeight (n : ℕ) (e : ℝ) (p : GW.Space) (m : ℕ)
    (K : GW.Fock.Coordinates m) : ℝ :=
  if n ≤ m then Real.sqrt (freeSymbol (-p) m K + 1 - (n : ℝ) - e) else 1

theorem auxiliaryWeight_of_ge (n m : ℕ) (e : ℝ) (p : GW.Space) (hnm : n ≤ m)
    (K : GW.Fock.Coordinates m) :
    auxiliaryWeight n e p m K = Real.sqrt (freeSymbol (-p) m K + 1 - (n : ℝ) - e) := by
  rw [auxiliaryWeight,if_pos hnm]

theorem auxiliaryWeight_below (n m : ℕ) (e : ℝ) (p : GW.Space) (hmn : m < n)
    (K : GW.Fock.Coordinates m) : auxiliaryWeight n e p m K = 1 := by
  rw [auxiliaryWeight,if_neg (Nat.not_le.mpr hmn)]

theorem auxiliaryWeight_measurable (n : ℕ) (e : ℝ) (p : GW.Space) (m : ℕ) :
    Measurable (auxiliaryWeight n e p m) := by
  unfold auxiliaryWeight
  split_ifs
  · exact ((((freeSymbol_measurable (-p) m).add_const 1).sub_const (n : ℝ)).sub_const e).sqrt
  · exact measurable_const

theorem auxiliaryWeight_permutation (n m : ℕ) (e : ℝ) (p : GW.Space)
    (tau : Equiv.Perm (Fin m)) (K : GW.Fock.Coordinates m) :
    auxiliaryWeight n e p m (fun i => K (tau i)) = auxiliaryWeight n e p m K := by
  simp only [auxiliaryWeight,freeSymbol_permutation]

theorem auxiliaryWeight_ge_one (n m : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (K : GW.Fock.Coordinates m) : 1 ≤ auxiliaryWeight n e p m K := by
  unfold auxiliaryWeight
  split_ifs with hnm
  · apply Real.le_sqrt_of_sq_le
    have hnmr : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    unfold freeSymbol
    nlinarith [sq_nonneg ‖totalMomentum m K - -p‖]
  · exact le_rfl

theorem auxiliaryWeight_sq (n m : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (hnm : n ≤ m) (K : GW.Fock.Coordinates m) :
    auxiliaryWeight n e p m K ^ 2 = freeSymbol (-p) m K + 1 - (n : ℝ) - e := by
  rw [auxiliaryWeight_of_ge n m e p hnm,Real.sq_sqrt]
  have hnmr : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  unfold freeSymbol
  nlinarith [sq_nonneg ‖totalMomentum m K - -p‖]

/-- Source comparison (weightcompare), uniform in p and the entire reference
energy interval. The auxiliary extension below n is not used here. -/
theorem energyWeight_le_auxiliaryWeight (n m : ℕ) (e : ℝ) (p : GW.Space)
    (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hnm : n ≤ m)
    (K : GW.Fock.Coordinates m) :
    energyWeight (-p) m K ≤ Real.sqrt 3 * auxiliaryWeight n e p m K := by
  have hW := auxiliaryWeight_ge_one n m e p he.2 K
  have hWsq := auxiliaryWeight_sq n m e p he.2 hnm K
  have hn' : (n : ℝ) ≤ 2 := by exact_mod_cast hn
  apply (sq_le_sq₀ (zero_le_one.trans (energyWeight_ge_one (-p) m K))
    (mul_nonneg (Real.sqrt_nonneg 3) (zero_le_one.trans hW))).mp
  rw [energyWeight_sq,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith [he.2]

end Froehlich
