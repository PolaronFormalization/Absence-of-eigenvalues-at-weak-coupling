import Froehlich.Nodes.CA02TermDerivative
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Finite coefficient data for the source scalar derivative algorithm.
The invariant is exactly |beta|+r=2j with j≤r. The absent lower monomial
is omitted precisely when beta_i=0. -/
noncomputable section
namespace Froehlich
variable {d : ℕ}

structure ScalarWeightTermData (d : ℕ) where
  coefficient : ℝ
  powers : Fin d → ℕ
  shift : ℕ

def ScalarWeightTermData.eval (t : ScalarWeightTermData d) (b : ℝ) (x : Fin d → ℝ) : ℝ :=
  scalarWeightTerm t.coefficient t.powers t.shift b x

def ScalarWeightTermData.Admissible (r : ℕ) (t : ScalarWeightTermData d) : Prop :=
  (∑ k, t.powers k)+r = 2*t.shift ∧ t.shift ≤ r

def ScalarWeightTermData.lower (i : Fin d) (t : ScalarWeightTermData d) : ScalarWeightTermData d :=
  ⟨t.coefficient*(t.powers i : ℝ),Function.update t.powers i (t.powers i-1),t.shift⟩

def ScalarWeightTermData.raise (i : Fin d) (t : ScalarWeightTermData d) : ScalarWeightTermData d :=
  ⟨-t.coefficient*(1+2*(t.shift : ℝ)),Function.update t.powers i (t.powers i+1),t.shift+1⟩

def ScalarWeightTermData.derive (i : Fin d) (t : ScalarWeightTermData d) : List (ScalarWeightTermData d) :=
  if t.powers i = 0 then [t.raise i] else [t.lower i,t.raise i]

def scalarTermMass (ts : List (ScalarWeightTermData d)) : ℝ :=
  (ts.map (fun t => |t.coefficient|)).sum

theorem sum_coordinate_update (beta : Fin d → ℕ) (i : Fin d) (n : ℕ) :
    (∑ k, Function.update beta i n k)+beta i = (∑ k, beta k)+n := by
  have hbase := Finset.sum_update_of_mem (Finset.mem_univ i) beta (beta i)
  rw [Function.update_eq_self] at hbase
  rw [Finset.sum_update_of_mem (Finset.mem_univ i) beta n]
  omega

theorem ScalarWeightTermData.coordinate_le_order (t : ScalarWeightTermData d) (r : ℕ)
    (ht : t.Admissible r) (i : Fin d) : t.powers i ≤ r := by
  have hi : t.powers i ≤ ∑ k, t.powers k :=
    Finset.single_le_sum (fun k hk => Nat.zero_le _) (Finset.mem_univ i)
  obtain ⟨hdeg,hshift⟩ := ht
  omega

theorem ScalarWeightTermData.lower_admissible (t : ScalarWeightTermData d) (r : ℕ)
    (ht : t.Admissible r) (i : Fin d) (hi : t.powers i ≠ 0) : (t.lower i).Admissible (r+1) := by
  have hu := sum_coordinate_update t.powers i (t.powers i-1)
  obtain ⟨hdeg,hshift⟩ := ht
  change (∑ k, Function.update t.powers i (t.powers i-1) k)+(r+1) = 2*t.shift ∧ t.shift ≤ r+1
  omega

theorem ScalarWeightTermData.raise_admissible (t : ScalarWeightTermData d) (r : ℕ)
    (ht : t.Admissible r) (i : Fin d) : (t.raise i).Admissible (r+1) := by
  have hu := sum_coordinate_update t.powers i (t.powers i+1)
  obtain ⟨hdeg,hshift⟩ := ht
  change (∑ k, Function.update t.powers i (t.powers i+1) k)+(r+1) = 2*(t.shift+1) ∧ t.shift+1 ≤ r+1
  omega

theorem ScalarWeightTermData.derive_admissible (t : ScalarWeightTermData d) (r : ℕ)
    (ht : t.Admissible r) (i : Fin d) : ∀ u ∈ t.derive i, u.Admissible (r+1) := by
  intro u hu
  by_cases hi : t.powers i = 0
  · simp only [ScalarWeightTermData.derive,hi,if_true,List.mem_singleton] at hu
    subst u
    exact t.raise_admissible r ht i
  · simp only [ScalarWeightTermData.derive,hi,if_false,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hu
    rcases hu with hu|hu
    · subst u
      exact t.lower_admissible r ht i hi
    · subst u
      exact t.raise_admissible r ht i

theorem ScalarWeightTermData.derive_mass (t : ScalarWeightTermData d) (i : Fin d) :
    scalarTermMass (t.derive i) = |t.coefficient| *((t.powers i : ℝ)+1+2*(t.shift : ℝ)) := by
  have hpos : 0 ≤ 1+2*(t.shift : ℝ) := by positivity
  by_cases hi : t.powers i = 0
  · simp [scalarTermMass,ScalarWeightTermData.derive,hi,ScalarWeightTermData.raise,
      abs_mul,abs_of_nonneg hpos] <;> ring
  · simp [scalarTermMass,ScalarWeightTermData.derive,hi,ScalarWeightTermData.raise,
      ScalarWeightTermData.lower,abs_mul,abs_of_nonneg hpos,abs_of_nonneg (show (0 : ℝ) ≤ (t.powers i : ℝ) from Nat.cast_nonneg _)] <;> ring

theorem ScalarWeightTermData.derive_mass_le (t : ScalarWeightTermData d) (r : ℕ)
    (ht : t.Admissible r) (i : Fin d) :
    scalarTermMass (t.derive i) ≤ (3*(r : ℝ)+1)*|t.coefficient| := by
  have hi : (t.powers i : ℝ) ≤ (r : ℝ) := by exact_mod_cast t.coordinate_le_order r ht i
  have hj : (t.shift : ℝ) ≤ (r : ℝ) := by exact_mod_cast ht.2
  rw [t.derive_mass i]
  nlinarith [abs_nonneg t.coefficient]

end Froehlich
