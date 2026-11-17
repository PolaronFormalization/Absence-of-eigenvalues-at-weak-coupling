import Froehlich.Nodes.CA02TermLists
import Froehlich.Nodes.CA01MultiIndexBlocks

set_option autoImplicit false

/-! The source finite expansion and its dimension-independent coefficient
bound, before matching coordinate block notation. All coefficient data
are independent of the base point x and the parameter b≥1. -/
noncomputable section
namespace Froehlich
variable {d : ℕ}

def scalarDerivativeCoefficientBound : ℕ → ℝ
  | 0 => 1
  | r+1 => (3*(r : ℝ)+1)*scalarDerivativeCoefficientBound r

def scalarDerivativeTerms : List (Fin d) → List (ScalarWeightTermData d)
  | [] => [⟨1,0,0⟩]
  | i::is => deriveScalarTerms i (scalarDerivativeTerms is)

theorem scalarDerivativeCoefficientBound_nonnegative (r : ℕ) :
    0 ≤ scalarDerivativeCoefficientBound r := by
  induction r with
  | zero => exact zero_le_one
  | succ r ih =>
    change 0 ≤ (3*(r : ℝ)+1)*scalarDerivativeCoefficientBound r
    exact mul_nonneg (by positivity) ih

theorem scalarDerivativeTerms_admissible (is : List (Fin d)) :
    ∀ t ∈ scalarDerivativeTerms is, t.Admissible is.length := by
  induction is with
  | nil =>
    intro t ht
    simp only [scalarDerivativeTerms,List.mem_singleton] at ht
    subst t
    simp [ScalarWeightTermData.Admissible]
  | cons i is ih =>
    exact deriveScalarTerms_admissible (scalarDerivativeTerms is) is.length ih i

theorem scalarDerivativeTerms_mass_le (is : List (Fin d)) :
    scalarTermMass (scalarDerivativeTerms is) ≤ scalarDerivativeCoefficientBound is.length := by
  induction is with
  | nil => simp [scalarDerivativeTerms,scalarTermMass,scalarDerivativeCoefficientBound]
  | cons i is ih =>
    change scalarTermMass (deriveScalarTerms i (scalarDerivativeTerms is)) ≤
      (3*(is.length : ℝ)+1)*scalarDerivativeCoefficientBound is.length
    calc
      _ ≤ (3*(is.length : ℝ)+1)*scalarTermMass (scalarDerivativeTerms is) :=
        deriveScalarTerms_mass_le _ is.length (scalarDerivativeTerms_admissible is) i
      _ ≤ _ := mul_le_mul_of_nonneg_left ih (by positivity)

theorem scalarDerivativeTerms_expansion (is : List (Fin d)) (b : ℝ) (hb : 1 ≤ b) :
    coordinateBlocksPartial (is.map (fun i => (i,1))) (scalarInverseRootWeight b) =
      evalScalarTerms (scalarDerivativeTerms is) b := by
  induction is with
  | nil =>
    funext x
    simp [coordinateBlocksPartial,scalarDerivativeTerms,evalScalarTerms,
      ScalarWeightTermData.eval,scalarWeightTerm,scalarInverseRootWeight]
  | cons i is ih =>
    change coordinateIterate i 1 (coordinateBlocksPartial (is.map (fun j => (j,1)))
      (scalarInverseRootWeight b)) = evalScalarTerms (deriveScalarTerms i (scalarDerivativeTerms is)) b
    rw [ih]
    funext x
    change deriv (fun t : ℝ => evalScalarTerms (scalarDerivativeTerms is) b (Function.update x i t)) (x i) = _
    exact (evalScalarTerms_hasDerivAt_update (scalarDerivativeTerms is) b hb x i).deriv

theorem scalarDerivativeTerms_relative_bound (is : List (Fin d))
    (b : ℝ) (hb : 1 ≤ b) (x : Fin d → ℝ) :
    |coordinateBlocksPartial (is.map (fun i => (i,1))) (scalarInverseRootWeight b) x| ≤
      scalarDerivativeCoefficientBound is.length * scalarInverseRootWeight b x := by
  rw [scalarDerivativeTerms_expansion is b hb]
  calc
    _ ≤ scalarTermMass (scalarDerivativeTerms is) * scalarInverseRootWeight b x :=
      evalScalarTerms_relative_bound _ is.length (scalarDerivativeTerms_admissible is) b hb x
    _ ≤ _ := mul_le_mul_of_nonneg_right (scalarDerivativeTerms_mass_le is) (by
      unfold scalarInverseRootWeight
      exact div_nonneg zero_le_one (scalarWeightRoot_pos b hb x).le)

/-- The finite family is chosen before b and x, and has the source's exact
admissibility and coefficient-mass bound. -/
theorem exists_scalarDerivativeExpansion (is : List (Fin d)) :
    ∃ ts : List (ScalarWeightTermData d),
      (∀ b : ℝ, 1 ≤ b → ∀ x,
        coordinateBlocksPartial (is.map (fun i => (i,1))) (scalarInverseRootWeight b) x = evalScalarTerms ts b x) ∧
      (∀ t ∈ ts, t.Admissible is.length) ∧
      scalarTermMass ts ≤ scalarDerivativeCoefficientBound is.length := by
  refine ⟨scalarDerivativeTerms is,?_,scalarDerivativeTerms_admissible is,scalarDerivativeTerms_mass_le is⟩
  intro b hb x
  exact congrFun (scalarDerivativeTerms_expansion is b hb) x

end Froehlich
