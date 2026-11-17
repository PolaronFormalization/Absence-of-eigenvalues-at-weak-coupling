import Froehlich.Nodes.CA02FiniteExpansion
import Froehlich.Nodes.CA01CoefficientBox

set_option autoImplicit false

/-! Exact canonical multi-index form of the source expansion. Flattening
coordinate blocks is a definitional iteration identity, not a commutation
of mixed derivatives. -/
noncomputable section
namespace Froehlich
variable {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def coordinateBlockIndices (bs : List (Fin d × ℕ)) : List (Fin d) :=
  bs.flatMap (fun b => List.replicate b.2 b.1)

theorem coordinateBlocksPartial_append (bs cs : List (Fin d × ℕ))
    (F : (Fin d → ℝ) → V) :
    coordinateBlocksPartial (bs++cs) F = coordinateBlocksPartial bs (coordinateBlocksPartial cs F) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.cons_append,coordinateBlocksPartial,ih]

theorem coordinateBlocksPartial_replicate_unit (i : Fin d) (n : ℕ)
    (F : (Fin d → ℝ) → V) :
    coordinateBlocksPartial ((List.replicate n i).map (fun j => (j,1))) F = coordinateIterate i n F := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,List.map_cons,coordinateBlocksPartial]
    rw [ih]
    change coordinatePartial i (coordinateIterate i n F) = coordinateIterate i (n+1) F
    exact (coordinateIterate_succ i n F).symm

theorem coordinateBlocksPartial_flatten (bs : List (Fin d × ℕ))
    (F : (Fin d → ℝ) → V) :
    coordinateBlocksPartial ((coordinateBlockIndices bs).map (fun i => (i,1))) F =
      coordinateBlocksPartial bs F := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change coordinateBlocksPartial
      ((List.replicate b.2 b.1 ++ coordinateBlockIndices bs).map (fun i => (i,1))) F =
      coordinateIterate b.1 b.2 (coordinateBlocksPartial bs F)
    rw [List.map_append,coordinateBlocksPartial_append,coordinateBlocksPartial_replicate_unit,ih]

theorem coordinateBlockIndices_length (bs : List (Fin d × ℕ)) :
    (coordinateBlockIndices bs).length = coordinateBlocksOrder bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change (List.replicate b.2 b.1 ++ coordinateBlockIndices bs).length =
      b.2+coordinateBlocksOrder bs
    rw [List.length_append,List.length_replicate,ih]

def canonicalMultiIndexCoordinates (alpha : Fin d → ℕ) : List (Fin d) :=
  coordinateBlockIndices (List.ofFn (fun i : Fin d => (i,alpha i)))

theorem canonicalMultiIndexCoordinates_length (alpha : Fin d → ℕ) :
    (canonicalMultiIndexCoordinates alpha).length = ∑ i, alpha i := by
  rw [canonicalMultiIndexCoordinates,coordinateBlockIndices_length,coordinateBlocksOrder_ofFn]

theorem coordinateMultiPartial_eq_unitBlocks (alpha : Fin d → ℕ) (F : (Fin d → ℝ) → V) :
    coordinateMultiPartial alpha F = coordinateBlocksPartial
      ((canonicalMultiIndexCoordinates alpha).map (fun i => (i,1))) F :=
  (coordinateBlocksPartial_flatten (List.ofFn (fun i : Fin d => (i,alpha i))) F).symm

theorem evalScalarTerms_eq_source (ts : List (ScalarWeightTermData d)) (b : ℝ) (hb : 1 ≤ b)
    (x : Fin d → ℝ) :
    evalScalarTerms ts b x = (ts.map (fun t => t.coefficient*(∏ i, (x i)^(t.powers i)) *
      (scalarWeightSquare b x)^(-(1/(2 : ℝ))-(t.shift : ℝ)))).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [evalScalarTerms_cons,List.map_cons,List.sum_cons,ih]
    congr 1
    exact scalarWeightTerm_eq_source t.coefficient t.powers t.shift b hb x

theorem exists_scalarWeightMultiIndexExpansion (alpha : Fin d → ℕ) :
    ∃ ts : List (ScalarWeightTermData d),
      (∀ b : ℝ, 1 ≤ b → ∀ x,
        coordinateMultiPartial alpha (scalarInverseRootWeight b) x =
          (ts.map (fun t => t.coefficient*(∏ i, (x i)^(t.powers i)) *
            (scalarWeightSquare b x)^(-(1/(2 : ℝ))-(t.shift : ℝ)))).sum) ∧
      (∀ t ∈ ts, (∑ i, t.powers i)+(∑ i, alpha i) = 2*t.shift ∧ t.shift ≤ ∑ i, alpha i) ∧
      scalarTermMass ts ≤ scalarDerivativeCoefficientBound (∑ i, alpha i) := by
  let is := canonicalMultiIndexCoordinates alpha
  obtain ⟨ts,hformula,hadmissible,hmass⟩ := exists_scalarDerivativeExpansion is
  refine ⟨ts,?_,?_,?_⟩
  · intro b hb x
    rw [coordinateMultiPartial_eq_unitBlocks,hformula b hb x,evalScalarTerms_eq_source ts b hb x]
  · intro t ht
    have h : t.Admissible (∑ i, alpha i) := by
      simpa only [is,canonicalMultiIndexCoordinates_length] using hadmissible t ht
    exact h
  · simpa only [is,canonicalMultiIndexCoordinates_length] using hmass

theorem scalarWeightMultiIndex_relative_bound (alpha : Fin d → ℕ) (b : ℝ) (hb : 1 ≤ b)
    (x : Fin d → ℝ) :
    |coordinateMultiPartial alpha (scalarInverseRootWeight b) x| ≤
      scalarDerivativeCoefficientBound (∑ i, alpha i) * scalarInverseRootWeight b x := by
  rw [coordinateMultiPartial_eq_unitBlocks]
  simpa only [canonicalMultiIndexCoordinates_length] using
    scalarDerivativeTerms_relative_bound (canonicalMultiIndexCoordinates alpha) b hb x

theorem scalarInverseRootWeight_eq_source (b : ℝ) (hb : 1 ≤ b) (x : Fin d → ℝ) :
    scalarInverseRootWeight b x = (scalarWeightSquare b x)^(-(1/(2 : ℝ))) := by
  simpa [scalarWeightTerm,scalarInverseRootWeight] using scalarWeightTerm_eq_source 1 (0 : Fin d → ℕ) 0 b hb x

theorem scalarInverseRootWeight_euclidean (b : ℝ) (hb : 1 ≤ b) (x : EuclideanSpace ℝ (Fin d)) :
    scalarInverseRootWeight b (fun i => x i) = (‖x‖^2+b)^(-(1/(2 : ℝ))) := by
  rw [scalarInverseRootWeight_eq_source b hb,scalarWeightSquare_euclidean]

end Froehlich
