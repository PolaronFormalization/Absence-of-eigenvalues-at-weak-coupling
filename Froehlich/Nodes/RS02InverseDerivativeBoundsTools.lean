import Froehlich.Nodes.CA02CanonicalExpansion
import Froehlich.Nodes.CA01MultiIndexConstants
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

/-! The strict degree decrease and constant-addition identities used by
RS02's exact source inverse recurrence induction. -/
noncomputable section
namespace Froehlich

theorem rs02MultiIndex_order_le {d : ℕ} (alpha beta : Fin d → ℕ)
    (hbeta : beta ∈ multiIndexBox alpha) : (∑ i, beta i) ≤ ∑ i, alpha i :=
  Finset.sum_le_sum (fun i _ => (mem_multiIndexBox alpha beta).mp hbeta i)

theorem rs02MultiIndex_positive_order {d : ℕ} (alpha : Fin d → ℕ) (ha : alpha ≠ 0) :
    0 < ∑ i, alpha i := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp ha
  have hi' : 0 < alpha i := Nat.pos_of_ne_zero (by simpa only [Pi.zero_apply] using hi)
  exact hi'.trans_le (Finset.single_le_sum (fun j _ => Nat.zero_le (alpha j)) (Finset.mem_univ i))

theorem rs02MultiIndex_difference_order_lt {d : ℕ} (alpha beta : Fin d → ℕ)
    (hbeta : beta ∈ (multiIndexBox alpha).erase 0) :
    (∑ i, (alpha i-beta i)) < ∑ i, alpha i := by
  classical
  have hbne : beta ≠ 0 := (Finset.mem_erase.mp hbeta).1
  have hble := (mem_multiIndexBox alpha beta).mp (Finset.mem_erase.mp hbeta).2
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hbne
  have hi' : 0 < beta i := Nat.pos_of_ne_zero (by simpa only [Pi.zero_apply] using hi)
  apply Finset.sum_lt_sum (fun j _ => Nat.sub_le (alpha j) (beta j))
  exact ⟨i,Finset.mem_univ i,Nat.sub_lt (hi'.trans_le (hble i)) hi'⟩

private theorem rs02UnitBlocks_const_add {d : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (c : V) (F : (Fin d → ℝ) → V) :
    ∀ is : List (Fin d), is ≠ [] →
      coordinateBlocksPartial (is.map (fun i => (i,1))) (fun p => c+F p) =
        coordinateBlocksPartial (is.map (fun i => (i,1))) F := by
  intro is
  induction is with
  | nil => intro h; exact False.elim (h rfl)
  | cons i is ih =>
    intro _
    by_cases his : is = []
    · subst is
      funext p
      change deriv (fun t : ℝ => c+F (Function.update p i t)) (p i) =
        deriv (fun t : ℝ => F (Function.update p i t)) (p i)
      exact deriv_const_add c
    · change coordinateIterate i 1 (coordinateBlocksPartial (is.map (fun j => (j,1))) (fun p => c+F p)) =
        coordinateIterate i 1 (coordinateBlocksPartial (is.map (fun j => (j,1))) F)
      rw [ih his]

theorem rs02CoordinateMultiPartial_const_add {d : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (alpha : Fin d → ℕ) (ha : alpha ≠ 0)
    (c : V) (F : (Fin d → ℝ) → V) :
    coordinateMultiPartial alpha (fun p => c+F p) = coordinateMultiPartial alpha F := by
  rw [coordinateMultiPartial_eq_unitBlocks,coordinateMultiPartial_eq_unitBlocks]
  apply rs02UnitBlocks_const_add c F
  intro hnil
  have hlen := congrArg List.length hnil
  rw [canonicalMultiIndexCoordinates_length] at hlen
  simp only [List.length_nil] at hlen
  exact (Nat.ne_of_gt (rs02MultiIndex_positive_order alpha ha)) hlen

end Froehlich
