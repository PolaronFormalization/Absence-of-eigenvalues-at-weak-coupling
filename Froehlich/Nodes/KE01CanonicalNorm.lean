import Froehlich.Nodes.KE01CanonicalNormTools
import Froehlich.Nodes.KE01CanonicalNormBasis
import Froehlich.Nodes.CA03VariableDifferences
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

set_option autoImplicit false
noncomputable section
namespace Froehlich
variable {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem canonicalMultiIndexCoordinates_count (alpha : Fin d → ℕ) (i : Fin d) :
    (canonicalMultiIndexCoordinates alpha).count i = alpha i := by
  classical
  simp [canonicalMultiIndexCoordinates,coordinateBlockIndices,List.count_flatMap,
    List.map_ofFn,List.sum_ofFn,List.count_replicate]

theorem coordinateWordPartial_canonical (is : List (Fin d)) :
    is.Perm (canonicalMultiIndexCoordinates (fun i => is.count i)) := by
  apply List.perm_iff_count.mpr
  intro i
  rw [canonicalMultiIndexCoordinates_count]

theorem coordinateMultiPartial_word (alpha : Fin d → ℕ) (F : (Fin d → ℝ) → V) :
    coordinateMultiPartial alpha F = coordinateWordPartial (canonicalMultiIndexCoordinates alpha) F := by
  rw [coordinateMultiPartial_eq_unitBlocks,coordinateWordPartial_unitBlocks]

theorem coordinateWordPartial_native_ofFn {k : ℕ} (is : Fin k → Fin d)
    (F : (Fin d → ℝ) → V) (hF : ContDiff ℝ k F) (q : Fin d → ℝ) :
    coordinateWordPartial (List.ofFn is) F q =
      iteratedFDeriv ℝ k F q (fun j => Pi.single (is j) 1) := by
  have hn := coordinateWordPartial_native (List.ofFn is) F
    (by simpa only [List.length_ofFn] using hF) q
  have hdir : listDirections (fun i : Fin d => (Pi.single i 1 : Fin d → ℝ)) (List.ofFn is) =
      (fun j => (Pi.single (is (Fin.cast (by simp) j)) 1 : Fin d → ℝ)) := by
    funext j
    rw [listDirections_eq_get,List.get_ofFn]
  rw [hdir] at hn
  have hc (n : ℕ) (h : n = k) :
      iteratedFDeriv ℝ n F q (fun j => Pi.single (is (Fin.cast h j)) 1) =
        iteratedFDeriv ℝ k F q (fun j => Pi.single (is j) 1) := by
    subst n
    rfl
  exact hn.trans (hc _ List.length_ofFn)

/-- Canonical partial bounds control the complete native derivative, with
the dimension-only factor d^k. Finite real Schwarz is proved in the tools
module; no analyticity or unprovided derivative estimates are assumed. -/
theorem iteratedFDeriv_norm_le_canonical (k : ℕ) (F : (Fin d → ℝ) → V)
    (hF : ContDiff ℝ k F) (K : ℝ) (hK : 0 ≤ K) (q : Fin d → ℝ)
    (hbound : ∀ alpha : Fin d → ℕ, (∑ i, alpha i) = k →
      ‖coordinateMultiPartial alpha F q‖ ≤ K) :
    ‖iteratedFDeriv ℝ k F q‖ ≤ (d : ℝ)^k*K := by
  apply multilinearMap_norm_le_coordinates d k _ K hK
  intro is
  rw [←coordinateWordPartial_native_ofFn is F hF q]
  let alpha : Fin d → ℕ := fun i => (List.ofFn is).count i
  have hp : (List.ofFn is).Perm (canonicalMultiIndexCoordinates alpha) :=
    coordinateWordPartial_canonical (List.ofFn is)
  have hdegree : (∑ i, alpha i) = k :=
    (canonicalMultiIndexCoordinates_length alpha).symm.trans
      (hp.length_eq.symm.trans (List.length_ofFn (f := is)))
  have hword := coordinateWordPartial_perm hp F (by simpa only [List.length_ofFn] using hF)
  rw [hword,←coordinateMultiPartial_word]
  exact hbound alpha hdegree

theorem coordinateMultiPartial_norm_le_iterated (alpha : Fin d → ℕ)
    (F : (Fin d → ℝ) → V) (hF : ContDiff ℝ (∑ i, alpha i : ℕ) F) (q : Fin d → ℝ) :
    ‖coordinateMultiPartial alpha F q‖ ≤ ‖iteratedFDeriv ℝ (∑ i, alpha i : ℕ) F q‖ := by
  classical
  rw [coordinateMultiPartial_word,coordinateWordPartial_native _ F
    (by simpa only [canonicalMultiIndexCoordinates_length] using hF)]
  have hp : (∏ j : Fin (canonicalMultiIndexCoordinates alpha).length,
      ‖listDirections (fun i : Fin d => (Pi.single i 1 : Fin d → ℝ))
        (canonicalMultiIndexCoordinates alpha) j‖) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    rw [listDirections_eq_get,Pi.norm_single,norm_one]
  have hb := (iteratedFDeriv ℝ (canonicalMultiIndexCoordinates alpha).length F q).le_opNorm
    (listDirections (fun i : Fin d => (Pi.single i 1 : Fin d → ℝ)) (canonicalMultiIndexCoordinates alpha))
  rw [hp,mul_one] at hb
  exact hb.trans_eq (congrArg (fun n : ℕ => ‖iteratedFDeriv ℝ n F q‖)
    (canonicalMultiIndexCoordinates_length alpha))

end Froehlich
