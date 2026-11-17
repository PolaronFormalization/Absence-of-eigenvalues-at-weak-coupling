import Froehlich.Nodes.CA01MultiIndexBlocks
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin

/-! The literal finite box and coefficients in the source multi-index rules.
No extra indices outside β ≤ α are included; the zero term is isolated
separately for the inverse recurrence. -/
noncomputable section
namespace Froehlich
variable {d : ℕ}

def multiIndexBox (alpha : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun i => Finset.range (alpha i+1))

def multiIndexBinomial (alpha beta : Fin d → ℕ) : ℕ :=
  ∏ i, (alpha i).choose (beta i)

theorem mem_multiIndexBox (alpha beta : Fin d → ℕ) :
    beta ∈ multiIndexBox alpha ↔ ∀ i, beta i ≤ alpha i := by
  simp only [multiIndexBox,Fintype.mem_piFinset,Finset.mem_range,Nat.lt_succ_iff]

theorem zero_mem_multiIndexBox (alpha : Fin d → ℕ) :
    (0 : Fin d → ℕ) ∈ multiIndexBox alpha :=
  (mem_multiIndexBox alpha 0).mpr (fun _ => Nat.zero_le _)

theorem multiIndexBinomial_zero (alpha : Fin d → ℕ) :
    multiIndexBinomial alpha 0 = 1 := by
  simp [multiIndexBinomial]

theorem multiIndexBinomial_self (alpha : Fin d → ℕ) :
    multiIndexBinomial alpha alpha = 1 := by
  simp [multiIndexBinomial]

theorem coordinateBlocksOrder_ofFn (alpha : Fin d → ℕ) :
    coordinateBlocksOrder (List.ofFn (fun i : Fin d => (i,alpha i))) = ∑ i, alpha i := by
  have h : ∀ (bs : List (Fin d × ℕ)),
      coordinateBlocksOrder bs = (bs.map Prod.snd).sum := by
    intro bs
    induction bs with
    | nil => rfl
    | cons b bs hb => simp only [coordinateBlocksOrder,List.map_cons,List.sum_cons,hb]
  rw [h,List.map_ofFn]
  change (List.ofFn alpha).sum = ∑ i, alpha i
  exact List.sum_ofFn

theorem multiIndexBox_sum_split_zero {V : Type*} [AddCommMonoid V]
    (alpha : Fin d → ℕ) (F : (Fin d → ℕ) → V) :
    (∑ beta ∈ multiIndexBox alpha, F beta) =
      F 0 + ∑ beta ∈ (multiIndexBox alpha).erase 0, F beta := by
  classical
  exact (Finset.add_sum_erase _ F (zero_mem_multiIndexBox alpha)).symm

end Froehlich
