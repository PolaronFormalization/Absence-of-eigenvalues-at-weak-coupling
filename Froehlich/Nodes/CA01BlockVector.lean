import Froehlich.Nodes.CA01CoefficientBox
import Froehlich.Nodes.CA01TwoBlockProduct
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Finite ordered block vectors and the exact recursive coefficient box.
The vector length and ambient coordinate dimension need not agree. -/
noncomputable section
namespace Froehlich
variable {d m : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def blockVectorPartial (coords : Fin m → Fin d) (alpha : Fin m → ℕ)
    (F : (Fin d → ℝ) → V) : (Fin d → ℝ) → V :=
  coordinateBlocksPartial (List.ofFn (fun k => (coords k,alpha k))) F

theorem blockVectorPartial_cons (coords : Fin (m+1) → Fin d)
    (alpha : Fin (m+1) → ℕ) (F : (Fin d → ℝ) → V) :
    blockVectorPartial coords alpha F = coordinateIterate (coords 0) (alpha 0)
      (blockVectorPartial (Fin.tail coords) (Fin.tail alpha) F) := by
  simp only [blockVectorPartial,List.ofFn_succ,coordinateBlocksPartial,Fin.tail]

theorem coordinateBlocksOrder_ofFn_labels (coords : Fin m → Fin d) (alpha : Fin m → ℕ) :
    coordinateBlocksOrder (List.ofFn (fun k => (coords k,alpha k))) = ∑ k, alpha k := by
  have h : ∀ (bs : List (Fin d × ℕ)),
      coordinateBlocksOrder bs = (bs.map Prod.snd).sum := by
    intro bs
    induction bs with
    | nil => rfl
    | cons b bs hb => simp only [coordinateBlocksOrder,List.map_cons,List.sum_cons,hb]
  rw [h,List.map_ofFn]
  change (List.ofFn alpha).sum = ∑ k, alpha k
  exact List.sum_ofFn

theorem blockVectorPartial_contDiffOn (coords : Fin m → Fin d) (alpha : Fin m → ℕ)
    (n : ℕ) (F : (Fin d → ℝ) → V) (S : Set (Fin d → ℝ)) (hS : IsOpen S)
    (hF : ContDiffOn ℝ (n+∑ k, alpha k : ℕ) F S) :
    ContDiffOn ℝ n (blockVectorPartial coords alpha F) S := by
  apply coordinateBlocksPartial_contDiffOn _ n F S hS
  simpa only [coordinateBlocksOrder_ofFn_labels] using hF

theorem multiIndexBox_sum_cons {A : Type*} [AddCommMonoid A]
    (alpha : Fin (m+1) → ℕ) (H : (Fin (m+1) → ℕ) → A) :
    (∑ beta ∈ multiIndexBox alpha, H beta) =
      ∑ k ∈ Finset.range (alpha 0+1), ∑ beta ∈ multiIndexBox (Fin.tail alpha), H (Fin.cons k beta) := by
  classical
  calc
    _ = ∑ b ∈ (Finset.range (alpha 0+1)).product (multiIndexBox (Fin.tail alpha)),
        H (Fin.cons b.1 b.2) := by
      apply Finset.sum_nbij' (fun beta => (beta 0,Fin.tail beta))
        (fun b => Fin.cons b.1 b.2)
      · intro beta hb
        have h := (mem_multiIndexBox alpha beta).mp hb
        exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (h 0)),
          (mem_multiIndexBox _ _).mpr (fun i => h i.succ)⟩
      · intro b hb
        obtain ⟨hk,hb⟩ := Finset.mem_product.mp hb
        apply (mem_multiIndexBox alpha _).mpr
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        · exact (mem_multiIndexBox _ _).mp hb j
      · intro beta hb
        exact Fin.cons_self_tail beta
      · intro b hb
        rcases b with ⟨k,beta⟩
        simp only [Fin.cons_zero,Fin.tail_cons]
      · intro beta hb
        exact congrArg H (Fin.cons_self_tail beta).symm
    _ = _ := Finset.sum_product _ _ _

theorem multiIndexBinomial_cons (alpha : Fin (m+1) → ℕ) (k : ℕ) (beta : Fin m → ℕ) :
    multiIndexBinomial alpha (Fin.cons k beta) =
      (alpha 0).choose k * multiIndexBinomial (Fin.tail alpha) beta := by
  simp only [multiIndexBinomial,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,Fin.tail]

end Froehlich
