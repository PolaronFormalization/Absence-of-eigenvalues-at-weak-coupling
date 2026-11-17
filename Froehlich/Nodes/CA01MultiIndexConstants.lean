import Froehlich.Nodes.CA01BlockProduct

/-! The zero derivative and the derivative of a constant in the canonical
ordered multi-index convention. These isolate the β=0 inverse term. -/
noncomputable section
namespace Froehlich
variable {d m : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem blockVectorPartial_zero (coords : Fin m → Fin d) (F : (Fin d → ℝ) → V) :
    blockVectorPartial coords 0 F = F := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [blockVectorPartial_cons]
    change coordinateIterate (coords 0) 0 (blockVectorPartial (Fin.tail coords) 0 F) = F
    rw [coordinateIterate_zero,ih]

theorem coordinateMultiPartial_zero (F : (Fin d → ℝ) → V) :
    coordinateMultiPartial 0 F = F := blockVectorPartial_zero id F

theorem coordinateIterate_const (i : Fin d) (n : ℕ) (c : V) (q : Fin d → ℝ) :
    coordinateIterate i n (fun _ => c) q = if n = 0 then c else 0 := by
  rw [coordinateIterate_eq_iteratedDeriv,iteratedDeriv_const]

theorem coordinateBlocksPartial_const (bs : List (Fin d × ℕ)) (c : V) :
    coordinateBlocksPartial bs (fun _ => c) =
      fun _ => if coordinateBlocksOrder bs = 0 then c else 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [coordinateBlocksPartial,ih]
    funext q
    rw [coordinateIterate_const]
    by_cases hb : b.2 = 0
    · simp only [hb,if_true,coordinateBlocksOrder,Nat.zero_add]
    · have hs : b.2 + coordinateBlocksOrder bs ≠ 0 := by omega
      simp only [hb,if_false,coordinateBlocksOrder,hs]

theorem coordinateMultiPartial_const (alpha : Fin d → ℕ) (halpha : alpha ≠ 0)
    (c : V) (q : Fin d → ℝ) : coordinateMultiPartial alpha (fun _ => c) q = 0 := by
  have hz : (∑ i, alpha i) ≠ 0 := by
    intro hs
    apply halpha
    funext i
    exact Finset.sum_eq_zero_iff.mp hs i (Finset.mem_univ i)
  rw [coordinateMultiPartial,coordinateBlocksPartial_const,coordinateBlocksOrder_ofFn,if_neg hz]

end Froehlich
