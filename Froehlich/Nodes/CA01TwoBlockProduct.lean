import Froehlich.Nodes.CA01BlockLinearity

/-! Exact two-block specialization of the multi-index Leibniz formula.
The coordinate labels may coincide; no exchange of mixed derivatives occurs. -/
noncomputable section
open scoped Topology
namespace Froehlich
variable {d : ℕ} {V W Z : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem coordinateIterate_twoBlocks_realBilinear
    (i j : Fin d) (n m : ℕ) (B : V →L[ℝ] W →L[ℝ] Z)
    (F : (Fin d → ℝ) → V) (G : (Fin d → ℝ) → W)
    (S : Set (Fin d → ℝ)) (hS : IsOpen S)
    (hF : ContDiffOn ℝ (n+m : ℕ) F S) (hG : ContDiffOn ℝ (n+m : ℕ) G S)
    (q : Fin d → ℝ) (hq : q ∈ S) :
    coordinateIterate i n (coordinateIterate j m (fun p => B (F p) (G p))) q =
      ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (n+1),
        (m.choose k * n.choose l) •
          B (coordinateIterate i l (coordinateIterate j k F) q)
            (coordinateIterate i (n-l) (coordinateIterate j (m-k) G) q) := by
  have hleft : ∀ k ≤ m, ContDiffOn ℝ n (coordinateIterate j k F) S := by
    intro k hk
    exact coordinateIterate_contDiffOn j k n F S hS
      (hF.of_le (by exact_mod_cast (Nat.add_le_add_left hk n)))
  have hright : ∀ k ≤ m, ContDiffOn ℝ n (coordinateIterate j (m-k) G) S := by
    intro k hk
    exact coordinateIterate_contDiffOn j (m-k) n G S hS
      (hG.of_le (by exact_mod_cast (Nat.add_le_add_left (Nat.sub_le m k) n)))
  have hterm : ∀ k ∈ Finset.range (m+1),
      ContDiffOn ℝ n
        (fun p => B (coordinateIterate j k F p) (coordinateIterate j (m-k) G p)) S := by
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact (contDiffOn_const.clm_apply (hleft k hkm)).clm_apply (hright k hkm)
  have heq : Set.EqOn (coordinateIterate j m (fun p => B (F p) (G p)))
      (fun p => ∑ k ∈ Finset.range (m+1), m.choose k •
        B (coordinateIterate j k F p) (coordinateIterate j (m-k) G p)) S := by
    intro p hp
    have hfm : ContDiffOn ℝ m F S := hF.of_le (by exact_mod_cast (Nat.le_add_left m n))
    have hgm : ContDiffOn ℝ m G S := hG.of_le (by exact_mod_cast (Nat.le_add_left m n))
    exact coordinateIterate_realBilinear j m B F G p
      ((hfm p hp).contDiffAt (hS.mem_nhds hp))
      ((hgm p hp).contDiffAt (hS.mem_nhds hp))
  rw [coordinateIterate_congr_of_isOpen i n _ _ S hS heq hq]
  rw [coordinateIterate_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    have hkn := ((hterm k hk) q hq).contDiffAt (hS.mem_nhds hq)
    rw [coordinateIterate_nsmul i n (m.choose k) _ q hkn]
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [coordinateIterate_realBilinear i n B _ _ q
      (((hleft k hkm) q hq).contDiffAt (hS.mem_nhds hq))
      (((hright k hkm) q hq).contDiffAt (hS.mem_nhds hq))]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    rw [← mul_smul]
  · intro k hk
    exact ((ContDiffOn.const_smul (m.choose k) (hterm k hk)) q hq).contDiffAt (hS.mem_nhds hq)

end Froehlich
