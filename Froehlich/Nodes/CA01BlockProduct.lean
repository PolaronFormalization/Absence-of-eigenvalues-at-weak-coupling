import Froehlich.Nodes.CA01BlockVector

/-! The full ordered multi-block Leibniz formula. Its coefficient box is
literal β ≤ α, and its coefficient is the product of coordinate binomials. -/
noncomputable section
open scoped Topology
namespace Froehlich
variable {d m : ℕ} {V W Z : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem blockVectorPartial_realBilinear
    (coords : Fin m → Fin d) (alpha : Fin m → ℕ)
    (B : V →L[ℝ] W →L[ℝ] Z)
    (F : (Fin d → ℝ) → V) (G : (Fin d → ℝ) → W)
    (S : Set (Fin d → ℝ)) (hS : IsOpen S)
    (hF : ContDiffOn ℝ (∑ k, alpha k : ℕ) F S)
    (hG : ContDiffOn ℝ (∑ k, alpha k : ℕ) G S)
    (q : Fin d → ℝ) (hq : q ∈ S) :
    blockVectorPartial coords alpha (fun p => B (F p) (G p)) q =
      ∑ beta ∈ multiIndexBox alpha, multiIndexBinomial alpha beta •
        B (blockVectorPartial coords beta F q)
          (blockVectorPartial coords (fun k => alpha k-beta k) G q) := by
  classical
  induction m generalizing q with
  | zero =>
    have hb : multiIndexBox alpha = {0} := by
      ext beta
      simp only [mem_multiIndexBox,Finset.mem_singleton]
      constructor
      · intro h
        funext k
        exact Fin.elim0 k
      · intro h k
        exact Fin.elim0 k
    rw [hb,Finset.sum_singleton,multiIndexBinomial_zero,one_smul]
    rfl
  | succ m ih =>
    let a : Fin m → ℕ := Fin.tail alpha
    let c : Fin m → Fin d := Fin.tail coords
    let n := alpha 0
    have hFn : ContDiffOn ℝ (n+∑ k, a k : ℕ) F S := by
      simpa only [Fin.sum_univ_succ,n,a,Fin.tail] using hF
    have hGn : ContDiffOn ℝ (n+∑ k, a k : ℕ) G S := by
      simpa only [Fin.sum_univ_succ,n,a,Fin.tail] using hG
    have hFtail : ContDiffOn ℝ (∑ k, a k : ℕ) F S :=
      hFn.of_le (by exact_mod_cast (Nat.le_add_left (∑ k, a k) n))
    have hGtail : ContDiffOn ℝ (∑ k, a k : ℕ) G S :=
      hGn.of_le (by exact_mod_cast (Nat.le_add_left (∑ k, a k) n))
    have hleft : ∀ beta ∈ multiIndexBox a, ContDiffOn ℝ n (blockVectorPartial c beta F) S := by
      intro beta hb
      have hsum : (∑ k, beta k) ≤ ∑ k, a k :=
        Finset.sum_le_sum (fun k _ => (mem_multiIndexBox a beta).mp hb k)
      exact blockVectorPartial_contDiffOn c beta n F S hS
        (hFn.of_le (by exact_mod_cast (Nat.add_le_add_left hsum n)))
    have hright : ∀ beta ∈ multiIndexBox a,
        ContDiffOn ℝ n (blockVectorPartial c (fun k => a k-beta k) G) S := by
      intro beta hb
      have hsum : (∑ k, (a k-beta k)) ≤ ∑ k, a k :=
        Finset.sum_le_sum (fun k _ => Nat.sub_le _ _)
      exact blockVectorPartial_contDiffOn c (fun k => a k-beta k) n G S hS
        (hGn.of_le (by exact_mod_cast (Nat.add_le_add_left hsum n)))
    have hterm : ∀ beta ∈ multiIndexBox a,
        ContDiffOn ℝ n (fun p => B (blockVectorPartial c beta F p)
          (blockVectorPartial c (fun k => a k-beta k) G p)) S := by
      intro beta hb
      exact (contDiffOn_const.clm_apply (hleft beta hb)).clm_apply (hright beta hb)
    have heq : Set.EqOn (blockVectorPartial c a (fun p => B (F p) (G p)))
        (fun p => ∑ beta ∈ multiIndexBox a, multiIndexBinomial a beta •
          B (blockVectorPartial c beta F p)
            (blockVectorPartial c (fun k => a k-beta k) G p)) S := by
      intro p hp
      exact ih c a hFtail hGtail p hp
    calc
      _ = coordinateIterate (coords 0) n
          (fun p => ∑ beta ∈ multiIndexBox a, multiIndexBinomial a beta •
            B (blockVectorPartial c beta F p)
              (blockVectorPartial c (fun k => a k-beta k) G p)) q := by
        rw [blockVectorPartial_cons]
        exact coordinateIterate_congr_of_isOpen (coords 0) n _ _ S hS heq hq
      _ = ∑ beta ∈ multiIndexBox a, multiIndexBinomial a beta •
          coordinateIterate (coords 0) n
            (fun p => B (blockVectorPartial c beta F p)
              (blockVectorPartial c (fun k => a k-beta k) G p)) q := by
        rw [coordinateIterate_sum]
        · apply Finset.sum_congr rfl
          intro beta hb
          exact coordinateIterate_nsmul _ _ _ _ _
            (((hterm beta hb) q hq).contDiffAt (hS.mem_nhds hq))
        · intro beta hb
          exact ((ContDiffOn.const_smul (multiIndexBinomial a beta) (hterm beta hb)) q hq).contDiffAt
            (hS.mem_nhds hq)
      _ = ∑ beta ∈ multiIndexBox a, ∑ k ∈ Finset.range (n+1),
          (n.choose k * multiIndexBinomial a beta) •
            B (coordinateIterate (coords 0) k (blockVectorPartial c beta F) q)
              (coordinateIterate (coords 0) (n-k)
                (blockVectorPartial c (fun l => a l-beta l) G) q) := by
        apply Finset.sum_congr rfl
        intro beta hb
        rw [coordinateIterate_realBilinear _ _ B _ _ q
          (((hleft beta hb) q hq).contDiffAt (hS.mem_nhds hq))
          (((hright beta hb) q hq).contDiffAt (hS.mem_nhds hq)),Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [← mul_smul,Nat.mul_comm]
      _ = ∑ k ∈ Finset.range (n+1), ∑ beta ∈ multiIndexBox a,
          (n.choose k * multiIndexBinomial a beta) •
            B (coordinateIterate (coords 0) k (blockVectorPartial c beta F) q)
              (coordinateIterate (coords 0) (n-k)
                (blockVectorPartial c (fun l => a l-beta l) G) q) := Finset.sum_comm
      _ = _ := by
        rw [multiIndexBox_sum_cons]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro beta hb
        rw [multiIndexBinomial_cons]
        simp only [blockVectorPartial_cons,Fin.cons_zero,Fin.tail_cons]
        rfl

/-- The source's canonical increasing-coordinate multi-index product rule. -/
theorem coordinateMultiPartial_realBilinear (alpha : Fin d → ℕ)
    (B : V →L[ℝ] W →L[ℝ] Z)
    (F : (Fin d → ℝ) → V) (G : (Fin d → ℝ) → W)
    (S : Set (Fin d → ℝ)) (hS : IsOpen S)
    (hF : ContDiffOn ℝ (∑ k, alpha k : ℕ) F S)
    (hG : ContDiffOn ℝ (∑ k, alpha k : ℕ) G S)
    (q : Fin d → ℝ) (hq : q ∈ S) :
    coordinateMultiPartial alpha (fun p => B (F p) (G p)) q =
      ∑ beta ∈ multiIndexBox alpha, multiIndexBinomial alpha beta •
        B (coordinateMultiPartial beta F q)
          (coordinateMultiPartial (fun k => alpha k-beta k) G q) :=
  blockVectorPartial_realBilinear id alpha B F G S hS hF hG q hq

end Froehlich
