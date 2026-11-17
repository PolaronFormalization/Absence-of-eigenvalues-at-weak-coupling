import Froehlich.Nodes.CA01Bilinear
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Sum

/-! Exact Pascal coefficients for real bilinear differentiation.
The jet hypotheses assert genuine norm derivatives on an open set; they
are not a hypothesis of a product rule. Canonical multi-index assembly is
kept separate from this scalar induction. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich
variable {V W Z : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def binomialProductJet (B : V →L[ℝ] W →L[ℝ] Z)
    (F : ℕ → ℝ → V) (G : ℕ → ℝ → W) (n : ℕ) (t : ℝ) : Z :=
  ∑ i ∈ Finset.range (n+1), n.choose i • B (F i t) (G (n-i) t)

theorem binomialProductJet_hasDerivAt (B : V →L[ℝ] W →L[ℝ] Z)
    (F : ℕ → ℝ → V) (G : ℕ → ℝ → W) (n : ℕ) (t : ℝ)
    (hF : ∀ i ≤ n, HasDerivAt (F i) (F (i+1) t) t)
    (hG : ∀ i ≤ n, HasDerivAt (G i) (G (i+1) t) t) :
    HasDerivAt (binomialProductJet B F G n) (binomialProductJet B F G (n+1) t) t := by
  have hterm : ∀ i ∈ Finset.range (n+1),
      HasDerivAt (fun s : ℝ => n.choose i • B (F i s) (G (n-i) s))
        (n.choose i • (B (F (i+1) t) (G (n-i) t) + B (F i t) (G (n-i+1) t))) t := by
    intro i hi
    have hn : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hd := (realBilinear_hasDerivAt B (F i) (G (n-i)) _ _ t
      (hF i hn) (hG (n-i) (Nat.sub_le n i))).const_smul (n.choose i)
    convert hd using 1
  have hs := HasDerivAt.fun_sum hterm
  have he : binomialProductJet B F G (n+1) t =
      ∑ i ∈ Finset.range (n+1), n.choose i •
        (B (F (i+1) t) (G (n-i) t) + B (F i t) (G (n-i+1) t)) := by
    have hp := Finset.sum_choose_succ_nsmul (fun i j => B (F i t) (G j t)) n
    change (∑ i ∈ Finset.range (n+2), (n+1).choose i • B (F i t) (G (n+1-i) t)) = _
    rw [hp,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hn : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hsub : n+1-i = n-i+1 := by omega
    rw [hsub,smul_add]
    exact add_comm _ _
  rw [← he] at hs
  exact hs

theorem iteratedDeriv_bilinear_of_jets (B : V →L[ℝ] W →L[ℝ] Z)
    (F : ℕ → ℝ → V) (G : ℕ → ℝ → W) (U : Set ℝ) (hU : IsOpen U) (r : ℕ)
    (hF : ∀ i < r, ∀ t ∈ U, HasDerivAt (F i) (F (i+1) t) t)
    (hG : ∀ i < r, ∀ t ∈ U, HasDerivAt (G i) (G (i+1) t) t) :
    ∀ n ≤ r, ∀ t ∈ U,
      iteratedDeriv n (fun s => B (F 0 s) (G 0 s)) t = binomialProductJet B F G n t := by
  intro n
  induction n with
  | zero =>
    intro hn t ht
    simp only [binomialProductJet,iteratedDeriv_zero,Nat.zero_add,Finset.range_one,
      Finset.sum_singleton,Nat.choose_self,Nat.sub_self,one_smul]
  | succ n ih =>
    intro hn t ht
    have he : iteratedDeriv n (fun s => B (F 0 s) (G 0 s)) =ᶠ[𝓝 t]
        binomialProductJet B F G n := by
      filter_upwards [hU.mem_nhds ht] with s hs
      exact ih (by omega) s hs
    have hd := binomialProductJet_hasDerivAt B F G n t
      (fun i hi => hF i (by omega) t ht) (fun i hi => hG i (by omega) t ht)
    rw [iteratedDeriv_succ]
    exact (hd.congr_of_eventuallyEq he).deriv

theorem iteratedDeriv_bilinear_of_differentiable_iterates
    (B : V →L[ℝ] W →L[ℝ] Z) (F : ℝ → V) (G : ℝ → W)
    (U : Set ℝ) (hU : IsOpen U) (r : ℕ)
    (hF : ∀ i < r, ∀ t ∈ U, DifferentiableAt ℝ (iteratedDeriv i F) t)
    (hG : ∀ i < r, ∀ t ∈ U, DifferentiableAt ℝ (iteratedDeriv i G) t)
    (t : ℝ) (ht : t ∈ U) :
    iteratedDeriv r (fun s => B (F s) (G s)) t =
      ∑ i ∈ Finset.range (r+1), r.choose i • B (iteratedDeriv i F t) (iteratedDeriv (r-i) G t) := by
  have hf : ∀ i < r, ∀ s ∈ U,
      HasDerivAt (iteratedDeriv i F) (iteratedDeriv (i+1) F s) s := by
    intro i hi s hs
    rw [iteratedDeriv_succ]
    exact (hF i hi s hs).hasDerivAt
  have hg : ∀ i < r, ∀ s ∈ U,
      HasDerivAt (iteratedDeriv i G) (iteratedDeriv (i+1) G s) s := by
    intro i hi s hs
    rw [iteratedDeriv_succ]
    exact (hG i hi s hs).hasDerivAt
  simpa only [iteratedDeriv_zero,binomialProductJet] using
    iteratedDeriv_bilinear_of_jets B (fun i => iteratedDeriv i F)
      (fun i => iteratedDeriv i G) U hU r hf hg r le_rfl t ht

end Froehlich
