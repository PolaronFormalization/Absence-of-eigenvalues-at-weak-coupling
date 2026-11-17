import Froehlich.Nodes.CA01InverseFamily
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Scalar-coordinate specialization of the source inverse recurrence.
Mandatory reuse: `iteratedDeriv_mul` / `iteratedDeriv_fun_mul` from
Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas, rather than another
higher multiplication rule. All endomorphisms are the same End_ℂ carrier. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich
open scoped BoundedEndReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem actualInverseFamily_iteratedDeriv
    (M R : ℝ → E →L[ℂ] E) (t : ℝ) (n : ℕ) (hn : n ≠ 0)
    (hM : ContDiffAt ℝ n M t)
    (hinv : ∀ᶠ s in 𝓝 t, M s * R s = 1 ∧ R s * M s = 1) :
    iteratedDeriv n R t = -R t *
      ∑ j ∈ Finset.range n, (n.choose (j+1) : E →L[ℂ] E) *
        iteratedDeriv (j+1) M t * iteratedDeriv (n-(j+1)) R t := by
  have hR : ContDiffAt ℝ n R t := actualInverseFamily_contDiffAt M R t n hM hinv
  have hnear : (fun s : ℝ => M s * R s) =ᶠ[𝓝 t] fun _ => (1 : E →L[ℂ] E) :=
    hinv.mono (fun _ hs => hs.1)
  have hzero : iteratedDeriv n (fun s : ℝ => M s * R s) t = 0 :=
    (hnear.iteratedDeriv_eq n).trans (by simp only [iteratedDeriv_const,if_neg hn])
  have hLeib := iteratedDeriv_fun_mul hM hR
  have hsum : (∑ j ∈ Finset.range (n+1), (n.choose j : E →L[ℂ] E) *
      iteratedDeriv j M t * iteratedDeriv (n-j) R t) = 0 := hLeib.symm.trans hzero
  rw [Finset.sum_range_succ'] at hsum
  have hs : (∑ j ∈ Finset.range n, (n.choose (j+1) : E →L[ℂ] E) *
      iteratedDeriv (j+1) M t * iteratedDeriv (n-(j+1)) R t) +
      M t * iteratedDeriv n R t = 0 := by
    simpa only [Nat.choose_zero_right,Nat.cast_one,one_mul,iteratedDeriv_zero,Nat.sub_zero] using hsum
  have hterm : M t * iteratedDeriv n R t =
      -(∑ j ∈ Finset.range n, (n.choose (j+1) : E →L[ℂ] E) *
        iteratedDeriv (j+1) M t * iteratedDeriv (n-(j+1)) R t) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using hs
  calc
    iteratedDeriv n R t = R t * (M t * iteratedDeriv n R t) := by
      rw [← mul_assoc,hinv.self_of_nhds.2,one_mul]
    _ = R t * -(∑ j ∈ Finset.range n, (n.choose (j+1) : E →L[ℂ] E) *
        iteratedDeriv (j+1) M t * iteratedDeriv (n-(j+1)) R t) := congrArg (fun z => R t * z) hterm
    _ = _ := by rw [mul_neg,neg_mul]

end Froehlich
