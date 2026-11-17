import Froehlich.Nodes.CA01MultiIndexBlocks

/-! Finite linearity of the genuine coordinate blocks. The regularity
hypotheses are needed because totalized derivatives need not be additive. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich
variable {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem coordinateIterate_sum {ι : Type*} (I : Finset ι) (i : Fin d) (n : ℕ)
    (F : ι → (Fin d → ℝ) → V) (q : Fin d → ℝ)
    (hF : ∀ a ∈ I, ContDiffAt ℝ n (F a) q) :
    coordinateIterate i n (fun p => ∑ a ∈ I, F a p) q =
      ∑ a ∈ I, coordinateIterate i n (F a) q := by
  have hf : ∀ a ∈ I, ContDiffAt ℝ n (fun s : ℝ => F a (Function.update q i s)) (q i) := by
    intro a ha
    have hfa : ContDiffAt ℝ n (F a) (Function.update q i (q i)) := by
      simpa only [Function.update_eq_self] using hF a ha
    exact hfa.comp (q i) ((contDiff_update (𝕜 := ℝ) n q i).contDiffAt)
  simpa only [coordinateIterate_eq_iteratedDeriv] using iteratedDeriv_fun_sum hf

theorem coordinateIterate_nsmul (i : Fin d) (n c : ℕ)
    (F : (Fin d → ℝ) → V) (q : Fin d → ℝ) (hF : ContDiffAt ℝ n F q) :
    coordinateIterate i n (fun p => c • F p) q = c • coordinateIterate i n F q := by
  have hf : ContDiffAt ℝ n (fun s : ℝ => F (Function.update q i s)) (q i) := by
    have hfa : ContDiffAt ℝ n F (Function.update q i (q i)) := by
      simpa only [Function.update_eq_self] using hF
    exact hfa.comp (q i) ((contDiff_update (𝕜 := ℝ) n q i).contDiffAt)
  simpa only [coordinateIterate_eq_iteratedDeriv] using iteratedDeriv_fun_const_smul hf c

end Froehlich
