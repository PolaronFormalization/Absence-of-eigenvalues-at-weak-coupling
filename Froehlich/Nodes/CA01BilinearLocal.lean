import Froehlich.Nodes.CA01BilinearJets
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! The scalar Pascal formula under local C^r hypotheses, without global
smoothness. This supplies each coordinate step of the multi-index assembly. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich
variable {V W Z : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem localContDiff_differentiable_iteratedDeriv
    (F : ℝ → V) (r i : ℕ) (t : ℝ) (hF : ContDiffAt ℝ r F t) (hi : i < r) :
    DifferentiableAt ℝ (iteratedDeriv i F) t := by
  have hd := hF.differentiableAt_iteratedFDeriv (m := i) (by exact_mod_cast hi)
  change DifferentiableAt ℝ (fun s => iteratedFDeriv ℝ i F s (fun _ : Fin i => (1 : ℝ))) t
  exact hd.continuousMultilinear_apply_const (fun _ : Fin i => (1 : ℝ))

theorem iteratedDeriv_realBilinear (B : V →L[ℝ] W →L[ℝ] Z)
    (F : ℝ → V) (G : ℝ → W) (r : ℕ) (t : ℝ)
    (hF : ContDiffAt ℝ r F t) (hG : ContDiffAt ℝ r G t) :
    iteratedDeriv r (fun s => B (F s) (G s)) t =
      ∑ i ∈ Finset.range (r+1), r.choose i •
        B (iteratedDeriv i F t) (iteratedDeriv (r-i) G t) := by
  have hnear := (hF.eventually (by simp)).and (hG.eventually (by simp))
  obtain ⟨T,hT,hFG⟩ := hnear.exists_mem
  obtain ⟨U,hUT,hU,ht⟩ := mem_nhds_iff.mp hT
  apply iteratedDeriv_bilinear_of_differentiable_iterates B F G U hU r
  · intro i hi s hs
    exact localContDiff_differentiable_iteratedDeriv F r i s (hFG s (hUT hs)).1 hi
  · intro i hi s hs
    exact localContDiff_differentiable_iteratedDeriv G r i s (hFG s (hUT hs)).2 hi
  · exact ht

end Froehlich
