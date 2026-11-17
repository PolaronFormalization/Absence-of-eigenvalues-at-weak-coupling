import Froehlich.Nodes.PT03KernelDefinitions
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false
noncomputable section
namespace Froehlich

/-- The larger open ball is used for ordinary derivatives at the closed
quarter-ball boundary. -/
theorem ke01_denominator_pos (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (P : GW.Space) (hP : ‖P‖ < 1/3) : 0 < 1+e-‖P‖^2 := by
  have hn := norm_nonneg P
  nlinarith [he.1]

theorem ke01_denominator_contDiffAt (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (t : GW.Space × (GW.Space × GW.Space)) (ht : ‖t.1‖ < 1/3) :
    ContDiffAt ℝ 3 (fun u : GW.Space × (GW.Space × GW.Space) =>
      (((1+e-‖u.1‖^2)⁻¹ : ℝ) : ℂ)) t := by
  have hd : ContDiff ℝ 3 (fun u : GW.Space × (GW.Space × GW.Space) => 1+e-‖u.1‖^2) :=
    contDiff_const.sub ((contDiff_norm_sq ℝ).comp contDiff_fst)
  have hi := hd.contDiffAt.inv (ne_of_gt (ke01_denominator_pos e he t.1 ht))
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp t hi

theorem ke01_denominator_contDiffAt_closedBall (e : ℝ)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (t : GW.Space × (GW.Space × GW.Space))
    (ht : ‖t.1‖ ≤ 1/4) :
    ContDiffAt ℝ 3 (fun u : GW.Space × (GW.Space × GW.Space) =>
      (((1+e-‖u.1‖^2)⁻¹ : ℝ) : ℂ)) t := by
  apply ke01_denominator_contDiffAt e he t
  linarith

end Froehlich
