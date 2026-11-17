import Froehlich.Nodes.CA01Inverse
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Native real calculus for a chosen family of actual bounded inverses. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich
open scoped BoundedEndReal
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem actualInverseFamily_eventuallyEq
    (M R : D → E →L[ℂ] E) (p : D)
    (hinv : ∀ᶠ q in 𝓝 p, M q * R q = 1 ∧ R q * M q = 1) :
    R =ᶠ[𝓝 p] fun q => Ring.inverse (M q) := by
  filter_upwards [hinv] with q hq
  exact (actualInverse_ringInverse (M q) (R q) hq.1 hq.2).symm

theorem actualInverseFamily_hasFDerivAt
    (M R : D → E →L[ℂ] E) (M' : D →L[ℝ] E →L[ℂ] E) (p : D)
    (hM : HasFDerivAt M M' p)
    (hinv : ∀ᶠ q in 𝓝 p, M q * R q = 1 ∧ R q * M q = 1) :
    HasFDerivAt R
      ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℂ] E) (R p) (R p)).comp M') p := by
  have hp := hinv.self_of_nhds
  exact ((actualInverse_hasFDerivAt (M p) (R p) hp.1 hp.2).comp p hM).congr_of_eventuallyEq
    (actualInverseFamily_eventuallyEq M R p hinv)

theorem actualInverseFamily_derivative_apply
    (M' : D →L[ℝ] E →L[ℂ] E) (R : E →L[ℂ] E) (h : D) :
    ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℂ] E) R R).comp M') h =
      -R * M' h * R := actualInverse_derivative_apply R (M' h)

theorem actualInverseFamily_contDiffAt
    (M R : D → E →L[ℂ] E) (p : D) (n : WithTop ENat)
    (hM : ContDiffAt ℝ n M p)
    (hinv : ∀ᶠ q in 𝓝 p, M q * R q = 1 ∧ R q * M q = 1) :
    ContDiffAt ℝ n R p := by
  have hp := hinv.self_of_nhds
  exact ((contDiffAt_ringInverse ℝ (actualInverseUnit (M p) (R p) hp.1 hp.2)).comp p hM).congr_of_eventuallyEq
    (actualInverseFamily_eventuallyEq M R p hinv)

end Froehlich
