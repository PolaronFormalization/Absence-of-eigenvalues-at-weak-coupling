import Froehlich.Nodes.GW05
import Froehlich.Nodes.FB02VacuumColumn

set_option autoImplicit false

/-! Pointwise cutoff coefficient adapters for scalar dominated convergence.
No uncut global L2 class or field limit is asserted. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich

theorem pt03_cutoffCoefficient_norm_le (g : ℝ) (Lambda : GW.Operators.PositiveCutoff) (k : GW.Space) :
    ‖(cutoffFormFactor g Lambda.val k : ℂ)‖ ≤ ‖(fiberFormFactor g k : ℂ)‖ := by
  by_cases hk : ‖k‖ ≤ Lambda.val
  · simp only [cutoffFormFactor,if_pos hk,le_refl]
  · simp only [cutoffFormFactor,if_neg hk,Complex.ofReal_zero,norm_zero]
    exact norm_nonneg _

theorem pt03_cutoffCoefficient_eventually_eq (g : ℝ) (k : GW.Space) :
    ∀ᶠ Lambda : GW.Operators.PositiveCutoff in atTop,
      (cutoffFormFactor g Lambda.val k : ℂ) = (fiberFormFactor g k : ℂ) := by
  have h := positiveCutoff_coe_tendsto.eventually (eventually_ge_atTop ‖k‖)
  filter_upwards [h] with Lambda hLambda
  simp only [cutoffFormFactor,if_pos hLambda]

theorem pt03_cutoffCoefficient_tendsto (g : ℝ) (k : GW.Space) :
    Tendsto (fun Lambda : GW.Operators.PositiveCutoff => (cutoffFormFactor g Lambda.val k : ℂ))
      atTop (𝓝 (fiberFormFactor g k : ℂ)) := by
  have heq : (fun Lambda : GW.Operators.PositiveCutoff => (cutoffFormFactor g Lambda.val k : ℂ))
      =ᶠ[atTop] (fun _ => (fiberFormFactor g k : ℂ)) := pt03_cutoffCoefficient_eventually_eq g k
  exact tendsto_const_nhds.congr' heq.symm

end Froehlich
