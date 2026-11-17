import Froehlich.Nodes.PT01FixedFreeForm
import Froehlich.Nodes.CV01FormRepresentatives
import Froehlich.Nodes.BA01

set_option autoImplicit false

/-! The literal shifted cutoff form on a fixed original high-energy graph. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem cutoffCommonFormOperator_fixed_representative (n : ℕ) (e : ℝ)
    (p0 p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (Λ : GW.Operators.PositiveCutoff) :
    cutoffCommonFormOperator n e p0 p hn he g Λ =
      (HighEnergySpace (-p0) n).subtypeL.adjoint.comp
        ((fixedFreeFormOperator (-p0) (-p) +
          formRepresentative (cutoffInteractionForm g Λ.val Λ.property (-p0))).comp
          (HighEnergySpace (-p0) n).subtypeL) -
      ((e-1+(n : ℝ) : ℝ) : ℂ) •
        ((highEnergyEmbedding (-p0) n).adjoint.comp (highEnergyEmbedding (-p0) n)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_left ℂ
  intro w
  rw [cutoffCommonFormOperator_spec]
  change (fiberFormData g (-p) (some Λ)).form
    (energyCoordinateChange (-p) (-p0) (w : EnergySpace (-p0)))
    (energyCoordinateChange (-p) (-p0) (u : EnergySpace (-p0))) - _ = _
  rw [fiberFormData_cutoff_apply,cutoffInteractionForm_change]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,inner_sub_right,
    inner_smul_right,ContinuousLinearMap.adjoint_inner_right,inner_add_right,
    fixedFreeFormOperator_spec,← formRepresentative_spec]
  rfl

end Froehlich
