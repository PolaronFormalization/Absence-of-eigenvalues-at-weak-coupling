import Froehlich.Nodes.UV01
import Froehlich.Nodes.FB02Transport

/-! Actual compressed shifted forms represented on one fixed original
energy graph. Their difference is the literal cutoff interaction tail. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p0 p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ)

def cutoffCommonFormOperator (Λ : GW.Operators.PositiveCutoff) :
    HighEnergySpace (-p0) n →L[ℂ] HighEnergySpace (-p0) n :=
  (highEnergyCoordinateChange (-p) (-p0) n).adjoint.comp
    ((cutoffCompressedEnergyOperator n e p hn he Λ g).comp (highEnergyCoordinateChange (-p) (-p0) n))

def singularCommonFormOperator : HighEnergySpace (-p0) n →L[ℂ] HighEnergySpace (-p0) n :=
  (highEnergyCoordinateChange (-p) (-p0) n).adjoint.comp
    ((auxiliaryCompressedEnergyOperator n e p hn he g).comp (highEnergyCoordinateChange (-p) (-p0) n))

theorem cutoffCommonFormOperator_spec (Λ : GW.Operators.PositiveCutoff) (w u : HighEnergySpace (-p0) n) :
    ⟪w,cutoffCommonFormOperator n e p0 p hn he g Λ u⟫_ℂ =
      (compressedFiberFormData g (-p) n (some Λ)).form
        (highEnergyCoordinateChange (-p) (-p0) n w) (highEnergyCoordinateChange (-p) (-p0) n u) -
      ((e-1+(n : ℝ) : ℝ) : ℂ)*⟪highEnergyEmbedding (-p0) n w,highEnergyEmbedding (-p0) n u⟫_ℂ := by
  change ⟪w,(highEnergyCoordinateChange (-p) (-p0) n).adjoint _⟫_ℂ = _
  rw [(highEnergyCoordinateChange (-p) (-p0) n).adjoint_inner_right]
  have hs := cutoffCompressedEnergyOperator_spec n e p hn he Λ g
    (highEnergyCoordinateChange (-p) (-p0) n w) (highEnergyCoordinateChange (-p) (-p0) n u)
  simpa only [highEnergyCoordinateChange_physical] using! hs

theorem singularCommonFormOperator_spec (w u : HighEnergySpace (-p0) n) :
    ⟪w,singularCommonFormOperator n e p0 p hn he g u⟫_ℂ =
      (compressedFiberFormData g (-p) n none).form
        (highEnergyCoordinateChange (-p) (-p0) n w) (highEnergyCoordinateChange (-p) (-p0) n u) -
      ((e-1+(n : ℝ) : ℝ) : ℂ)*⟪highEnergyEmbedding (-p0) n w,highEnergyEmbedding (-p0) n u⟫_ℂ := by
  change ⟪w,(highEnergyCoordinateChange (-p) (-p0) n).adjoint _⟫_ℂ = _
  rw [(highEnergyCoordinateChange (-p) (-p0) n).adjoint_inner_right]
  have hs := auxiliaryCompressedEnergyOperator_spec n e p hn he g
    (highEnergyCoordinateChange (-p) (-p0) n w) (highEnergyCoordinateChange (-p) (-p0) n u)
  simpa only [highEnergyCoordinateChange_physical] using! hs

theorem commonFormOperator_difference_inner (Λ : GW.Operators.PositiveCutoff) (w u : HighEnergySpace (-p0) n) :
    ⟪w,(cutoffCommonFormOperator n e p0 p hn he g Λ-singularCommonFormOperator n e p0 p hn he g) u⟫_ℂ =
      cutoffInteractionForm g Λ.val Λ.property (-p0) w u-singularInteraction g (-p0) w u := by
  change ⟪w,cutoffCommonFormOperator n e p0 p hn he g Λ u-singularCommonFormOperator n e p0 p hn he g u⟫_ℂ = _
  rw [inner_sub_right,cutoffCommonFormOperator_spec,singularCommonFormOperator_spec]
  change (fiberFormData g (-p) (some Λ)).form
    (energyCoordinateChange (-p) (-p0) (w : EnergySpace (-p0)))
    (energyCoordinateChange (-p) (-p0) (u : EnergySpace (-p0))) - _ -
    ((fiberFormData g (-p) none).form
      (energyCoordinateChange (-p) (-p0) (w : EnergySpace (-p0)))
      (energyCoordinateChange (-p) (-p0) (u : EnergySpace (-p0))) - _) = _
  rw [fiberFormData_cutoff_apply,fiberFormData_singular_apply,cutoffInteractionForm_change,singularInteraction_change]
  ring

end Froehlich
