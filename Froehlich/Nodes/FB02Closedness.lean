import Froehlich.Nodes.GW06Action

/-! The actual shifted form norm is complete and has the original physical
form domain; semiboundedness holds for every real coupling. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem fiberShiftedForm_complete (g : ℝ) (P : GW.Space) :
    CompleteSpace (GW.Operators.EnergySpace (fiberFormData g P none)) := inferInstance

theorem fiberShiftedForm_norm_sq (g : ℝ) (P : GW.Space) (x : EnergySpace P) :
    ‖(GW.Operators.energyCoordinates (fiberFormData g P none)).symm x‖^2 =
      ((fiberFormData g P none).form x x).re + (lyGlobalRemainder g+1)*‖energyEmbedding P x‖^2 := by
  have h := GW.Operators.energy_norm_sq (fiberFormData g P none)
    ((GW.Operators.energyCoordinates (fiberFormData g P none)).symm x)
  rw [LinearEquiv.apply_symm_apply,GW.Operators.energyForm_diagonal_re] at h
  exact h

theorem fiberForm_completion_range (g : ℝ) (P : GW.Space) :
    Set.range (GW.Operators.completedEnergyEmbedding (fiberFormData g P none)) =
      Set.range (energyEmbedding P) :=
  GW.Operators.completedEnergyEmbedding_range (fiberFormData g P none)

theorem fiberForm_semibounded (g : ℝ) (P : GW.Space) (x : EnergySpace P) :
    -(lyGlobalRemainder g)*‖energyEmbedding P x‖^2 ≤ ((fiberFormData g P none).form x x).re := by
  have hd := GW.Operators.uniformLimitForm_diagonal (fiberUniformData g P) x
  change ‖singularInteraction g P x x‖ ≤
    (1/2 : ℝ)*(freeFiberForm P x x).re + lyGlobalRemainder g*‖energyEmbedding P x‖^2 at hd
  have hl := neg_le_of_abs_le ((Complex.abs_re_le_norm (singularInteraction g P x x)).trans hd)
  have hn : 0 ≤ (freeFiberForm P x x).re := by
    rw [freeFiberForm_physical_energy]
    exact freeEnergy_nonneg P _
  rw [fiberFormData_singular_apply,Complex.add_re]
  linarith

theorem fiberHamiltonian_semibounded (g : ℝ) (P : GW.Space) (u : (fiberHamiltonian g P).domain) :
    -(lyGlobalRemainder g)*‖(u : GW.Fock.Carrier)‖^2 ≤
      (⟪(u : GW.Fock.Carrier),fiberHamiltonian g P u⟫_ℂ).re := by
  have h := fiberForm_semibounded g P (fiberFormCoordinate g P u)
  rw [fiberFormCoordinate_embedding] at h
  have he := fiberHamiltonian_form_identity g P u (fiberFormCoordinate g P u)
  rw [fiberFormCoordinate_embedding] at he
  rw [fiberFormData_singular_apply] at h
  exact h.trans_eq (congrArg Complex.re he)

end Froehlich
