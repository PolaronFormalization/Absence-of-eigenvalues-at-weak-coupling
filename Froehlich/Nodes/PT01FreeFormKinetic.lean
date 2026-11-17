import Froehlich.Nodes.PT01KineticTransport
import Froehlich.Nodes.FB01KineticIdentityFull
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false

/-! The literal free form decomposed into its momentum and number graph
pairings, on the full energy space. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

private def kineticNumberGram (P : GW.Space) : EnergySpace P →L[ℂ] EnergySpace P :=
  (∑ a : Fin 3, (energyKineticComponent P a).adjoint.comp (energyKineticComponent P a)) +
    (energyNumberCoordinates P).adjoint.comp (energyNumberCoordinates P)

private theorem kineticNumber_norm_identity (P : GW.Space) (x : EnergySpace P) :
    (∑ a : Fin 3, ‖energyKineticComponent P a x‖^2) + ‖energyNumberCoordinates P x‖^2 = ‖x‖^2 := by
  have h := energyKineticNumber_identity P x
  have hn := numberForm_norm_identity (energyNumberCoordinates P x)
  rw [energyNumberCoordinates_intertwines] at hn
  have he := energyEmbedding_norm_identity P x
  linarith

private theorem kineticNumberGram_eq_id (P : GW.Space) :
    kineticNumberGram P = ContinuousLinearMap.id ℂ (EnergySpace P) := by
  have h := (ext_inner_map (kineticNumberGram P).toLinearMap
    (ContinuousLinearMap.id ℂ (EnergySpace P)).toLinearMap).mp (fun x => by
      change ⟪kineticNumberGram P x,x⟫_ℂ = ⟪x,x⟫_ℂ
      simp only [kineticNumberGram,ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.comp_apply,inner_add_left,sum_inner,
        ContinuousLinearMap.adjoint_inner_left,inner_self_eq_norm_sq_to_K]
      exact_mod_cast kineticNumber_norm_identity P x)
  exact DFunLike.ext _ _ (fun x => congrArg (fun f : EnergySpace P →ₗ[ℂ] EnergySpace P => f x) h)

theorem freeFiberForm_kinetic_number (P : GW.Space) (w u : EnergySpace P) :
    freeFiberForm P w u =
      (∑ a : Fin 3, ⟪energyKineticComponent P a w,energyKineticComponent P a u⟫_ℂ) +
        ⟪energyNumberCoordinates P w,energyNumberCoordinates P u⟫_ℂ -
        ⟪energyEmbedding P w,energyEmbedding P u⟫_ℂ := by
  have h : ⟪w,kineticNumberGram P u⟫_ℂ = ⟪w,u⟫_ℂ := by
    rw [kineticNumberGram_eq_id,ContinuousLinearMap.id_apply]
  simp only [kineticNumberGram,ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,inner_add_right,inner_sum,
    ContinuousLinearMap.adjoint_inner_right] at h
  rw [freeFiberForm_apply,← h]

end Froehlich
