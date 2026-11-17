import Froehlich.Nodes.PT01FreeFormKinetic

set_option autoImplicit false

/-! The actual free form represented on a fixed energy graph. Its bounded
operator depends continuously on the momentum in operator norm. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def fixedFreeFormOperator (Q P : GW.Space) : EnergySpace Q →L[ℂ] EnergySpace Q :=
  (∑ a : Fin 3, (fixedEnergyKineticComponent Q a P).adjoint.comp
    (fixedEnergyKineticComponent Q a P)) +
    (energyNumberCoordinates Q).adjoint.comp (energyNumberCoordinates Q) -
    (energyEmbedding Q).adjoint.comp (energyEmbedding Q)

theorem fixedFreeFormOperator_spec (Q P : GW.Space) (w u : EnergySpace Q) :
    ⟪w,fixedFreeFormOperator Q P u⟫_ℂ =
      freeFiberForm P (energyCoordinateChange P Q w) (energyCoordinateChange P Q u) := by
  rw [freeFiberForm_kinetic_number]
  simp_rw [energyKineticComponent_change,energyNumberCoordinates_change,
    energyCoordinateChange_intertwines]
  simp only [fixedFreeFormOperator,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,inner_sub_right,inner_add_right,
    inner_sum,ContinuousLinearMap.adjoint_inner_right,fixedEnergyKineticComponent,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply]

theorem fixedFreeFormOperator_continuous (Q : GW.Space) : Continuous (fixedFreeFormOperator Q) := by
  have hc (a : Fin 3) : Continuous (fun P : GW.Space =>
      (fixedEnergyKineticComponent Q a P).adjoint.comp (fixedEnergyKineticComponent Q a P)) := by
    have hk := fixedEnergyKineticComponent_continuous Q a
    have ha : Continuous (fun P : GW.Space => (fixedEnergyKineticComponent Q a P).adjoint) :=
      ContinuousLinearMap.adjoint.continuous.comp hk
    exact (ContinuousLinearMap.compL ℂ (EnergySpace Q) GW.Fock.Carrier (EnergySpace Q)).continuous₂.comp
      (ha.prodMk hk)
  exact ((continuous_finsetSum Finset.univ (fun a _ => hc a)).add continuous_const).sub continuous_const

end Froehlich
