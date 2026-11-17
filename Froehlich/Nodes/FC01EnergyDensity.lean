import Froehlich.Nodes.FC01GraphDensity

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology
namespace Froehlich

theorem energyCore_dense (P : GW.Space) :
    Dense {x : EnergySpace P | energyEmbedding P x ∈ boundedMomentumCore} := by
  let j : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
    (energyEmbedding P).comp (energyCoordinates P).symm.toLinearIsometry.toContinuousLinearMap
  have hj : ∀ x n, (fun k => (energyWeight P n k : ℂ) * physicalSector n (j x n) k)
      =ᵐ[GW.Fock.sectorMeasure n] physicalSector n (x n) := by
    intro x n
    simpa only [j, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      LinearIsometryEquiv.apply_symm_apply, smul_eq_mul] using
      energyEmbedding_weighted_ae P ((energyCoordinates P).symm x) n
  have hd := weightedEmbedding_core_dense j (energyWeight P)
    (fun n k => zero_lt_one.trans_le (energyWeight_ge_one P n k)) hj
  have hp := hd.preimage (energyCoordinates P).toHomeomorph.isOpenMap
  simpa only [LinearIsometryEquiv.coe_toHomeomorph, Set.preimage_setOf_eq, j, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.symm_apply_apply] using hp

theorem freeOperatorCore_dense (P : GW.Space) :
    Dense {x : OperatorGraphSpace P | graphEmbedding P x ∈ boundedMomentumCore} := by
  let j : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
    (graphEmbedding P).comp (graphCoordinates P).symm.toLinearIsometry.toContinuousLinearMap
  have hj : ∀ x n, (fun k => (operatorGraphWeight P n k : ℂ) * physicalSector n (j x n) k)
      =ᵐ[GW.Fock.sectorMeasure n] physicalSector n (x n) := by
    intro x n
    simpa only [j, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      LinearIsometryEquiv.apply_symm_apply, smul_eq_mul] using
      graphEmbedding_weighted_ae P ((graphCoordinates P).symm x) n
  have hd := weightedEmbedding_core_dense j (operatorGraphWeight P)
    (fun n k => zero_lt_one.trans_le (operatorGraphWeight_ge_one P n k)) hj
  have hp := hd.preimage (graphCoordinates P).toHomeomorph.isOpenMap
  simpa only [LinearIsometryEquiv.coe_toHomeomorph, Set.preimage_setOf_eq, j, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.symm_apply_apply] using hp

end Froehlich
