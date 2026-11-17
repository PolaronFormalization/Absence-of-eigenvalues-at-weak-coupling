import Froehlich.Nodes.OP03
import Froehlich.Nodes.PT03FormVacuumProduct

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem se03_momentumTranslation_zero (f : GW.OnePhonon) : momentumTranslation 0 f = f := by
  apply Lp.ext
  simpa only [add_zero] using momentumTranslation_ae 0 f

theorem se03_energyTranslation_zero (f : OneParticleEnergySpace 0) : energyTranslation 0 f = f := by
  apply (isolatedEnergyCoordinates 0).injective
  rw [energyTranslation_coordinates,se03_momentumTranslation_zero]

theorem se03_energyTranslation_zero_symm (f : OneParticleEnergySpace 0) :
    (energyTranslation 0).symm f = f := by
  apply (energyTranslation 0).injective
  rw [LinearIsometryEquiv.apply_symm_apply,se03_energyTranslation_zero]

theorem se03_sourceLinear_zero (g : ℝ) (f : OneParticleEnergySpace 0) :
    onePhononSourceLinear g 0 f = translatedLinearSource g 0 f := by
  rw [(onePhononSourceLinear_integral g 0 f).2,translatedLinearSource_integral]
  simp only [add_zero]

theorem se03_sourceOperator_zero_pairing (g : ℝ) (f h : OneParticleEnergySpace 0) :
    ⟪f,onePhononSourceOperator g 0 h⟫_ℂ =
      (starRingEnd ℂ) (translatedLinearSource g 0 f)*translatedLinearSource g 0 h := by
  rw [onePhononSourceOperator,ContinuousLinearMap.comp_apply,
    (onePhononSourceLinear g 0).adjoint_inner_right,RCLike.inner_apply',
    se03_sourceLinear_zero,se03_sourceLinear_zero]

end Froehlich
