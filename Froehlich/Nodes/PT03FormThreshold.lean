import Froehlich.Nodes.SP03SchurForm
import Froehlich.Nodes.PT03KernelDefinitions
import Froehlich.Nodes.TR01

set_option autoImplicit false

/-! The manuscript's threshold forms are the actual SP03 Schur form and
its retained energy-translation pullback. These are not kernel definitions. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem thresholdForm_denominator (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4) :
    (1/2 : ℝ) ≤ onePhononVacuumDenominator e 0 P := by
  have h := thresholdKernel_denominator_lower e he P hP
  change (1/2 : ℝ) ≤ 1+e-‖P‖^2-0
  linarith

def untranslatedThresholdForm (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)
    (f h : OneParticleEnergySpace P) : ℂ :=
  ⟪f,onePhononSchurOperator g e 0 P hquarter heLower he.2 (by norm_num) hquadratic
    (thresholdForm_denominator e he P hP) h⟫_ℂ

def translatedThresholdForm (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)
    (f h : OneParticleEnergySpace 0) : ℂ :=
  untranslatedThresholdForm e he g hquarter heLower hquadratic P hP
    ((energyTranslation P).symm f) ((energyTranslation P).symm h)

theorem pt03_onePhononMassOperator_pairing (P : GW.Space) (f h : OneParticleEnergySpace P) :
    ⟪f,onePhononMassOperator P h⟫_ℂ =
      ⟪oneParticleEnergyEmbedding P f,oneParticleEnergyEmbedding P h⟫_ℂ := by
  rw [onePhononMassOperator,ContinuousLinearMap.comp_apply,
    (oneParticleEnergyEmbedding P).adjoint_inner_right]

theorem untranslatedThresholdForm_components (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)
    (f h : OneParticleEnergySpace P) :
    untranslatedThresholdForm e he g hquarter heLower hquadratic P hP f h =
      (⟪f,h⟫_ℂ-((1+e : ℝ) : ℂ)*⟪oneParticleEnergyEmbedding P f,oneParticleEnergyEmbedding P h⟫_ℂ) -
      ⟪f,onePhononHighCorrection g e 0 P hquarter heLower he.2 (by norm_num) hquadratic h⟫_ℂ +
      (((1+e-‖P‖^2)⁻¹ : ℝ) : ℂ)*⟪f,onePhononSourceOperator g P h⟫_ℂ := by
  simp only [untranslatedThresholdForm,onePhononSchurOperator,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,ContinuousLinearMap.smul_apply,
    inner_add_right,inner_sub_right,inner_smul_right,pt03_onePhononMassOperator_pairing,
    onePhononVacuumDenominator,sub_zero,zero_sub,Complex.ofReal_sub,Complex.ofReal_neg,
    Complex.ofReal_add,Complex.ofReal_one]
  ring

end Froehlich
