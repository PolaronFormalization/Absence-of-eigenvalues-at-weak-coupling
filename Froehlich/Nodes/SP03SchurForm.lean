import Froehlich.Nodes.SP03OneParticleKinetic
import Froehlich.Nodes.SP03Correction

/-! The literal bounded representative of the source one-phonon Schur
form. Its domain is the canonical isolated one-particle energy space. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def onePhononVacuumDenominator (e eps : ℝ) (P : GW.Space) : ℝ := 1+e-‖P‖^2-eps

def onePhononMassOperator (P : GW.Space) : OneParticleEnergySpace P →L[ℂ] OneParticleEnergySpace P :=
  (oneParticleEnergyEmbedding P).adjoint.comp (oneParticleEnergyEmbedding P)

def onePhononSourceLinear (g : ℝ) (P : GW.Space) : OneParticleEnergySpace P →L[ℂ] ℂ :=
  linearizedLoad (isolatedFiberSourceLoad g P)

def onePhononSourceOperator (g : ℝ) (P : GW.Space) :
    OneParticleEnergySpace P →L[ℂ] OneParticleEnergySpace P :=
  (onePhononSourceLinear g P).adjoint.comp (onePhononSourceLinear g P)

theorem onePhononMassOperator_diagonal (P : GW.Space) (f : OneParticleEnergySpace P) :
    (⟪f,onePhononMassOperator P f⟫_ℂ).re = ‖oneParticleEnergyEmbedding P f‖^2 := by
  rw [onePhononMassOperator,ContinuousLinearMap.comp_apply,
    (oneParticleEnergyEmbedding P).adjoint_inner_right]
  simpa only [RCLike.re_eq_complex_re] using
    (norm_sq_eq_re_inner (𝕜 := ℂ) (oneParticleEnergyEmbedding P f)).symm

theorem onePhononSourceOperator_diagonal (g : ℝ) (P : GW.Space) (f : OneParticleEnergySpace P) :
    (⟪f,onePhononSourceOperator g P f⟫_ℂ).re = ‖onePhononSourceLinear g P f‖^2 := by
  rw [onePhononSourceOperator,ContinuousLinearMap.comp_apply,
    (onePhononSourceLinear g P).adjoint_inner_right]
  simpa only [RCLike.re_eq_complex_re] using
    (norm_sq_eq_re_inner (𝕜 := ℂ) (onePhononSourceLinear g P f)).symm

theorem onePhononSourceLinear_apply (g : ℝ) (P : GW.Space) (f : OneParticleEnergySpace P) :
    onePhononSourceLinear g P f = star (isolatedFiberSourceLoad g P f) := rfl

variable (g e eps : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (heLower : -sectorEnergyConstant*|g|^2 ≤ e) (he : e ≤ 0)
    (heps : 0 ≤ eps) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8)

def onePhononSchurOperator (_hdenom : 1/2 ≤ onePhononVacuumDenominator e eps P) :
    OneParticleEnergySpace P →L[ℂ] OneParticleEnergySpace P :=
  1 + ((eps-e-1 : ℝ) : ℂ) • onePhononMassOperator P -
    onePhononHighCorrection g e eps P hg heLower he heps hsmall +
      (((onePhononVacuumDenominator e eps P)⁻¹ : ℝ) : ℂ) • onePhononSourceOperator g P

theorem onePhononSchurOperator_diagonal
    (hdenom : 1/2 ≤ onePhononVacuumDenominator e eps P) (f : OneParticleEnergySpace P) :
    (⟪f,onePhononSchurOperator g e eps P hg heLower he heps hsmall hdenom f⟫_ℂ).re =
      onePhononKineticNorm P f ^ 2 + (eps-e)*‖oneParticleEnergyEmbedding P f‖^2 -
        (⟪f,onePhononHighCorrection g e eps P hg heLower he heps hsmall f⟫_ℂ).re +
          ‖onePhononSourceLinear g P f‖^2/onePhononVacuumDenominator e eps P := by
  have hi : (⟪f,f⟫_ℂ).re = ‖f‖^2 := by
    simpa only [RCLike.re_eq_complex_re] using (norm_sq_eq_re_inner (𝕜 := ℂ) f).symm
  simp only [onePhononSchurOperator,ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply,ContinuousLinearMap.smul_apply,inner_add_right,inner_sub_right,
    inner_smul_right,Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,hi]
  rw [onePhononMassOperator_diagonal,onePhononSourceOperator_diagonal,onePhononKineticNorm_identity]
  simp only [div_eq_mul_inv]
  ring

end Froehlich
