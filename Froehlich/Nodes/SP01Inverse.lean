import Froehlich.Nodes.FB03TwoSector
import Froehlich.Nodes.SP00
import Froehlich.Nodes.SY01CoerciveTransport

/-! SP01: the actual nonvacuum weak operator and its coercive inverse,
before any ground energy is constructed. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def nonvacuumBaseOperator (g : ℝ) (P : GW.Space) : HighEnergySpace P 1 →L[ℂ] HighEnergySpace P 1 :=
  GW.Operators.formRiesz (compressedFiberFormData g P 1 none) -
    ((compressedFiberFormData g P 1 none).shift : ℂ) •
      ((highEnergyEmbedding P 1).adjoint.comp (highEnergyEmbedding P 1))

def nonvacuumOperator (g : ℝ) (P : GW.Space) (lam : ℝ) : HighEnergySpace P 1 →L[ℂ] HighEnergySpace P 1 :=
  sourceOperator (nonvacuumBaseOperator g P) (highEnergyEmbedding P 1) lam

theorem nonvacuumBaseOperator_selfadjoint (g : ℝ) (P : GW.Space) :
    (nonvacuumBaseOperator g P).adjoint = nonvacuumBaseOperator g P := by
  simp only [nonvacuumBaseOperator,map_sub,map_smulₛₗ,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,Complex.conj_ofReal,(GW.Operators.formRiesz_spec _).2.1]

theorem nonvacuumOperator_selfadjoint (g : ℝ) (P : GW.Space) (lam : ℝ) :
    (nonvacuumOperator g P lam).adjoint = nonvacuumOperator g P lam :=
  sourceOperator_selfadjoint _ _ (nonvacuumBaseOperator_selfadjoint g P) lam

theorem nonvacuumOperator_spec (g : ℝ) (P : GW.Space) (lam : ℝ) (w u : HighEnergySpace P 1) :
    ⟪w,nonvacuumOperator g P lam u⟫_ℂ = (compressedFiberFormData g P 1 none).form w u -
      (lam : ℂ)*⟪highEnergyEmbedding P 1 w,highEnergyEmbedding P 1 u⟫_ℂ := by
  simp only [nonvacuumOperator,sourceOperator,nonvacuumBaseOperator,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,inner_sub_right,inner_smul_right]
  rw [← (GW.Operators.formRiesz_spec (compressedFiberFormData g P 1 none)).1]
  simp only [(highEnergyEmbedding P 1).adjoint_inner_right]
  rw [GW.Operators.energyForm,GW.Operators.shiftedForm_apply]
  have he : (compressedFiberFormData g P 1 none).embedding = highEnergyEmbedding P 1 := rfl
  rw [he]
  ring

def nonvacuumCoercivity (g : ℝ) (P : GW.Space) (lam : ℝ)
    (hg : |g| ≤ 1/4) (hlam : lam < nonvacuumThreshold g) : CompressedCoercivity g lam P 1 none where
  operator := nonvacuumOperator g P lam
  selfadjoint := nonvacuumOperator_selfadjoint g P lam
  lower := min (1-|g|) ((nonvacuumThreshold g-lam)/2)
  positive := nonvacuum_coercivity_positive g lam hg hlam
  representative := nonvacuumOperator_spec g P lam
  bound u := by
    have h := fiberForm_nonvacuum_coercive g lam P u hg hlam
    have hi : (⟪highEnergyEmbedding P 1 u,highEnergyEmbedding P 1 u⟫_ℂ).re =
        ‖highEnergyEmbedding P 1 u‖^2 := by
      simpa only [RCLike.re_eq_complex_re] using
        (norm_sq_eq_re_inner (𝕜 := ℂ) (highEnergyEmbedding P 1 u)).symm
    rw [nonvacuumOperator_spec,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,hi]
    exact h

def vacuumSourceSolution (g : ℝ) (P : GW.Space) (lam : ℝ)
    (hg : |g| ≤ 1/4) (hlam : lam < nonvacuumThreshold g) : HighEnergySpace P 1 :=
  compressedCoerciveSolution (nonvacuumCoercivity g P lam hg hlam) (highFiberSourceLoad g P 1)

theorem vacuumSourceSolution_equation (g : ℝ) (P : GW.Space) (lam : ℝ)
    (hg : |g| ≤ 1/4) (hlam : lam < nonvacuumThreshold g) (w : HighEnergySpace P 1) :
    (compressedFiberFormData g P 1 none).form w (vacuumSourceSolution g P lam hg hlam) -
      (lam : ℂ)*⟪highEnergyEmbedding P 1 w,highEnergyEmbedding P 1 (vacuumSourceSolution g P lam hg hlam)⟫_ℂ =
        highFiberSourceLoad g P 1 w :=
  compressedCoerciveSolution_equation (nonvacuumCoercivity g P lam hg hlam) _ w

end Froehlich
