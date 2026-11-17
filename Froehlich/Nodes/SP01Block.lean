import Froehlich.Nodes.SP01EnergySplit
import Froehlich.Nodes.SP01ScalarIdentities

/-! The literal scalar/nonvacuum bounded blocks and their exact scalar
Schur complement. The maps act on the usual product norm used by FA04. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def vacuumBlockA (P : GW.Space) (lam : ℝ) : ℂ →L[ℂ] ℂ :=
  ((‖P‖^2-lam : ℝ) : ℂ) • ContinuousLinearMap.id ℂ ℂ

def vacuumBlockB (g : ℝ) (P : GW.Space) : ℂ →L[ℂ] HighEnergySpace P 1 :=
  ContinuousLinearMap.toSpanSingleton ℂ (loadRiesz (highFiberSourceLoad g P 1))

def vacuumBlockC (g : ℝ) (P : GW.Space) : HighEnergySpace P 1 →L[ℂ] ℂ :=
  innerSL ℂ (loadRiesz (highFiberSourceLoad g P 1))

def vacuumBlockOperator (g : ℝ) (P : GW.Space) (lam : ℝ) :
    (ℂ × HighEnergySpace P 1) →L[ℂ] (ℂ × HighEnergySpace P 1) :=
  blockOperator (vacuumBlockA P lam) (vacuumBlockC g P) (vacuumBlockB g P)
    (nonvacuumOperator g P lam)

theorem vacuumSourceInverse_quadratic (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) :
    ⟪loadRiesz (highFiberSourceLoad g P 1),
      nonvacuumSourceInverse g P hg lam (loadRiesz (highFiberSourceLoad g P 1))⟫_ℂ =
      (vacuumSelfEnergy g P hg lam : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im,nonvacuumSourceInverse] using
      sourceInverse_real (nonvacuumBaseOperator g P) (highEnergyEmbedding P 1) _
        (nonvacuumBaseOperator_selfadjoint g P) (nonvacuumSourceCoercivity g P hg) lam
        (loadRiesz (highFiberSourceLoad g P 1))

theorem vacuumBlock_schurComplement (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) (c : ℂ) :
    schurComplement (vacuumBlockA P lam) (vacuumBlockC g P) (vacuumBlockB g P)
      (nonvacuumSourceInverse g P hg lam) c = (vacuumSchurFunction g P hg lam : ℂ)*c := by
  rw [schurComplement_apply]
  simp only [vacuumBlockA,vacuumBlockB,vacuumBlockC,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.toSpanSingleton_apply,map_smul,
    innerSL_apply_apply,inner_smul_right,smul_eq_mul]
  rw [vacuumSourceInverse_quadratic]
  simp only [vacuumSchurFunction,Complex.ofReal_sub,Complex.ofReal_pow]
  ring

theorem nonvacuumSourceInverse_left_apply (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) (u : HighEnergySpace P 1) :
    nonvacuumSourceInverse g P hg lam (nonvacuumOperator g P lam u) = u := by
  exact congrArg (fun T : HighEnergySpace P 1 →L[ℂ] HighEnergySpace P 1 => T u)
    (sourceInverse_left (nonvacuumBaseOperator g P) (highEnergyEmbedding P 1) _
      (nonvacuumBaseOperator_selfadjoint g P) (nonvacuumSourceCoercivity g P hg) lam)

theorem nonvacuumSourceInverse_right_apply (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) (u : HighEnergySpace P 1) :
    nonvacuumOperator g P lam (nonvacuumSourceInverse g P hg lam u) = u := by
  exact congrArg (fun T : HighEnergySpace P 1 →L[ℂ] HighEnergySpace P 1 => T u)
    (sourceInverse_right (nonvacuumBaseOperator g P) (highEnergyEmbedding P 1) _
      (nonvacuumBaseOperator_selfadjoint g P) (nonvacuumSourceCoercivity g P hg) lam)

end Froehlich
