import Froehlich.Nodes.SP01Block

/-! FA04 gives a genuine two-sided bounded inverse for every nonzero
vacuum Schur scalar. No spectral conclusion is claimed before form transport. -/
noncomputable section
namespace Froehlich

def vacuumBlockScalarInverse (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) : ℂ →L[ℂ] ℂ :=
  (vacuumSchurFunction g P hg lam : ℂ)⁻¹ • ContinuousLinearMap.id ℂ ℂ

def vacuumBlockInverse (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) :
    (ℂ × HighEnergySpace P 1) →L[ℂ] (ℂ × HighEnergySpace P 1) :=
  schurInverse (vacuumBlockC g P) (vacuumBlockB g P) (nonvacuumSourceInverse g P hg lam)
    (vacuumBlockScalarInverse g P hg lam)

theorem vacuumBlockScalarInverse_left (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) (hF : vacuumSchurFunction g P hg lam ≠ 0) (c : ℂ) :
    vacuumBlockScalarInverse g P hg lam
      (schurComplement (vacuumBlockA P lam) (vacuumBlockC g P) (vacuumBlockB g P)
        (nonvacuumSourceInverse g P hg lam) c) = c := by
  rw [vacuumBlock_schurComplement]
  simp only [vacuumBlockScalarInverse,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,smul_eq_mul]
  rw [← mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hF),one_mul]

theorem vacuumBlockScalarInverse_right (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) (hF : vacuumSchurFunction g P hg lam ≠ 0) (c : ℂ) :
    schurComplement (vacuumBlockA P lam) (vacuumBlockC g P) (vacuumBlockB g P)
      (nonvacuumSourceInverse g P hg lam) (vacuumBlockScalarInverse g P hg lam c) = c := by
  rw [vacuumBlock_schurComplement]
  simp only [vacuumBlockScalarInverse,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,smul_eq_mul]
  rw [← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hF),one_mul]

theorem vacuumBlockInverse_left (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) (hF : vacuumSchurFunction g P hg lam ≠ 0) :
    (vacuumBlockInverse g P hg lam).comp (vacuumBlockOperator g P lam) =
      ContinuousLinearMap.id ℂ (ℂ × HighEnergySpace P 1) :=
  schurInverse_blockOperator (vacuumBlockA P lam) (vacuumBlockC g P) (vacuumBlockB g P)
    (nonvacuumOperator g P lam) (nonvacuumSourceInverse g P hg lam)
    (vacuumBlockScalarInverse g P hg lam)
    (nonvacuumSourceInverse_left_apply g P hg lam) (vacuumBlockScalarInverse_left g P hg lam hF)

theorem vacuumBlockInverse_right (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) (hF : vacuumSchurFunction g P hg lam ≠ 0) :
    (vacuumBlockOperator g P lam).comp (vacuumBlockInverse g P hg lam) =
      ContinuousLinearMap.id ℂ (ℂ × HighEnergySpace P 1) :=
  blockOperator_schurInverse (vacuumBlockA P lam) (vacuumBlockC g P) (vacuumBlockB g P)
    (nonvacuumOperator g P lam) (nonvacuumSourceInverse g P hg lam)
    (vacuumBlockScalarInverse g P hg lam)
    (nonvacuumSourceInverse_right_apply g P hg lam) (vacuumBlockScalarInverse_right g P hg lam hF)

end Froehlich
