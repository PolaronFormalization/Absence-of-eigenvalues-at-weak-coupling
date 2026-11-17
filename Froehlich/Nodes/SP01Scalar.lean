import Froehlich.Nodes.SP01Inverse

/-! The vacuum Schur scalar on the entire coercive interval. The fixed
Riesz source and the actual nonvacuum operator specialize SP00 directly. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def nonvacuumSourceCoercivity (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4) :
    SourceCoercivity (nonvacuumBaseOperator g P) (highEnergyEmbedding P 1)
      (Set.Iio (nonvacuumThreshold g)) where
  lower lam := (nonvacuumCoercivity g P lam hg lam.property).lower
  positive lam := (nonvacuumCoercivity g P lam hg lam.property).positive
  bound lam := (nonvacuumCoercivity g P lam hg lam.property).bound

def nonvacuumSourceInverse (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) : HighEnergySpace P 1 →L[ℂ] HighEnergySpace P 1 :=
  sourceInverse (nonvacuumBaseOperator g P) (highEnergyEmbedding P 1) _
    (nonvacuumBaseOperator_selfadjoint g P) (nonvacuumSourceCoercivity g P hg) lam

theorem vacuumSourceSolution_eq_sourceInverse (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) :
    vacuumSourceSolution g P lam hg lam.property =
      nonvacuumSourceInverse g P hg lam (loadRiesz (highFiberSourceLoad g P 1)) := rfl

/-- The real self-energy; reality of the complex quadratic pairing is proved below. -/
def vacuumSelfEnergy (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) : ℝ :=
  sourceScalar (nonvacuumBaseOperator g P) (highEnergyEmbedding P 1) _
    (nonvacuumBaseOperator_selfadjoint g P) (nonvacuumSourceCoercivity g P hg)
    (loadRiesz (highFiberSourceLoad g P 1)) lam

def vacuumSchurFunction (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) : ℝ :=
  ‖P‖^2 - (lam : ℝ) - vacuumSelfEnergy g P hg lam

theorem vacuumSelfEnergy_nonnegative (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) : 0 ≤ vacuumSelfEnergy g P hg lam :=
  sourceInverse_nonnegative (nonvacuumBaseOperator g P) (highEnergyEmbedding P 1) _
    (nonvacuumBaseOperator_selfadjoint g P) (nonvacuumSourceCoercivity g P hg) lam _

theorem vacuumSelfEnergy_continuous (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4) :
    Continuous (vacuumSelfEnergy g P hg) :=
  sourceScalar_continuous (nonvacuumBaseOperator g P) (highEnergyEmbedding P 1) _
    (nonvacuumBaseOperator_selfadjoint g P) (nonvacuumSourceCoercivity g P hg) _

theorem vacuumSelfEnergy_monotone (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4) :
    Monotone (vacuumSelfEnergy g P hg) :=
  sourceInverse_monotone (nonvacuumBaseOperator g P) (highEnergyEmbedding P 1) _
    (nonvacuumBaseOperator_selfadjoint g P) (nonvacuumSourceCoercivity g P hg) _

theorem vacuumSchurFunction_continuous (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4) :
    Continuous (vacuumSchurFunction g P hg) :=
  (continuous_const.sub continuous_subtype_val).sub (vacuumSelfEnergy_continuous g P hg)

theorem vacuumSchurFunction_decrease (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (a b : Set.Iio (nonvacuumThreshold g)) (hab : a < b) :
    vacuumSchurFunction g P hg b ≤ vacuumSchurFunction g P hg a - ((b : ℝ)-(a : ℝ)) := by
  have hm := vacuumSelfEnergy_monotone g P hg hab.le
  dsimp [vacuumSchurFunction]
  linarith

end Froehlich
