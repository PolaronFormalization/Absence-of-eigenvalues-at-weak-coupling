import Froehlich.Nodes.SP01Scalar

/-! Source evaluation and elementary scalar consequences for the actual
vacuum Schur function. No vacuum operator-domain assertion is used. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem vacuumSourceSolution_sourceValue (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) :
    highFiberSourceLoad g P 1 (vacuumSourceSolution g P lam hg lam.property) =
      (vacuumSelfEnergy g P hg lam : ℂ) := by
  rw [loadRiesz_spec, vacuumSourceSolution_eq_sourceInverse]
  have hr := sourceInverse_real (nonvacuumBaseOperator g P) (highEnergyEmbedding P 1) _
    (nonvacuumBaseOperator_selfadjoint g P) (nonvacuumSourceCoercivity g P hg) lam
    (loadRiesz (highFiberSourceLoad g P 1))
  have he := inner_conj_symm (𝕜 := ℂ) (loadRiesz (highFiberSourceLoad g P 1))
    (nonvacuumSourceInverse g P hg lam (loadRiesz (highFiberSourceLoad g P 1)))
  apply Complex.ext
  · simpa only [Complex.conj_re,Complex.ofReal_re,vacuumSelfEnergy,sourceScalar,nonvacuumSourceInverse] using congrArg Complex.re he
  · have hi := congrArg Complex.im he.symm
    simp only [Complex.conj_im] at hi
    change (⟪loadRiesz (highFiberSourceLoad g P 1),
      nonvacuumSourceInverse g P hg lam (loadRiesz (highFiberSourceLoad g P 1))⟫_ℂ).im = 0 at hr
    rw [hr] at hi
    simp only [Complex.ofReal_im]
    linarith

theorem vacuumSchurFunction_upperEndpoint (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (hP : ‖P‖^2 < nonvacuumThreshold g) :
    vacuumSchurFunction g P hg ⟨‖P‖^2,hP⟩ ≤ 0 := by
  have h := vacuumSelfEnergy_nonnegative g P hg ⟨‖P‖^2,hP⟩
  dsimp [vacuumSchurFunction]
  linarith

theorem vacuumSchurFunction_strictAnti (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4) :
    StrictAnti (vacuumSchurFunction g P hg) := by
  intro a b hab
  have h := vacuumSchurFunction_decrease g P hg a b hab
  have hab' : (a : ℝ) < (b : ℝ) := hab
  linarith

theorem vacuumSchurFunction_root_unique (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (a b : Set.Iio (nonvacuumThreshold g))
    (ha : vacuumSchurFunction g P hg a = 0) (hb : vacuumSchurFunction g P hg b = 0) : a = b :=
  (vacuumSchurFunction_strictAnti g P hg).injective (ha.trans hb.symm)

end Froehlich
