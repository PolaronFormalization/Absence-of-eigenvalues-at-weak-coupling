import Froehlich.Nodes.SP01Eigenvector

/-! Schur completion at a scalar root makes the full shifted form
nonnegative, using the actual nonvacuum coercivity. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem fiberForm_nonnegative_at_vacuum_root (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) (hroot : vacuumSchurFunction g P hg lam = 0)
    (w : EnergySpace P) :
    (lam : ℝ)*‖energyEmbedding P w‖^2 ≤ ((fiberFormData g P none).form w w).re := by
  let s := GW.Operators.shiftedForm (fiberFormData g P none).form (energyEmbedding P) (-(lam : ℝ))
  let psi := vacuumSchurVectorEnergy g P hg lam
  have hs : ∀ v u, s v u = star (s u v) :=
    GW.Operators.shiftedForm_hermitian _ _ _ (fiberFormData g P none).hermitian
  have hker : ∀ u, s u psi = 0 := by
    intro u
    rw [GW.Operators.shiftedForm_apply,vacuumSchurVector_weak_equation g P hg lam hroot,
      Complex.ofReal_neg]
    ring
  have hleft : ∀ u, s psi u = 0 := by
    intro u
    simpa only [hker,star_zero] using hs psi u
  let c : ℂ := vacuumCoefficient (energyEmbedding P w)
  let y : HighEnergySpace P 1 := highEnergyProject P 1 w + c • vacuumSourceSolution g P lam hg lam.property
  have hd : c • psi + (y : EnergySpace P) = w := by
    have hw := energy_vacuum_high_decomposition P w
    change c • (vacuumEnergyLift P -
      (vacuumSourceSolution g P lam hg lam.property : EnergySpace P)) +
      ((highEnergyProject P 1 w : EnergySpace P) +
        c • (vacuumSourceSolution g P lam hg lam.property : EnergySpace P)) = w
    change c • vacuumEnergyLift P + (highEnergyProject P 1 w : EnergySpace P) = w at hw
    rw [smul_sub]
    calc
      _ = c • vacuumEnergyLift P + (highEnergyProject P 1 w : EnergySpace P) := by module
      _ = w := hw
  have hshift : s w w = s (y : EnergySpace P) (y : EnergySpace P) := by
    calc
      _ = s (c • psi + (y : EnergySpace P)) (c • psi + (y : EnergySpace P)) := by rw [hd]
      _ = _ := by
        simp only [map_add,map_smulₛₗ,LinearMap.add_apply,LinearMap.smul_apply,
          map_smul,hker,hleft,mul_zero,zero_add,add_zero,smul_zero]
  have hinner (u : EnergySpace P) : (⟪energyEmbedding P u,energyEmbedding P u⟫_ℂ).re =
      ‖energyEmbedding P u‖^2 := by
    simpa only [RCLike.re_eq_complex_re] using
      (norm_sq_eq_re_inner (𝕜 := ℂ) (energyEmbedding P u)).symm
  have hpos : 0 ≤ (s (y : EnergySpace P) (y : EnergySpace P)).re := by
    have hb := fiberForm_nonvacuum_coercive g lam P y hg lam.property
    have hl := nonvacuum_coercivity_positive g lam hg lam.property
    rw [GW.Operators.shiftedForm_apply,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,hinner]
    nlinarith [sq_nonneg ‖y‖]
  rw [← hshift] at hpos
  rw [GW.Operators.shiftedForm_apply,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,hinner] at hpos
  linarith

end Froehlich
