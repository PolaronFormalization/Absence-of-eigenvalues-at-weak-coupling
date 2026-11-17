import Froehlich.Nodes.SP01VacuumScalar

/-! The actual vacuum Schur vector in the form domain: its nonvacuum
weak row vanishes, and its vacuum coefficient is one. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def vacuumSchurVectorEnergy (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) : EnergySpace P :=
  vacuumEnergyLift P - (vacuumSourceSolution g P lam hg lam.property : EnergySpace P)

theorem vacuumSchurVector_high_row (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) (w : HighEnergySpace P 1) :
    (fiberFormData g P none).form (w : EnergySpace P) (vacuumSchurVectorEnergy g P hg lam) -
      (lam : ℂ)*⟪energyEmbedding P (w : EnergySpace P),
        energyEmbedding P (vacuumSchurVectorEnergy g P hg lam)⟫_ℂ = 0 := by
  have hw := vacuumSourceSolution_equation g P lam hg lam.property w
  have hi : ⟪highEnergyEmbedding P 1 w,
      highEnergyEmbedding P 1 (vacuumSourceSolution g P lam hg lam.property)⟫_ℂ =
      ⟪energyEmbedding P (w : EnergySpace P),
        energyEmbedding P (vacuumSourceSolution g P lam hg lam.property : EnergySpace P)⟫_ℂ := by
    change ⟪(highEnergyEmbedding P 1 w : GW.Fock.Carrier),
      (highEnergyEmbedding P 1 (vacuumSourceSolution g P lam hg lam.property) : GW.Fock.Carrier)⟫_ℂ = _
    rw [highEnergyEmbedding_apply,highEnergyEmbedding_apply]
  rw [hi] at hw
  change (fiberFormData g P none).form (w : EnergySpace P)
      (vacuumSourceSolution g P lam hg lam.property : EnergySpace P) -
    (lam : ℂ)*⟪energyEmbedding P (w : EnergySpace P),
      energyEmbedding P (vacuumSourceSolution g P lam hg lam.property : EnergySpace P)⟫_ℂ =
    highFiberSourceLoad g P 1 w at hw
  simp only [vacuumSchurVectorEnergy,map_sub,inner_sub_right,
    vacuumEnergyLift_embedding,fiberForm_high_vacuum_column,highEnergyEmbedding_vacuum_orthogonal]
  rw [← hw]
  ring

theorem vacuumSchurVector_vacuum_coefficient (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) :
    ⟪energyEmbedding P (vacuumSchurVectorEnergy g P hg lam),GW.Fock.vacuum⟫_ℂ = 1 := by
  rw [vacuumSchurVectorEnergy,map_sub,inner_sub_left,vacuumEnergyLift_embedding,
    vacuum_inner_self,highEnergyEmbedding_vacuum_orthogonal,sub_zero]

theorem vacuumSchurVector_embedding_ne_zero (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) :
    energyEmbedding P (vacuumSchurVectorEnergy g P hg lam) ≠ 0 := by
  intro hz
  have h := vacuumSchurVector_vacuum_coefficient g P hg lam
  rw [hz,inner_zero_left] at h
  exact zero_ne_one h

end Froehlich
