import Froehlich.Nodes.SP01SchurVector

/-! The exact scalar Schur completion evaluated on its form-domain vector. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem vacuumSchurVector_vacuum_row (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) :
    (fiberFormData g P none).form (vacuumEnergyLift P) (vacuumSchurVectorEnergy g P hg lam) -
      (lam : ℂ)*⟪GW.Fock.vacuum,energyEmbedding P (vacuumSchurVectorEnergy g P hg lam)⟫_ℂ =
      (vacuumSchurFunction g P hg lam : ℂ) := by
  have hvh : (fiberFormData g P none).form (vacuumEnergyLift P)
      (vacuumSourceSolution g P lam hg lam.property : EnergySpace P) =
      (vacuumSelfEnergy g P hg lam : ℂ) := by
    rw [(fiberFormData g P none).hermitian,fiberForm_high_vacuum_column,
      vacuumSourceSolution_sourceValue]
    exact Complex.conj_ofReal _
  have hc : ⟪GW.Fock.vacuum,energyEmbedding P (vacuumSchurVectorEnergy g P hg lam)⟫_ℂ = 1 := by
    rw [← inner_conj_symm (𝕜 := ℂ) GW.Fock.vacuum
      (energyEmbedding P (vacuumSchurVectorEnergy g P hg lam)),
      vacuumSchurVector_vacuum_coefficient,map_one]
  rw [hc,vacuumSchurVectorEnergy,map_sub,fiberForm_vacuum_diagonal,hvh,mul_one]
  simp only [vacuumSchurFunction,Complex.ofReal_sub,Complex.ofReal_pow]
  ring

theorem vacuumSchurVector_completion (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) :
    (fiberFormData g P none).form (vacuumSchurVectorEnergy g P hg lam)
      (vacuumSchurVectorEnergy g P hg lam) -
      (lam : ℂ)*⟪energyEmbedding P (vacuumSchurVectorEnergy g P hg lam),
        energyEmbedding P (vacuumSchurVectorEnergy g P hg lam)⟫_ℂ =
      (vacuumSchurFunction g P hg lam : ℂ) := by
  have hv := vacuumSchurVector_vacuum_row g P hg lam
  have hh := vacuumSchurVector_high_row g P hg lam
    (vacuumSourceSolution g P lam hg lam.property)
  have he : energyEmbedding P (vacuumSchurVectorEnergy g P hg lam) =
      GW.Fock.vacuum - energyEmbedding P
        (vacuumSourceSolution g P lam hg lam.property : EnergySpace P) := by
    rw [vacuumSchurVectorEnergy,map_sub,vacuumEnergyLift_embedding]
  have hf : (fiberFormData g P none).form (vacuumSchurVectorEnergy g P hg lam)
      (vacuumSchurVectorEnergy g P hg lam) =
      (fiberFormData g P none).form (vacuumEnergyLift P) (vacuumSchurVectorEnergy g P hg lam) -
      (fiberFormData g P none).form
        (vacuumSourceSolution g P lam hg lam.property : EnergySpace P)
        (vacuumSchurVectorEnergy g P hg lam) := by
    change (fiberFormData g P none).form
      (vacuumEnergyLift P - (vacuumSourceSolution g P lam hg lam.property : EnergySpace P))
      (vacuumSchurVectorEnergy g P hg lam) = _
    rw [map_sub]
    rfl
  have hi : ⟪energyEmbedding P (vacuumSchurVectorEnergy g P hg lam),
      energyEmbedding P (vacuumSchurVectorEnergy g P hg lam)⟫_ℂ =
      ⟪GW.Fock.vacuum,energyEmbedding P (vacuumSchurVectorEnergy g P hg lam)⟫_ℂ -
      ⟪energyEmbedding P (vacuumSourceSolution g P lam hg lam.property : EnergySpace P),
        energyEmbedding P (vacuumSchurVectorEnergy g P hg lam)⟫_ℂ := by
    nth_rw 1 [he]
    exact inner_sub_left _ _ _
  rw [hf,hi]
  rw [← hv]
  linear_combination -hh

end Froehlich
