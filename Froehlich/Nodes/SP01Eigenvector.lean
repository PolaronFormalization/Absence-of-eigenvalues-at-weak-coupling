import Froehlich.Nodes.SP01Completion
import Froehlich.Nodes.SP01VacuumDecomposition
import Froehlich.Nodes.DF01

/-! A zero of the actual scalar Schur function yields a nonzero vector
in the full singular Hamiltonian domain, by the complete weak equation. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem vacuumSchurVector_weak_equation (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) (hroot : vacuumSchurFunction g P hg lam = 0)
    (w : EnergySpace P) :
    (fiberFormData g P none).form w (vacuumSchurVectorEnergy g P hg lam) =
      (lam : ℂ)*⟪energyEmbedding P w,
        energyEmbedding P (vacuumSchurVectorEnergy g P hg lam)⟫_ℂ := by
  have hv := vacuumSchurVector_vacuum_row g P hg lam
  rw [hroot,Complex.ofReal_zero] at hv
  have hv' := sub_eq_zero.mp hv
  have hh := sub_eq_zero.mp (vacuumSchurVector_high_row g P hg lam (highEnergyProject P 1 w))
  have hd := energy_vacuum_high_decomposition P w
  rw [← hd]
  simp only [map_add,map_smulₛₗ,inner_add_left,inner_smul_left,vacuumEnergyLift_embedding]
  change (starRingEnd ℂ) (vacuumCoefficient (energyEmbedding P w)) *
      (fiberFormData g P none).form (vacuumEnergyLift P) (vacuumSchurVectorEnergy g P hg lam) +
      (fiberFormData g P none).form (highEnergyProject P 1 w : EnergySpace P)
        (vacuumSchurVectorEnergy g P hg lam) =
      (lam : ℂ)*((starRingEnd ℂ) (vacuumCoefficient (energyEmbedding P w)) *
        ⟪GW.Fock.vacuum,energyEmbedding P (vacuumSchurVectorEnergy g P hg lam)⟫_ℂ +
        ⟪energyEmbedding P (highEnergyProject P 1 w : EnergySpace P),
          energyEmbedding P (vacuumSchurVectorEnergy g P hg lam)⟫_ℂ)
  rw [hv',hh]
  ring

theorem vacuumSchurVector_eigenvector (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) (hroot : vacuumSchurFunction g P hg lam = 0) :
    HasEigenvector (fiberHamiltonian g P) lam := by
  obtain ⟨hm,he⟩ := fiberHamiltonian_domain_of_equation g P
    (vacuumSchurVectorEnergy g P hg lam)
    ((lam : ℂ) • energyEmbedding P (vacuumSchurVectorEnergy g P hg lam)) (by
      intro w
      rw [inner_smul_right]
      exact vacuumSchurVector_weak_equation g P hg lam hroot w)
  exact ⟨⟨energyEmbedding P (vacuumSchurVectorEnergy g P hg lam),hm⟩,
    vacuumSchurVector_embedding_ne_zero g P hg lam,he⟩

end Froehlich
