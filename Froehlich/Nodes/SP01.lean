import Froehlich.Nodes.SP01Smallness
import Froehlich.Nodes.SP01Spectral

/-! SP01 / lem:vacuumroot: the actual ground energy, its unique vacuum
Schur root, canonical full-domain eigenvector, and full low real spectrum. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem vacuumSchurVector_canonical_embedding (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) :
    energyEmbedding P (vacuumSchurVectorEnergy g P hg lam) = GW.Fock.vacuum -
      energyEmbedding P (vacuumSourceSolution g P lam hg lam.property : EnergySpace P) := by
  rw [vacuumSchurVectorEnergy,map_sub,vacuumEnergyLift_embedding]

theorem vacuumSchurVector_canonical_domain (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) (hroot : vacuumSchurFunction g P hg lam = 0) :
    ∃ hm : energyEmbedding P (vacuumSchurVectorEnergy g P hg lam) ∈ (fiberHamiltonian g P).domain,
      fiberHamiltonian g P ⟨energyEmbedding P (vacuumSchurVectorEnergy g P hg lam),hm⟩ =
        (lam : ℂ) • energyEmbedding P (vacuumSchurVectorEnergy g P hg lam) := by
  apply fiberHamiltonian_domain_of_equation g P (vacuumSchurVectorEnergy g P hg lam)
  intro w
  rw [inner_smul_right]
  exact vacuumSchurVector_weak_equation g P hg lam hroot w

theorem finalSP01 : ∃ s : ℝ, 0 < s ∧ ∀ (g : ℝ), |g| < s → ∀ (P : GW.Space), ‖P‖ ≤ 1/4 →
    ∃ hg : |g| ≤ 1/4, ∃ he : groundEnergy (fiberHamiltonian g P) < nonvacuumThreshold g,
      -1 < groundEnergy (fiberHamiltonian g P) ∧
      groundEnergy (fiberHamiltonian g P) ≤ ‖P‖^2 ∧
      -(sectorEnergyConstant*|g|^2) ≤ groundEnergy (fiberHamiltonian g P) ∧
      vacuumSchurFunction g P hg ⟨groundEnergy (fiberHamiltonian g P),he⟩ = 0 ∧
      (∀ a, vacuumSchurFunction g P hg a = 0 → (a : ℝ) = groundEnergy (fiberHamiltonian g P)) ∧
      realSpectrum (fiberHamiltonian g P) ∩ Set.Iio (nonvacuumThreshold g) =
        {groundEnergy (fiberHamiltonian g P)} ∧
      (∀ w : EnergySpace P, groundEnergy (fiberHamiltonian g P)*‖energyEmbedding P w‖^2 ≤
        ((fiberFormData g P none).form w w).re) ∧
      let lam : Set.Iio (nonvacuumThreshold g) := ⟨groundEnergy (fiberHamiltonian g P),he⟩
      let psi := energyEmbedding P (vacuumSchurVectorEnergy g P hg lam)
      psi = GW.Fock.vacuum - energyEmbedding P
        (vacuumSourceSolution g P lam hg lam.property : EnergySpace P) ∧
      ⟪psi,GW.Fock.vacuum⟫_ℂ = 1 ∧ psi ≠ 0 ∧
      ∃ hm : psi ∈ (fiberHamiltonian g P).domain,
        fiberHamiltonian g P ⟨psi,hm⟩ = (groundEnergy (fiberHamiltonian g P) : ℂ) • psi := by
  obtain ⟨s,hs,hsmall⟩ := vacuumRoot_uniform_smallness
  refine ⟨s,hs,?_⟩
  intro g hg P hP
  obtain ⟨hgc,hL,hquad⟩ := hsmall g hg
  have hminus : -1 < nonvacuumThreshold g := by linarith
  have hPsq : ‖P‖^2 < nonvacuumThreshold g := by nlinarith [norm_nonneg P]
  obtain ⟨e,hel,heu,hroot,hunique⟩ := vacuumSchurFunction_existsUnique_root g P hgc
    hminus hPsq (hquad.trans (by norm_num))
  have hE := vacuumRoot_groundEnergy g P hgc e hroot
  have he : groundEnergy (fiberHamiltonian g P) < nonvacuumThreshold g := by
    rw [hE]
    exact e.property
  let lam : Set.Iio (nonvacuumThreshold g) := ⟨groundEnergy (fiberHamiltonian g P),he⟩
  have heq : lam = e := Subtype.ext hE
  have hr : vacuumSchurFunction g P hgc lam = 0 := by rw [heq]; exact hroot
  refine ⟨hgc,he,?_,?_,?_,hr,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hE] using hel
  · simpa only [hE] using heu
  · simpa only [hE] using vacuumRoot_energy_lower g P hgc e hroot
  · intro a ha
    exact (congrArg Subtype.val (hunique a ha)).trans hE.symm
  · simpa only [hE] using vacuumRoot_spectrum_below g P hgc e hroot
  · exact fiberForm_nonnegative_at_vacuum_root g P hgc lam hr
  · exact vacuumSchurVector_canonical_embedding g P hgc lam
  · exact vacuumSchurVector_vacuum_coefficient g P hgc lam
  · exact vacuumSchurVector_embedding_ne_zero g P hgc lam
  · exact vacuumSchurVector_canonical_domain g P hgc lam hr

end Froehlich
