import Froehlich.Nodes.FD02WeightedOperations

/-! Native scalar conjugation restricted to the canonical symmetric sectors.
This is the foundation for conjugation on the real weighted domains. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

def ambientConjugation (n : ℕ) (u : GW.Fock.AmbientSector n) : GW.Fock.AmbientSector n :=
  Complex.conjCLE.toContinuousLinearMap.compLp u

theorem ambientConjugation_ae (n : ℕ) (u : GW.Fock.AmbientSector n) :
    ambientConjugation n u =ᵐ[GW.Fock.sectorMeasure n] (fun k => (starRingEnd ℂ) (u k)) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLp u

theorem ambientConjugation_norm (n : ℕ) (u : GW.Fock.AmbientSector n) :
    ‖ambientConjugation n u‖ = ‖u‖ := by
  have hn := (ambientConjugation_ae n u).mono (fun k hk => by
    have h : ‖ambientConjugation n u k‖ = ‖u k‖ := by rw [hk, RCLike.norm_conj]
    exact h)
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hn.mono (fun _ h => h.le)))
    (Lp.norm_le_norm_of_ae_le (hn.mono (fun _ h => h.symm.le)))

theorem ambientConjugation_symmetric (n : ℕ) (u : GW.Fock.AmbientSector n)
    (hu : u ∈ GW.Fock.symmetricSector n) : ambientConjugation n u ∈ GW.Fock.symmetricSector n := by
  apply (GW.Fock.symmetricSector_mem_iff n _).mpr
  intro τ
  have hs := (GW.Fock.symmetricSector_mem_iff n u).mp hu τ
  have ha := ambientConjugation_ae n u
  filter_upwards [ha, (GW.Fock.coordinatePermutation_preserving n τ).quasiMeasurePreserving.ae ha,
    hs] with k hk ht hs
  simp only [GW.Fock.coordinatePermutation_eq] at ht
  rw [ht, hk, hs]

def sectorConjugation (n : ℕ) (u : GW.Fock.Sector n) : GW.Fock.Sector n :=
  sectorSliceProjection n (ambientConjugation n (physicalSector n u))

theorem sectorConjugation_physical (n : ℕ) (u : GW.Fock.Sector n) :
    physicalSector n (sectorConjugation n u) = ambientConjugation n (physicalSector n u) := by
  have hi (v : GW.Fock.Sector n) :
      GW.Fock.kernelFixedInclusion n (GW.Fock.ordinarySectorKernel n v) = physicalSector n v := by
    cases n <;> rfl
  have hu : physicalSector n u ∈ GW.Fock.symmetricSector n := by
    rw [← hi u]
    exact (GW.Fock.ordinaryKernelFixed_iff n _).mp (GW.Fock.ordinarySectorKernel n u).property
  rw [← hi (sectorConjugation n u)]
  exact kernelRepresentative_sliceProjection n _ ((GW.Fock.ordinaryKernelFixed_iff n _).mpr
    (ambientConjugation_symmetric n _ hu))

theorem sectorConjugation_norm (n : ℕ) (u : GW.Fock.Sector n) :
    ‖sectorConjugation n u‖ = ‖u‖ := by
  rw [← (physicalSector n).norm_map (sectorConjugation n u), sectorConjugation_physical,
    ambientConjugation_norm, LinearIsometry.norm_map]

end Froehlich
