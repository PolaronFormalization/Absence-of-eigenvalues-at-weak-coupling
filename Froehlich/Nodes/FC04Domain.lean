import Froehlich.Nodes.FC04Assembly

/-! Symmetric reconstruction of the moving weighted slices, using retained
invariance of the actual multiplication graph. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem physicalSector_symmetric (n : ℕ) (u : GW.Fock.Sector n) :
    physicalSector n u ∈ GW.Fock.symmetricSector n := by
  rw [← kernelRepresentative_physical]
  exact (GW.Fock.ordinaryKernelFixed_iff n _).mp (GW.Fock.ordinarySectorKernel n u).property

theorem weightedPhysical_symmetric (Q : GW.Space) (n : ℕ) (u : GW.Fock.Sector n)
    (v : GW.Fock.AmbientSector n)
    (hv : (fun K => (energyWeight Q n K : ℂ) * physicalSector n u K)
      =ᵐ[GW.Fock.sectorMeasure n] v) :
    v ∈ GW.Fock.symmetricSector n := by
  let a : (GW.Analysis.realMultiplier (energyWeight Q n) (GW.Fock.sectorMeasure n)).domain :=
    ⟨physicalSector n u, ⟨v, by simpa only [smul_eq_mul] using hv⟩⟩
  have he : GW.Analysis.realMultiplier (energyWeight Q n) (GW.Fock.sectorMeasure n) a = v := by
    apply Lp.ext
    exact (GW.Analysis.realMultiplier_ae (energyWeight Q n) a).symm.trans
      (by simpa only [smul_eq_mul] using hv)
  rw [← he]
  exact GW.Spaces.invariant_product_mem (energyWeightInvariant Q n) a (physicalSector_symmetric n u)

theorem symmetric_sliceProjection_physical (n : ℕ) (v : GW.Fock.AmbientSector n)
    (hv : v ∈ GW.Fock.symmetricSector n) : physicalSector n (sectorSliceProjection n v) = v := by
  rw [← kernelRepresentative_physical]
  exact kernelRepresentative_sliceProjection n v ((GW.Fock.ordinaryKernelFixed_iff n v).mpr hv)

theorem movingEnergySectorField_symmetric (P : GW.Space) (x : OperatorGraphSpace P) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∀ n,
      movingEnergySectorField P x n k ∈ GW.Fock.symmetricSector n := by
  filter_upwards [movingEnergySectorField_physical P x] with k hk
  intro n
  exact weightedPhysical_symmetric (P-k) n _ _ (hk n)

theorem movingEnergyAmbientField_symmetric (P : GW.Space) (x : OperatorGraphSpace P) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∀ n,
      movingEnergyAmbientField P x k n ∈ GW.Fock.symmetricSector n := by
  have ha := GW.Fock.bochnerReconstruct_ae (volume : Measure GW.Space)
    (fun n => GW.Fock.AmbientSector n) (movingEnergySectorSum P x)
  filter_upwards [ha, movingEnergySectorField_symmetric P x] with k hk hs
  intro n
  have he : movingEnergyAmbientField P x k n = movingEnergySectorField P x n k := hk n
  rw [he]
  exact hs n

end Froehlich
