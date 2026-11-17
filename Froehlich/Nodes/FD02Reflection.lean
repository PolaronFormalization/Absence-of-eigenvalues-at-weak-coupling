import Froehlich.Nodes.FD02WeightedSymmetries
import Froehlich.Nodes.AN00

/-! Actual momentum reflection on the retained configuration measures and
symmetric sectors, including the scalar vacuum. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

def configurationNegation (n : ℕ) : GW.Fock.Coordinates n ≃ᵐ GW.Fock.Coordinates n where
  toFun k i := -k i
  invFun k i := -k i
  left_inv k := by funext i; exact neg_neg _
  right_inv k := by funext i; exact neg_neg _
  measurable_toFun := Measurable.of_eval (fun i => (measurable_pi_apply i).neg)
  measurable_invFun := Measurable.of_eval (fun i => (measurable_pi_apply i).neg)

theorem configurationNegation_preserving (n : ℕ) :
    MeasurePreserving (configurationNegation n) (GW.Fock.sectorMeasure n) (GW.Fock.sectorMeasure n) :=
  measurePreserving_pi (fun _ : Fin n => (volume : Measure GW.Space))
    (fun _ : Fin n => (volume : Measure GW.Space)) (fun _ => space_negation_preserving)

def ambientReflection (n : ℕ) : GW.Fock.AmbientSector n ≃ₗᵢ[ℂ] GW.Fock.AmbientSector n :=
  GW.Fock.pullbackUnitary (configurationNegation n) (configurationNegation_preserving n)

theorem ambientReflection_ae (n : ℕ) (u : GW.Fock.AmbientSector n) :
    ambientReflection n u =ᵐ[GW.Fock.sectorMeasure n] (fun k => u (fun i => -k i)) :=
  GW.Fock.pullbackUnitary_ae (configurationNegation n) (configurationNegation_preserving n) u

theorem ambientReflection_involutive (n : ℕ) : Function.Involutive (ambientReflection n) := by
  intro u
  apply Lp.ext
  filter_upwards [ambientReflection_ae n (ambientReflection n u),
    (configurationNegation_preserving n).quasiMeasurePreserving.ae (ambientReflection_ae n u)] with k hk hu
  rw [hk]
  change ambientReflection n u (fun i => -k i) = u (fun i => -(-k i)) at hu
  simpa only [neg_neg] using hu

theorem ambientReflection_symmetric (n : ℕ) (u : GW.Fock.AmbientSector n)
    (hu : u ∈ GW.Fock.symmetricSector n) : ambientReflection n u ∈ GW.Fock.symmetricSector n := by
  apply (GW.Fock.symmetricSector_mem_iff n _).mpr
  intro τ
  have hs := (configurationNegation_preserving n).quasiMeasurePreserving.ae
    ((GW.Fock.symmetricSector_mem_iff n u).mp hu τ)
  have ha := ambientReflection_ae n u
  filter_upwards [ha, (GW.Fock.coordinatePermutation_preserving n τ).quasiMeasurePreserving.ae ha,
    hs] with k hk ht hs
  simp only [GW.Fock.coordinatePermutation_eq] at ht
  rw [ht, hk]
  exact hs

def sectorReflection (n : ℕ) : GW.Fock.Sector n →L[ℂ] GW.Fock.Sector n :=
  (sectorSliceProjection n).comp ((ambientReflection n).toLinearIsometry.toContinuousLinearMap.comp
    (physicalSector n).toContinuousLinearMap)

theorem sectorReflection_physical (n : ℕ) (u : GW.Fock.Sector n) :
    physicalSector n (sectorReflection n u) = ambientReflection n (physicalSector n u) := by
  have hi (v : GW.Fock.Sector n) :
      GW.Fock.kernelFixedInclusion n (GW.Fock.ordinarySectorKernel n v) = physicalSector n v := by
    cases n <;> rfl
  have hu : physicalSector n u ∈ GW.Fock.symmetricSector n := by
    rw [← hi u]
    exact (GW.Fock.ordinaryKernelFixed_iff n _).mp (GW.Fock.ordinarySectorKernel n u).property
  rw [← hi (sectorReflection n u)]
  exact kernelRepresentative_sliceProjection n _ ((GW.Fock.ordinaryKernelFixed_iff n _).mpr
    (ambientReflection_symmetric n _ hu))

theorem sectorReflection_norm (n : ℕ) (u : GW.Fock.Sector n) :
    ‖sectorReflection n u‖ = ‖u‖ := by
  rw [← (physicalSector n).norm_map (sectorReflection n u), sectorReflection_physical,
    LinearIsometryEquiv.norm_map, LinearIsometry.norm_map]

theorem sectorReflection_involutive (n : ℕ) : Function.Involutive (sectorReflection n) := by
  intro u
  apply (physicalSector n).injective
  rw [sectorReflection_physical, sectorReflection_physical, ambientReflection_involutive]

end Froehlich
