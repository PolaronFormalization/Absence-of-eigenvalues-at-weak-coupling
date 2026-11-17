import Froehlich.Nodes.FC04Weighted
import Froehlich.Nodes.FD02FreeForm
import Froehlich.Nodes.FC01Fields

/-! Physical identification of the constructive moving-energy sections.
The input is always the full free operator graph carrier. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

def freeGraphNumberCoordinates (P : GW.Space) : OperatorGraphSpace P →L[ℂ] NumberFormSpace :=
  (energyNumberCoordinates P).comp
    ((energyEmbedding P).adjoint.comp ((freeActionOnGraph P) + graphEmbedding P))

theorem freeGraphNumberCoordinates_embedding (P : GW.Space) (x : OperatorGraphSpace P) :
    numberFormEmbedding (freeGraphNumberCoordinates P x) = graphEmbedding P x := by
  change numberFormEmbedding (energyNumberCoordinates P
    ((energyEmbedding P).adjoint (freeActionOnGraph P x + graphEmbedding P x))) = _
  rw [energyNumberCoordinates_intertwines]
  apply freeFiberOperator_graph_energyLift
  exact (freeFiberOperator_graph_ae_iff P _ _).mpr (freeActionOnGraph_ae P x)

theorem movingEnergySectorField_sections (P : GW.Space) (x : OperatorGraphSpace P) (n : ℕ) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      movingEnergySectorField P x n k =ᵐ[GW.Fock.sectorMeasure n]
        (fun K => movingEnergySection P n
          (physicalSector (n+1) (graphEmbedding P x (n+1))) (k,K)) := by
  have hs := productUnitary_sections volume (GW.Fock.sectorMeasure n)
    (movingEnergySectorField P x n)
  have hc := Measure.ae_ae_of_ae_prod (movingEnergySectorClass_ae P x n)
  have he : GW.Fock.productUnitary volume (GW.Fock.sectorMeasure n)
      (movingEnergySectorField P x n) = movingEnergySectorClass P x n :=
    (GW.Fock.productUnitary volume (GW.Fock.sectorMeasure n)).apply_symm_apply _
  rw [he] at hs
  filter_upwards [hs, hc] with k hk hc
  exact hk.symm.trans hc

/-- The constructed weighted L² slice is precisely the moving graph weight
times the physical canonical annihilation slice, with no representative
evaluation asserted outside the two almost-everywhere quantifiers. -/
theorem movingEnergySectorField_physical (P : GW.Space) (x : OperatorGraphSpace P) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∀ n,
      (fun K => (energyWeight (P-k) n K : ℂ) *
        physicalSector n ((annihilationField (freeGraphNumberCoordinates P x) k) n) K)
        =ᵐ[GW.Fock.sectorMeasure n] movingEnergySectorField P x n k := by
  have hf := annihilationField_representative_common_ae (freeGraphNumberCoordinates P x)
  rw [freeGraphNumberCoordinates_embedding] at hf
  filter_upwards [hf, ae_all_iff.mpr (movingEnergySectorField_sections P x)] with k hk hs
  intro n
  have hphys := kernelRepresentative_physical n ((annihilationField (freeGraphNumberCoordinates P x) k) n)
  have hkn := hk n
  rw [hphys] at hkn
  filter_upwards [hkn, hs n] with K hK hsK
  rw [hK, hsK]
  unfold movingEnergySection
  simp only [smul_eq_mul]
  dsimp only [physicalSector]
  ring

end Froehlich
