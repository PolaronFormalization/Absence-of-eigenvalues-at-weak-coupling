import Froehlich.Nodes.FC04Linear
import Froehlich.Nodes.GW06Sectors

set_option autoImplicit false

/-! The dependency-ready free-graph part of PT01's energy-valued residual.
This is the actual annihilation field in one fixed high energy space. -/
noncomputable section
open MeasureTheory
namespace Froehlich

theorem annihilationField_mem_high_of_number_high (m : ℕ) (x : NumberFormSpace)
    (hx : numberFormEmbedding x ∈ HighSectorSpace (m+1)) :
    ∀ᵐ k ∂(volume : Measure GW.Space), annihilationField x k ∈ HighSectorSpace m := by
  have hfix : numberFormHighProjection (m+1) x = x := by
    apply numberFormEmbedding_injective
    rw [numberFormEmbedding_highProjection]
    exact (highSector_mem_iff (m+1) _).mp hx
  have h := annihilationField_highProjection_ae m x
  rw [hfix] at h
  filter_upwards [h] with k hk
  exact (highSector_mem_iff m _).mpr hk.symm

variable (P : GW.Space) (m : ℕ) (K : Set GW.Space) (hK : MeasurableSet K)
    (R : ℝ) (hR : 0 ≤ R) (hKR : ∀ k ∈ K, ‖k‖ ≤ R)

def restrictedHighEnergyFieldMap : OperatorGraphSpace P →L[ℂ]
    Lp (HighEnergySpace 0 m) 2 ((volume : Measure GW.Space).restrict K) :=
  ((highEnergyProject 0 m).compLpL 2 ((volume : Measure GW.Space).restrict K)).comp
    (restrictedEnergyFieldMap P K hK R hR hKR)

theorem restrictedHighEnergyFieldMap_physical (x : OperatorGraphSpace P)
    (hx : graphEmbedding P x ∈ HighSectorSpace (m+1)) :
    ∀ᵐ k ∂((volume : Measure GW.Space).restrict K),
      (highEnergyEmbedding 0 m (restrictedHighEnergyFieldMap P m K hK R hR hKR x k) : GW.Fock.Carrier) =
        annihilationField (freeGraphNumberCoordinates P x) k := by
  have hnum : numberFormEmbedding (freeGraphNumberCoordinates P x) ∈ HighSectorSpace (m+1) := by
    rw [freeGraphNumberCoordinates_embedding]
    exact hx
  have hhigh := ae_restrict_of_ae (s := K)
    (annihilationField_mem_high_of_number_high m (freeGraphNumberCoordinates P x) hnum)
  have hmap := (highEnergyProject 0 m).coeFn_compLp (restrictedEnergyFieldMap P K hK R hR hKR x)
  filter_upwards [hmap,restrictedEnergyFieldMap_physical P K hK R hR hKR x,hhigh] with k hk hp hh
  change (highEnergyEmbedding 0 m
    ((highEnergyProject 0 m).compLp (restrictedEnergyFieldMap P K hK R hR hKR x) k) : GW.Fock.Carrier) = _
  rw [hk]
  change energyEmbedding 0 (energyHighProjection 0 m
    (restrictedEnergyFieldMap P K hK R hR hKR x k)) = _
  rw [energyHighProjection_intertwines,hp]
  exact (highSector_mem_iff m _).mp hh

end Froehlich
