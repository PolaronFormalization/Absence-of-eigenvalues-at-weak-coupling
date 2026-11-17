import Froehlich.Nodes.GW01
import Froehlich.Nodes.GW02Sections

/-! GW02: the prescribed currying direction and symmetric-sector restriction.
All product maps below are the retained GW maps, used in their actual direction. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal

namespace Froehlich

/-- First split off momentum zero, then apply the inverse GW product unitary. -/
def ambientCurrying (n : ℕ) : GW.Fock.AmbientSector (n+1) ≃ₗᵢ[ℂ]
    Lp (GW.Fock.AmbientSector n) 2 (volume : Measure GW.Space) :=
  (GW.Fock.splitUnitary n 0).trans
    (GW.Fock.productUnitary (E := ℂ) volume (GW.Fock.sectorMeasure n)).symm

/-- The unprojected curried field is already an isometry on the actual input sector. -/
def rawSectorCurrying (n : ℕ) : GW.Fock.Sector (n+1) →ₗᵢ[ℂ]
    Lp (GW.Fock.AmbientSector n) 2 (volume : Measure GW.Space) :=
  (ambientCurrying n).toLinearIsometry.comp (GW.Fock.sectorInclusion n)

theorem ambientCurrying_product (n : ℕ) (u : GW.Fock.AmbientSector (n+1)) :
    GW.Fock.productUnitary volume (GW.Fock.sectorMeasure n) (ambientCurrying n u) =
      GW.Fock.splitUnitary n 0 u :=
  (GW.Fock.productUnitary (E := ℂ) volume (GW.Fock.sectorMeasure n)).apply_symm_apply _

/-- An instantiated application confirming the inverse-product direction on rectangles. -/
theorem inverseProduct_rectangle (n : ℕ) (A : Set GW.Space)
    (B : Set (GW.Fock.Coordinates n)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAf : (volume : Measure GW.Space) A ≠ ∞) (hBf : GW.Fock.sectorMeasure n B ≠ ∞)
    (z : ℂ) :
    (GW.Fock.productUnitary (E := ℂ) volume (GW.Fock.sectorMeasure n)).symm
      (indicatorConstLp 2 (hA.prod hB)
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hAf hBf) z) =
      indicatorConstLp 2 hA hAf (indicatorConstLp 2 hB hBf z) := by
  apply (GW.Fock.productUnitary (E := ℂ) volume (GW.Fock.sectorMeasure n)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (GW.Fock.productUnitary_rectangle volume (GW.Fock.sectorMeasure n)
    A B hA hB hAf hBf z).symm

/-- The pointwise projection followed by the prescribed inverse sector identification.
At `n = 0` the latter is the scalar-vacuum inverse. -/
def sectorSliceProjection (n : ℕ) : GW.Fock.AmbientSector n →L[ℂ] GW.Fock.Sector n :=
  (GW.Fock.ordinarySectorKernel n).symm.toLinearIsometry.toContinuousLinearMap.comp
    (GW.Fock.kernelFixedProjection (E := ℂ) n)

theorem sectorSliceProjection_norm_le (n : ℕ) (u : GW.Fock.AmbientSector n) :
    ‖sectorSliceProjection n u‖ ≤ ‖u‖ := by
  change ‖(GW.Fock.ordinarySectorKernel n).symm (GW.Fock.kernelFixedProjection n u)‖ ≤ ‖u‖
  rw [LinearIsometryEquiv.norm_map]
  exact GW.Fock.kernelSymmetrizer_norm_le n u

theorem sectorSliceProjection_opNorm (n : ℕ) : ‖sectorSliceProjection n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using sectorSliceProjection_norm_le n u

theorem sectorSliceProjection_inclusion (n : ℕ) (u : GW.Fock.Sector n) :
    sectorSliceProjection n
      (GW.Fock.kernelFixedInclusion n (GW.Fock.ordinarySectorKernel n u)) = u := by
  change (GW.Fock.ordinarySectorKernel n).symm
    (GW.Fock.kernelFixedProjection n
      (GW.Fock.kernelFixedInclusion n (GW.Fock.ordinarySectorKernel n u))) = u
  have he : GW.Fock.kernelFixedProjection n
      (GW.Fock.kernelFixedInclusion n (GW.Fock.ordinarySectorKernel n u)) =
      GW.Fock.ordinarySectorKernel n u := by
    apply Subtype.ext
    exact GW.Fock.kernelSymmetrizer_of_fixed n _ (GW.Fock.ordinarySectorKernel n u).property
  rw [he, LinearIsometryEquiv.symm_apply_apply]

/-- The exact GW02 composition on canonical sectors. -/
def sectorCurrying (n : ℕ) : GW.Fock.Sector (n+1) →L[ℂ]
    Lp (GW.Fock.Sector n) 2 (volume : Measure GW.Space) :=
  (GW.Fock.amplify volume (sectorSliceProjection n)).comp
    (rawSectorCurrying n).toContinuousLinearMap

theorem sectorCurrying_ae (n : ℕ) (u : GW.Fock.Sector (n+1)) :
    sectorCurrying n u =ᵐ[volume]
      (fun k => sectorSliceProjection n (rawSectorCurrying n u k)) :=
  GW.Fock.amplify_ae volume (sectorSliceProjection n) (rawSectorCurrying n u)

theorem sectorCurrying_norm_le (n : ℕ) (u : GW.Fock.Sector (n+1)) :
    ‖sectorCurrying n u‖ ≤ ‖u‖ := by
  calc
    _ ≤ ‖GW.Fock.amplify volume (sectorSliceProjection n)‖ * ‖rawSectorCurrying n u‖ :=
      (GW.Fock.amplify volume (sectorSliceProjection n)).le_opNorm _
    _ ≤ 1 * ‖rawSectorCurrying n u‖ :=
      mul_le_mul_of_nonneg_right
        ((GW.Fock.amplify_norm_le volume (sectorSliceProjection n)).trans
          (sectorSliceProjection_opNorm n)) (norm_nonneg _)
    _ = ‖u‖ := by rw [one_mul, LinearIsometry.norm_map]

/-- The distinguished coordinate is fixed while the remaining coordinates are permuted. -/
theorem splitCoordinates_spectator (n : ℕ) (τ : Equiv.Perm (Fin n))
    (p : GW.Space × GW.Fock.Coordinates n) :
    GW.Fock.coordinatePermutation (n+1) (GW.Fock.extendSpectator n τ)
      ((GW.Fock.splitCoordinates n 0).symm p) =
      (GW.Fock.splitCoordinates n 0).symm
        (p.1, GW.Fock.coordinatePermutation n τ p.2) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have hz := (GW.Fock.extendSpectator n τ).property
    change (GW.Fock.extendSpectator n τ : Equiv.Perm (Fin (n+1))) 0 = 0 at hz
    simp only [GW.Fock.coordinatePermutation_apply, hz]
    exact (GW.Fock.insertCoordinate_same n 0 p.1 p.2).trans
      (GW.Fock.insertCoordinate_same n 0 p.1
        (GW.Fock.coordinatePermutation n τ p.2)).symm
  · simp only [GW.Fock.coordinatePermutation_apply, GW.Fock.extendSpectator_succ]
    calc
      _ = p.2 (τ j) := by
        simpa only [Fin.zero_succAbove] using GW.Fock.insertCoordinate_succAbove n 0 p.1 p.2 (τ j)
      _ = GW.Fock.coordinatePermutation n τ p.2 j :=
        (GW.Fock.coordinatePermutation_apply n τ p.2 j).symm
      _ = _ := by
        simpa only [Fin.zero_succAbove] using
          (GW.Fock.insertCoordinate_succAbove n 0 p.1
            (GW.Fock.coordinatePermutation n τ p.2) j).symm

theorem splitSector_spectator_fixed (n : ℕ) (u : GW.Fock.Sector (n+1))
    (τ : Equiv.Perm (Fin n)) :
    GW.Fock.productPermutation volume n τ
      (GW.Fock.splitUnitary n 0 (GW.Fock.sectorInclusion n u)) =
      GW.Fock.splitUnitary n 0 (GW.Fock.sectorInclusion n u) := by
  let v := GW.Fock.splitUnitary n 0 (GW.Fock.sectorInclusion n u)
  let ρ : GW.Space × GW.Fock.Coordinates n → GW.Space × GW.Fock.Coordinates n :=
    fun p => (p.1, GW.Fock.coordinatePermutation n τ p.2)
  have hρ : MeasurePreserving ρ
      ((volume : Measure GW.Space).prod (GW.Fock.sectorMeasure n))
      ((volume : Measure GW.Space).prod (GW.Fock.sectorMeasure n)) :=
    (MeasurePreserving.id volume).prod (GW.Fock.coordinatePermutation_preserving n τ)
  have hs := GW.Fock.splitUnitary_ae n 0 (GW.Fock.sectorInclusion n u)
  have hu := (GW.Fock.permutation_fixed_iff (n+1)
    (GW.Fock.extendSpectator n τ) (GW.Fock.sectorInclusion n u)).mp
      (u.property (GW.Fock.extendSpectator n τ))
  apply Lp.ext
  filter_upwards [GW.Fock.productPermutation_ae volume n τ v, hs,
    hρ.quasiMeasurePreserving.ae hs,
    (GW.Fock.splitCoordinates_inverse_preserving n 0).quasiMeasurePreserving.ae hu]
    with p hp hs₀ hs₁ hu₀
  change _ = v p
  rw [hp]
  have hr : v (ρ p) = v p := by
    rw [hs₁]
    change GW.Fock.sectorInclusion n u ((GW.Fock.splitCoordinates n 0).symm
      (p.1, GW.Fock.coordinatePermutation n τ p.2)) = v p
    rw [← splitCoordinates_spectator n τ p]
    exact hu₀.trans hs₀.symm
  simpa only [ρ, GW.Fock.coordinatePermutation_eq] using hr

/-- The actual unprojected slices lie in the closed symmetric subspace a.e. -/
theorem rawSectorCurrying_symmetric_ae (n : ℕ) (u : GW.Fock.Sector (n+1)) :
    ∀ᵐ k ∂(volume : Measure GW.Space), rawSectorCurrying n u k ∈ GW.Fock.symmetricSector n := by
  obtain ⟨w, hw⟩ := (GW.Fock.symmetricProduct_range volume n
    (GW.Fock.splitUnitary n 0 (GW.Fock.sectorInclusion n u))).mpr
      (splitSector_spectator_fixed n u)
  have hr : GW.Fock.amplify volume (GW.Fock.symmetricInclusion n).toContinuousLinearMap w =
      rawSectorCurrying n u := by
    apply (GW.Fock.productUnitary (E := ℂ) volume (GW.Fock.sectorMeasure n)).injective
    exact hw.trans (ambientCurrying_product n (GW.Fock.sectorInclusion n u)).symm
  rw [← hr]
  filter_upwards [GW.Fock.amplify_ae volume
    (GW.Fock.symmetricInclusion n).toContinuousLinearMap w] with k hk
  rw [hk]
  exact (w k).property

theorem sectorCurrying_norm (n : ℕ) (u : GW.Fock.Sector (n+1)) :
    ‖sectorCurrying n u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← (rawSectorCurrying n).norm_map u]
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ), GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  apply integral_congr_ae
  filter_upwards [sectorCurrying_ae n u, rawSectorCurrying_symmetric_ae n u] with k hk hs
  rw [hk]
  change ‖(GW.Fock.ordinarySectorKernel n).symm
    (GW.Fock.kernelFixedProjection n (rawSectorCurrying n u k))‖ ^ 2 = _
  rw [LinearIsometryEquiv.norm_map]
  change ‖GW.Fock.kernelSymmetrizer n (rawSectorCurrying n u k)‖ ^ 2 = _
  rw [GW.Fock.kernelSymmetrizer_of_fixed n _ ((GW.Fock.ordinaryKernelFixed_iff n _).mpr hs)]

def sectorCurryingIsometry (n : ℕ) : GW.Fock.Sector (n+1) →ₗᵢ[ℂ]
    Lp (GW.Fock.Sector n) 2 (volume : Measure GW.Space) where
  toLinearMap := (sectorCurrying n).toLinearMap
  norm_map' := sectorCurrying_norm n

theorem kernelRepresentative_zero (z : ℂ) :
    GW.Fock.kernelFixedInclusion 0 (GW.Fock.ordinarySectorKernel 0 z) =
      GW.Fock.vacuumAdapter z := rfl

theorem kernelRepresentative_succ (n : ℕ) (u : GW.Fock.Sector (n+1)) :
    GW.Fock.kernelFixedInclusion (n+1) (GW.Fock.ordinarySectorKernel (n+1) u) =
      GW.Fock.sectorInclusion n u := rfl

theorem kernelRepresentative_sliceProjection (n : ℕ) (v : GW.Fock.AmbientSector n)
    (hv : v ∈ GW.Fock.kernelFixed (E := ℂ) n) :
    GW.Fock.kernelFixedInclusion n (GW.Fock.ordinarySectorKernel n (sectorSliceProjection n v)) = v := by
  change GW.Fock.kernelFixedInclusion n (GW.Fock.ordinarySectorKernel n
    ((GW.Fock.ordinarySectorKernel n).symm (GW.Fock.kernelFixedProjection n v))) = v
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact GW.Fock.kernelSymmetrizer_of_fixed n v hv

theorem sectorCurrying_kernelRepresentative_ae (n : ℕ) (u : GW.Fock.Sector (n+1)) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      GW.Fock.kernelFixedInclusion n (GW.Fock.ordinarySectorKernel n (sectorCurrying n u k)) =
        rawSectorCurrying n u k := by
  filter_upwards [sectorCurrying_ae n u, rawSectorCurrying_symmetric_ae n u] with k hk hs
  rw [hk]
  exact kernelRepresentative_sliceProjection n _ ((GW.Fock.ordinaryKernelFixed_iff n _).mpr hs)

/-- Canonical representative sections of the exact source composition, with one a.e.
quantifier for the external momentum and one for the remaining coordinates. -/
theorem sectorCurrying_sections (n : ℕ) (u : GW.Fock.Sector (n+1)) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      (GW.Fock.kernelFixedInclusion n
        (GW.Fock.ordinarySectorKernel n (sectorCurrying n u k)) : GW.Fock.AmbientSector n) =ᵐ[GW.Fock.sectorMeasure n]
          (fun K => GW.Fock.sectorInclusion n u ((GW.Fock.splitCoordinates n 0).symm (k,K))) := by
  have hp := productUnitary_sections volume (GW.Fock.sectorMeasure n) (rawSectorCurrying n u)
  have he : GW.Fock.productUnitary volume (GW.Fock.sectorMeasure n) (rawSectorCurrying n u) =
      GW.Fock.splitUnitary n 0 (GW.Fock.sectorInclusion n u) :=
    ambientCurrying_product n (GW.Fock.sectorInclusion n u)
  rw [he] at hp
  have hs := Measure.ae_ae_of_ae_prod (GW.Fock.splitUnitary_ae n 0 (GW.Fock.sectorInclusion n u))
  filter_upwards [hp, hs, sectorCurrying_kernelRepresentative_ae n u] with k hk hs₀ hr
  rw [hr]
  exact hk.symm.trans hs₀

/-- The section and membership statement for arbitrary source and target representatives.
No value of either L² class at a prescribed momentum is used. -/
theorem sectorCurrying_arbitrary_representatives (n : ℕ) (u : GW.Fock.Sector (n+1))
    (r : GW.Fock.Coordinates (n+1) → ℂ)
    (hr : (GW.Fock.sectorInclusion n u : GW.Fock.Coordinates (n+1) → ℂ) =ᵐ[GW.Fock.sectorMeasure (n+1)] r)
    (s : GW.Space → GW.Fock.Sector n)
    (hs : (sectorCurrying n u : GW.Space → GW.Fock.Sector n) =ᵐ[volume] s) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      MemLp (fun K => r ((GW.Fock.splitCoordinates n 0).symm (k,K))) 2 (GW.Fock.sectorMeasure n) ∧
        (GW.Fock.kernelFixedInclusion n (GW.Fock.ordinarySectorKernel n (s k)) : GW.Fock.AmbientSector n) =ᵐ[GW.Fock.sectorMeasure n]
          (fun K => r ((GW.Fock.splitCoordinates n 0).symm (k,K))) := by
  have hi := Measure.ae_ae_of_ae_prod
    ((GW.Fock.splitCoordinates_inverse_preserving n 0).quasiMeasurePreserving.ae hr)
  filter_upwards [sectorCurrying_sections n u, hi, hs] with k hk hi₀ hs₀
  have h : (GW.Fock.kernelFixedInclusion n (GW.Fock.ordinarySectorKernel n (s k)) : GW.Fock.AmbientSector n) =ᵐ[GW.Fock.sectorMeasure n]
      (fun K => r ((GW.Fock.splitCoordinates n 0).symm (k,K))) := by
    rw [← hs₀]
    exact hk.trans hi₀
  exact ⟨(Lp.memLp _).ae_eq h, h⟩

end Froehlich
