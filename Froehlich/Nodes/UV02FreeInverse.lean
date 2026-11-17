import Froehlich.Nodes.UV02ShiftWeights
import Froehlich.Nodes.FD02WeightedConjugation
import Froehlich.Nodes.FD02Multipliers

/-! The genuine bounded reciprocal of F+c on the retained Fock carrier,
constructed using the existing maximal weighted-domain coordinates. -/
noncomputable section
open MeasureTheory Filter
namespace Froehlich
variable (P : GW.Space) (c : ℝ) (hc : 1 ≤ c)

abbrev FreeShiftDomain := GW.Spaces.WeightedDomain (freeShiftWeightedGraph P c hc)

def freeShiftCoordinates : FreeShiftDomain P c hc ≃ₗᵢ[ℂ] GW.Fock.Carrier :=
  fockWeightedCoordinates (freeShiftWeight P c) (freeShiftWeight_measurable P c)
    (freeShiftWeight_lower P c hc) (freeShiftWeight_permutation P c)

def freeShiftInclusion : FreeShiftDomain P c hc →L[ℂ] GW.Fock.Carrier :=
  fockWeightedInclusion (freeShiftWeight P c) (freeShiftWeight_measurable P c)
    (freeShiftWeight_lower P c hc) (freeShiftWeight_permutation P c)

def freeShiftInverse : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  (freeShiftInclusion P c hc).comp (freeShiftCoordinates P c hc).symm.toLinearIsometry.toContinuousLinearMap

theorem freeShiftInverse_norm_le : ‖freeShiftInverse P c hc‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  have h := fockWeightedInclusion_norm_le (freeShiftWeight P c) (freeShiftWeight_measurable P c)
    (freeShiftWeight_lower P c hc) (freeShiftWeight_permutation P c) ((freeShiftCoordinates P c hc).symm f)
  change ‖freeShiftInverse P c hc f‖ ≤ _ at h
  change ‖freeShiftInverse P c hc f‖ ≤ 1*‖f‖
  rw [one_mul]
  exact h.trans_eq ((freeShiftCoordinates P c hc).symm.norm_map f)

theorem freeShiftInverse_weighted_ae (f : GW.Fock.Carrier) (n : ℕ) :
    (fun K => (freeShiftWeight P c n K : ℂ)*physicalSector n (freeShiftInverse P c hc f n) K)
      =ᵐ[GW.Fock.sectorMeasure n] physicalSector n (f n) := by
  let u := (freeShiftCoordinates P c hc).symm f
  have h := fockWeightedCoordinates_physical (freeShiftWeight P c) (freeShiftWeight_measurable P c)
    (freeShiftWeight_lower P c hc) (freeShiftWeight_permutation P c) u n
  have hi := fockWeightedInclusion_apply (freeShiftWeight P c) (freeShiftWeight_measurable P c)
    (freeShiftWeight_lower P c hc) (freeShiftWeight_permutation P c) u
  change freeShiftInclusion P c hc u = _ at hi
  have hu : freeShiftCoordinates P c hc u=f := (freeShiftCoordinates P c hc).apply_symm_apply f
  change (fun K => (freeShiftWeight P c n K : ℂ)*physicalSector n (freeShiftInclusion P c hc u n) K)
    =ᵐ[GW.Fock.sectorMeasure n] physicalSector n (f n)
  rw [hi]
  change (fun K => (freeShiftWeight P c n K : ℂ)*physicalSector n (weightedFockValue _ _ _ _ u n) K)
    =ᵐ[GW.Fock.sectorMeasure n] physicalSector n (freeShiftCoordinates P c hc u n) at h
  rw [hu] at h
  exact h

theorem freeShiftInverse_graph (f : GW.Fock.Carrier) :
    (freeShiftInverse P c hc f,f) ∈ (fockRealMultiplier (freeShiftWeight P c)).graph :=
  (fockRealMultiplier_graph_ae_iff _ _ _).mpr (fun n => freeShiftInverse_weighted_ae P c hc f n)

end Froehlich
