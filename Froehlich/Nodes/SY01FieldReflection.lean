import Froehlich.Nodes.SY01FieldConjugation

/-! Reflection covariance of the actual Bochner annihilation field, including
reflection of the external momentum variable. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

theorem reflectedInsertion (n : ℕ) (k : GW.Space) (K : GW.Fock.Coordinates n) :
    (fun i => -((GW.Fock.splitCoordinates n 0).symm (k,K)) i) =
      (GW.Fock.splitCoordinates n 0).symm (-k,fun i => -K i) := by
  funext i
  rcases Fin.eq_self_or_eq_succAbove (0 : Fin (n+1)) i with rfl | ⟨j,rfl⟩
  · rw [GW.Fock.insertCoordinate_same, GW.Fock.insertCoordinate_same]
  · rw [GW.Fock.insertCoordinate_succAbove, GW.Fock.insertCoordinate_succAbove]

def outerFieldReflection :
    Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) →ₗᵢ[ℂ]
      Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun k : GW.Space => -k) space_negation_preserving

def reflectFockField :
    Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) →L[ℂ]
      Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) :=
  (fockReflection.compLpL 2 volume).comp outerFieldReflection.toContinuousLinearMap

theorem reflectFockField_ae (u : Lp GW.Fock.Carrier 2 (volume : Measure GW.Space)) :
    reflectFockField u =ᵐ[volume] (fun k => fockReflection (u (-k))) := by
  have ho : outerFieldReflection u =ᵐ[volume] (fun k => u (-k)) :=
    Lp.coeFn_compMeasurePreserving u space_negation_preserving
  filter_upwards [ho, fockReflection.coeFn_compLp (outerFieldReflection u)] with k ho hi
  have he : reflectFockField u k = fockReflection (outerFieldReflection u k) := hi
  rw [he, ho]

theorem annihilationField_reflection (x : NumberFormSpace) :
    annihilationField (numberReflection x) = reflectFockField (annihilationField x) := by
  have hj := annihilationField_representative_common_ae (numberReflection x)
  rw [numberReflection_intertwines] at hj
  have ha := space_negation_preserving.quasiMeasurePreserving.ae
    (annihilationField_representative_common_ae x)
  have hi (n : ℕ) := Measure.ae_ae_of_ae_prod
    ((GW.Fock.splitCoordinates_inverse_preserving n 0).quasiMeasurePreserving.ae
      (fockReflection_physical (numberFormEmbedding x) (n+1)))
  apply Lp.ext
  filter_upwards [hj, ha, ae_all_iff.mpr hi, reflectFockField_ae (annihilationField x)]
    with k hj ha hi hfield
  rw [hfield]
  apply lp.ext
  funext n
  apply (physicalSector n).injective
  apply Lp.ext
  have hjn := hj n
  have han := ha n
  rw [kernelRepresentative_physical] at hjn han
  have hneg := (configurationNegation_preserving n).quasiMeasurePreserving.ae han
  filter_upwards [hjn, hneg, hi n, fockReflection_physical (annihilationField x (-k)) n]
    with K hj ha hi hr
  change physicalSector n (annihilationField x (-k) n) (fun i => -K i) =
    (Real.sqrt (n+1 : ℕ) : ℂ) • GW.Fock.sectorInclusion n (numberFormEmbedding x (n+1))
      ((GW.Fock.splitCoordinates n 0).symm (-k,fun i => -K i)) at ha
  change physicalSector (n+1) (fockReflection (numberFormEmbedding x) (n+1))
      ((GW.Fock.splitCoordinates n 0).symm (k,K)) =
    physicalSector (n+1) (numberFormEmbedding x (n+1))
      (fun i => -((GW.Fock.splitCoordinates n 0).symm (k,K)) i) at hi
  rw [hj, hr, ha]
  change (Real.sqrt (n+1 : ℕ) : ℂ) •
      physicalSector (n+1) (fockReflection (numberFormEmbedding x) (n+1))
        ((GW.Fock.splitCoordinates n 0).symm (k,K)) = _
  rw [hi, reflectedInsertion]
  rfl

theorem annihilationField_reflection_ae (x : NumberFormSpace) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      annihilationField (numberReflection x) k = fockReflection (annihilationField x (-k)) := by
  rw [annihilationField_reflection]
  exact reflectFockField_ae (annihilationField x)

end Froehlich
