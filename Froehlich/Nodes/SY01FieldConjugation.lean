import Froehlich.Nodes.SY01NumberMaps
import Froehlich.Nodes.FC01Fields

/-! Conjugation covariance of the genuine Bochner annihilation field. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

def fockConjugationIsometry : GW.Fock.Carrier →ₗᵢ⋆[ℂ] GW.Fock.Carrier where
  toLinearMap :=
    { toFun := fockConjugation
      map_add' := fockConjugation_add
      map_smul' := fockConjugation_smul }
  norm_map' := fockConjugation_norm

def conjugateFockField :
    Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) →L⋆[ℂ]
      Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) :=
  fockConjugationIsometry.toContinuousLinearMap.compLpL 2 volume

theorem annihilationField_conjugation (x : NumberFormSpace) :
    annihilationField (numberConjugation x) = conjugateFockField (annihilationField x) := by
  have ha := annihilationField_representative_common_ae x
  have hj := annihilationField_representative_common_ae (numberConjugation x)
  rw [numberConjugation_intertwines] at hj
  have hi (n : ℕ) := Measure.ae_ae_of_ae_prod
    ((GW.Fock.splitCoordinates_inverse_preserving n 0).quasiMeasurePreserving.ae
      (fockConjugation_physical (numberFormEmbedding x) (n+1)))
  apply Lp.ext
  filter_upwards [ha, hj, ae_all_iff.mpr hi,
    fockConjugationIsometry.toContinuousLinearMap.coeFn_compLp (annihilationField x)] with k ha hj hi hfield
  have he : conjugateFockField (annihilationField x) k = fockConjugation (annihilationField x k) := hfield
  rw [he]
  apply lp.ext
  funext n
  apply (physicalSector n).injective
  apply Lp.ext
  have han := ha n
  have hjn := hj n
  rw [kernelRepresentative_physical] at han hjn
  filter_upwards [han, hjn, hi n, fockConjugation_physical (annihilationField x k) n]
    with K ha hj hi hr
  change physicalSector (n+1) (fockConjugation (numberFormEmbedding x) (n+1))
      ((GW.Fock.splitCoordinates n 0).symm (k,K)) =
    (starRingEnd ℂ) (physicalSector (n+1) (numberFormEmbedding x (n+1))
      ((GW.Fock.splitCoordinates n 0).symm (k,K))) at hi
  rw [hj, hr, ha]
  change (Real.sqrt (n+1 : ℕ) : ℂ) *
      physicalSector (n+1) (fockConjugation (numberFormEmbedding x) (n+1))
        ((GW.Fock.splitCoordinates n 0).symm (k,K)) = _
  rw [hi]
  dsimp only [physicalSector]
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]

theorem annihilationField_conjugation_ae (x : NumberFormSpace) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      annihilationField (numberConjugation x) k = fockConjugation (annihilationField x k) := by
  rw [annihilationField_conjugation]
  exact fockConjugationIsometry.toContinuousLinearMap.coeFn_compLp (annihilationField x)

end Froehlich
