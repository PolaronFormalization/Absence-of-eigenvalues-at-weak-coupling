import Froehlich.Nodes.SY01FieldReflection

/-! Symmetry covariance of the actual maximal smeared annihilation operators,
on their retained continuous number-graph restrictions. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

def conjugateOnePhonon (f : GW.OnePhonon) : GW.OnePhonon :=
  Complex.conjCLE.toContinuousLinearMap.compLp f

def reflectOnePhonon (f : GW.OnePhonon) : GW.OnePhonon :=
  Lp.compMeasurePreserving (fun k : GW.Space => -k) space_negation_preserving f

theorem conjugateOnePhonon_ae (f : GW.OnePhonon) :
    conjugateOnePhonon f =ᵐ[volume] (fun k => (starRingEnd ℂ) (f k)) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLp f

theorem reflectOnePhonon_ae (f : GW.OnePhonon) :
    reflectOnePhonon f =ᵐ[volume] (fun k => f (-k)) :=
  Lp.coeFn_compMeasurePreserving f space_negation_preserving

theorem conjugation_commutes_real_smul (r : ℝ) (z : ℂ) :
    (starRingEnd ℂ) (r • z) = r • (starRingEnd ℂ) z := by
  change (starRingEnd ℂ) ((r : ℂ) * z) = (r : ℂ) * (starRingEnd ℂ) z
  rw [map_mul, Complex.conj_ofReal]

theorem annihilationRestriction_conjugation (f : GW.OnePhonon) (x : NumberFormSpace) :
    annihilationRestriction (conjugateOnePhonon f) (numberConjugation x) =
      fockConjugation (annihilationRestriction f x) := by
  rw [annihilationRestriction_integral, annihilationRestriction_integral]
  have hi := annihilationRestriction_integrable f x
  have hc := ContinuousLinearMap.integral_comp_commSL conjugation_commutes_real_smul
    fockConjugationIsometry.toContinuousLinearMap hi
  change (∫ k : GW.Space, (starRingEnd ℂ) (conjugateOnePhonon f k) •
    annihilationField (numberConjugation x) k) = _
  change (∫ k : GW.Space, fockConjugation ((starRingEnd ℂ) (f k) • annihilationField x k)) =
    fockConjugation (∫ k : GW.Space, (starRingEnd ℂ) (f k) • annihilationField x k) at hc
  rw [← hc]
  apply integral_congr_ae
  filter_upwards [conjugateOnePhonon_ae f, annihilationField_conjugation_ae x] with k hf hx
  rw [hf, hx, starRingEnd_self_apply]
  simpa only [starRingEnd_self_apply] using
    (fockConjugation_smul ((starRingEnd ℂ) (f k)) (annihilationField x k)).symm

theorem annihilationRestriction_reflection (f : GW.OnePhonon) (x : NumberFormSpace) :
    annihilationRestriction (reflectOnePhonon f) (numberReflection x) =
      fockReflection (annihilationRestriction f x) := by
  rw [annihilationRestriction_integral, annihilationRestriction_integral]
  have hi := annihilationRestriction_integrable f x
  have hneg := space_negation_preserving.integrable_comp_of_integrable hi
  have hc := fockReflection.integral_comp_comm hneg
  calc
    _ = ∫ k : GW.Space, fockReflection ((starRingEnd ℂ) (f (-k)) • annihilationField x (-k)) := by
      apply integral_congr_ae
      filter_upwards [reflectOnePhonon_ae f, annihilationField_reflection_ae x] with k hf hx
      rw [hf, hx, map_smul]
    _ = fockReflection (∫ k : GW.Space, (starRingEnd ℂ) (f (-k)) • annihilationField x (-k)) := hc
    _ = _ := congrArg fockReflection
      (space_negation_preserving.integral_comp (MeasurableEquiv.neg GW.Space).measurableEmbedding
        (fun k => (starRingEnd ℂ) (f k) • annihilationField x k))

end Froehlich
