import Froehlich.Nodes.LD01
import Froehlich.Nodes.EN02Dual
import GW.Analysis.Fourier

/-! TR01 (`lem:translationadapter`): the source momentum translation is the
retained GW translation with the opposite sign. Energy translations preserve
physical vectors through their actual reciprocal-weight embeddings. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Froehlich

theorem retainedTranslation_inverse (P : GW.Space) (f : GW.OnePhonon) :
    GW.Analysis.translation (-P) (GW.Analysis.translation P f) = f := by
  apply Lp.ext
  have hi := (measurePreserving_sub_right (volume : Measure GW.Space) (-P)).quasiMeasurePreserving.ae
    (GW.Analysis.translation_ae P f)
  filter_upwards [GW.Analysis.translation_ae (-P) (GW.Analysis.translation P f), hi] with q ho hi
  rw [ho, hi]
  simp only [sub_neg_eq_add, add_sub_cancel_right]

/-- The exact source convention `τ_P f(q)=f(q+P)`. -/
def momentumTranslation (P : GW.Space) : GW.OnePhonon ≃ₗᵢ[ℂ] GW.OnePhonon :=
  LinearIsometryEquiv.ofSurjective (GW.Analysis.translation (-P)) (by
    intro f
    exact ⟨GW.Analysis.translation P f, retainedTranslation_inverse P f⟩)

theorem momentumTranslation_ae (P : GW.Space) (f : GW.OnePhonon) :
    momentumTranslation P f =ᵐ[volume] (fun q => f (q + P)) := by
  change GW.Analysis.translation (-P) f =ᵐ[volume] _
  simpa only [sub_neg_eq_add] using GW.Analysis.translation_ae (-P) f

theorem momentumTranslation_symm_apply (P : GW.Space) (f : GW.OnePhonon) :
    (momentumTranslation P).symm f = GW.Analysis.translation P f := by
  apply (momentumTranslation P).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (retainedTranslation_inverse P f).symm

def isolatedEnergyCoordinates (P : GW.Space) : OneParticleEnergySpace P ≃ₗᵢ[ℂ] GW.OnePhonon :=
  GW.Spaces.WeightedL2.coordinates (H := ℂ) (w := oneParticleEnergyWeight P)
    (μ := (volume : Measure GW.Space))

/-- Isometry from the isolated graph norm at P onto that at zero. -/
def energyTranslation (P : GW.Space) : OneParticleEnergySpace P ≃ₗᵢ[ℂ] OneParticleEnergySpace 0 :=
  ((isolatedEnergyCoordinates P).trans (momentumTranslation P)).trans (isolatedEnergyCoordinates 0).symm

theorem energyTranslation_coordinates (P : GW.Space) (f : OneParticleEnergySpace P) :
    isolatedEnergyCoordinates 0 (energyTranslation P f) =
      momentumTranslation P (isolatedEnergyCoordinates P f) := rfl

theorem oneParticleEnergyWeight_translation (P q : GW.Space) :
    oneParticleEnergyWeight P (q + P) = oneParticleEnergyWeight 0 q := by
  simp only [oneParticleEnergyWeight, add_sub_cancel_right, sub_zero]

theorem energyTranslation_intertwines (P : GW.Space) (f : OneParticleEnergySpace P) :
    oneParticleEnergyEmbedding 0 (energyTranslation P f) =
      momentumTranslation P (oneParticleEnergyEmbedding P f) := by
  apply Lp.ext
  have h0 := GW.Spaces.WeightedL2.embed_ae (oneParticleEnergyWeight_measurable 0)
    (oneParticleEnergyWeight_ge_one 0) (energyTranslation P f)
  have hs := (space_translation_preserving P).quasiMeasurePreserving.ae
    (GW.Spaces.WeightedL2.embed_ae (oneParticleEnergyWeight_measurable P)
      (oneParticleEnergyWeight_ge_one P) f)
  filter_upwards [h0, hs, momentumTranslation_ae P (isolatedEnergyCoordinates P f),
    momentumTranslation_ae P (oneParticleEnergyEmbedding P f)] with q h0 hs hc hp
  change (((oneParticleEnergyWeight 0 q)⁻¹ : ℝ) : ℂ) •
    momentumTranslation P (isolatedEnergyCoordinates P f) q =
      oneParticleEnergyEmbedding 0 (energyTranslation P f) q at h0
  change (((oneParticleEnergyWeight P (q + P))⁻¹ : ℝ) : ℂ) •
    isolatedEnergyCoordinates P f (q + P) = oneParticleEnergyEmbedding P f (q + P) at hs
  rw [hp, ← hs, ← h0, hc, oneParticleEnergyWeight_translation]

theorem energyTranslation_symm_intertwines (P : GW.Space) (f : OneParticleEnergySpace 0) :
    oneParticleEnergyEmbedding P ((energyTranslation P).symm f) =
      (momentumTranslation P).symm (oneParticleEnergyEmbedding 0 f) := by
  apply (momentumTranslation P).injective
  rw [← energyTranslation_intertwines, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]

theorem energyTranslation_norm (P : GW.Space) (f : OneParticleEnergySpace P) :
    ‖energyTranslation P f‖ = ‖f‖ := (energyTranslation P).norm_map f

def translatedFiberSourceLoad (g : ℝ) (P : GW.Space) : ConjugateLoad (OneParticleEnergySpace 0) :=
  (isolatedFiberSourceLoad g P).comp (energyTranslation P).symm.toLinearIsometry.toContinuousLinearMap

/-- The manuscript's linear source functional, distinguished from the weak
conjugate-linear load. -/
def translatedLinearSource (g : ℝ) (P : GW.Space) : OneParticleEnergySpace 0 →L[ℂ] ℂ :=
  linearizedLoad (translatedFiberSourceLoad g P)

theorem translatedSource_pairing_ae (g : ℝ) (P : GW.Space) (f : OneParticleEnergySpace 0) :
    (fun q => (starRingEnd ℂ) (GW.Analysis.translation P (oneParticleEnergyEmbedding 0 f) (q + P)) *
      (fiberFormFactor g (q + P) : ℂ)) =ᵐ[volume]
        (fun q => (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q) * (fiberFormFactor g (q + P) : ℂ)) := by
  have ht := (space_translation_preserving P).quasiMeasurePreserving.ae
    (GW.Analysis.translation_ae P (oneParticleEnergyEmbedding 0 f))
  filter_upwards [ht] with q hq
  simp only [add_sub_cancel_right] at hq
  rw [hq]

theorem translatedFiberSourceLoad_integrable (g : ℝ) (P : GW.Space) (f : OneParticleEnergySpace 0) :
    Integrable (fun q => (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q) *
      (fiberFormFactor g (q + P) : ℂ)) volume := by
  have hi := weightedSource_pairing_integrable (oneParticleEnergyWeight P)
    (oneParticleEnergyWeight_measurable P) (oneParticleEnergyWeight_ge_one P)
    (fun k => (fiberFormFactor g k : ℂ)) (fiberSource_quotient_memLp g P) ((energyTranslation P).symm f)
  change Integrable (fun k => (starRingEnd ℂ)
    (oneParticleEnergyEmbedding P ((energyTranslation P).symm f) k) * (fiberFormFactor g k : ℂ)) volume at hi
  rw [energyTranslation_symm_intertwines, momentumTranslation_symm_apply] at hi
  have ht := (space_translation_preserving P).integrable_comp_of_integrable hi
  exact ht.congr (translatedSource_pairing_ae g P f)

theorem translatedFiberSourceLoad_integral (g : ℝ) (P : GW.Space) (f : OneParticleEnergySpace 0) :
    translatedFiberSourceLoad g P f = ∫ q : GW.Space,
      (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q) * (fiberFormFactor g (q + P) : ℂ) := by
  change weightedSourceLoad (oneParticleEnergyWeight P) (fun k => (fiberFormFactor g k : ℂ))
    (fiberSource_quotient_memLp g P) ((energyTranslation P).symm f) = _
  rw [weightedSourceLoad_integral (oneParticleEnergyWeight P)
    (oneParticleEnergyWeight_measurable P) (oneParticleEnergyWeight_ge_one P)]
  change (∫ k : GW.Space, (starRingEnd ℂ)
    (oneParticleEnergyEmbedding P ((energyTranslation P).symm f) k) * (fiberFormFactor g k : ℂ)) = _
  rw [energyTranslation_symm_intertwines, momentumTranslation_symm_apply]
  calc
    _ = ∫ q : GW.Space, (starRingEnd ℂ) (GW.Analysis.translation P (oneParticleEnergyEmbedding 0 f) (q + P)) *
        (fiberFormFactor g (q + P) : ℂ) :=
      (integral_add_right_eq_self (fun k => (starRingEnd ℂ)
        (GW.Analysis.translation P (oneParticleEnergyEmbedding 0 f) k) * (fiberFormFactor g k : ℂ)) P).symm
    _ = _ := integral_congr_ae (translatedSource_pairing_ae g P f)

theorem translatedLinearSource_integral (g : ℝ) (P : GW.Space) (f : OneParticleEnergySpace 0) :
    translatedLinearSource g P f =
      ∫ q : GW.Space, (fiberFormFactor g (q + P) : ℂ) * oneParticleEnergyEmbedding 0 f q := by
  change linearizedLoad (translatedFiberSourceLoad g P) f = _
  rw [linearizedLoad_apply, translatedFiberSourceLoad_integral, Complex.star_def, ← integral_conj]
  apply integral_congr_ae
  exact Eventually.of_forall (fun q => by
    change (starRingEnd ℂ) ((starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q) *
      (fiberFormFactor g (q + P) : ℂ)) =
        (fiberFormFactor g (q + P) : ℂ) * oneParticleEnergyEmbedding 0 f q
    rw [map_mul, starRingEnd_self_apply, Complex.conj_ofReal, mul_comm])

theorem translatedLinearSource_integrable (g : ℝ) (P : GW.Space) (f : OneParticleEnergySpace 0) :
    Integrable (fun q => (fiberFormFactor g (q + P) : ℂ) * oneParticleEnergyEmbedding 0 f q) volume := by
  have hm : AEStronglyMeasurable
      (fun q => (fiberFormFactor g (q + P) : ℂ) * oneParticleEnergyEmbedding 0 f q) volume :=
    ((Complex.continuous_ofReal.measurable.comp
      ((fiberFormFactor_measurable g).comp (measurable_id.add_const P))).aestronglyMeasurable).mul
        (Lp.memLp (oneParticleEnergyEmbedding 0 f)).aestronglyMeasurable
  apply (translatedFiberSourceLoad_integrable g P f).mono hm
  exact Eventually.of_forall (fun q => by
    simp only [norm_mul, RCLike.norm_conj, mul_comm]
    exact le_rfl)

theorem translatedFiberSourceLoad_norm_le (g : ℝ) (P : GW.Space) :
    ‖translatedFiberSourceLoad g P‖ ≤ ‖isolatedFiberSourceLoad g P‖ := by
  let F : ConjugateLoad (OneParticleEnergySpace P) := isolatedFiberSourceLoad g P
  change ‖translatedFiberSourceLoad g P‖ ≤ ‖F‖
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
  intro f
  change ‖F ((energyTranslation P).symm f)‖ ≤ _
  simpa only [LinearIsometryEquiv.norm_map] using F.le_opNorm ((energyTranslation P).symm f)

theorem translatedLinearSource_norm_le (g : ℝ) (P : GW.Space) :
    ‖translatedLinearSource g P‖ ≤ ‖translatedFiberSourceLoad g P‖ := by
  let F : ConjugateLoad (OneParticleEnergySpace 0) := translatedFiberSourceLoad g P
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
  intro f
  change ‖linearizedLoad F f‖ ≤ _
  rw [linearizedLoad_apply, norm_star]
  exact F.le_opNorm f

theorem translatedSource_uniform_bound : ∃ Cv : ℝ, 0 < Cv ∧ ∀ (g : ℝ) (P : GW.Space),
    ‖translatedFiberSourceLoad g P‖ ^ 2 ≤ Cv * g ^ 2 ∧
      ‖translatedLinearSource g P‖ ^ 2 ≤ Cv * g ^ 2 := by
  obtain ⟨Cv, hCv, hb⟩ := fiberSourceLoads_uniform_bound
  refine ⟨Cv, hCv, fun g P => ?_⟩
  have hc := translatedFiberSourceLoad_norm_le g P
  have hl := (translatedLinearSource_norm_le g P).trans hc
  exact ⟨((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hc).trans (hb g P).1,
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hl).trans (hb g P).1⟩

/-- Positivity is transported as a form on energy coordinates, applying the
inverse translation to both arguments. -/
theorem energyTranslation_nonnegative_iff (P : GW.Space)
    (T : OneParticleEnergySpace P →L[ℂ] OneParticleEnergySpace P) :
    (∀ x, 0 ≤ (⟪x,T x⟫_ℂ).re) ↔
      ∀ y, 0 ≤ (⟪y,transportFormOperator (energyTranslation P).symm.toLinearIsometry.toContinuousLinearMap T y⟫_ℂ).re := by
  constructor
  · intro h y
    rw [← transportFormOperator_spec]
    exact h _
  · intro h x
    have hy := h (energyTranslation P x)
    rw [← transportFormOperator_spec] at hy
    change 0 ≤ (⟪(energyTranslation P).symm (energyTranslation P x),
      T ((energyTranslation P).symm (energyTranslation P x))⟫_ℂ).re at hy
    rw [LinearIsometryEquiv.symm_apply_apply] at hy
    exact hy

end Froehlich
