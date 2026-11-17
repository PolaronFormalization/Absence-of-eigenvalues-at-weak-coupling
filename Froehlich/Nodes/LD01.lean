import Froehlich.Nodes.BA01
import GW.Spaces.WeightedL2
import Froehlich.Nodes.EN02OneParticle
import Froehlich.Nodes.AN02
import Froehlich.Nodes.GW05

/-! LD01 (`lem:weightedloads`): a singular measurable source is represented
by its weighted L² quotient, never by an assumed physical Hilbert vector. -/

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace Froehlich

def weightedSourceCoordinate (w : GW.Space → ℝ) (s : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (w k : ℂ)) 2 volume) : GW.OnePhonon :=
  hs.toLp (fun k => s k / (w k : ℂ))

theorem weightedSourceCoordinate_ae (w : GW.Space → ℝ) (s : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (w k : ℂ)) 2 volume) :
    (weightedSourceCoordinate w s hs : GW.Space → ℂ) =ᵐ[volume]
      (fun k => s k / (w k : ℂ)) := hs.coeFn_toLp

def weightedSourceLoad (w : GW.Space → ℝ) (s : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (w k : ℂ)) 2 volume) :
    ConjugateLoad (GW.Spaces.WeightedL2 ℂ w (volume : Measure GW.Space)) :=
  (innerSLFlip ℂ (weightedSourceCoordinate w s hs)).comp
    GW.Spaces.WeightedL2.coordinates.toLinearIsometry.toContinuousLinearMap

theorem weightedSourceLoad_apply (w : GW.Space → ℝ) (s : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (w k : ℂ)) 2 volume)
    (f : GW.Spaces.WeightedL2 ℂ w (volume : Measure GW.Space)) :
    weightedSourceLoad w s hs f =
      ⟪GW.Spaces.WeightedL2.coordinates f, weightedSourceCoordinate w s hs⟫_ℂ := rfl

theorem weightedSourceLoad_riesz (w : GW.Space → ℝ) (s : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (w k : ℂ)) 2 volume) :
    loadRiesz (weightedSourceLoad w s hs) =
      GW.Spaces.WeightedL2.coordinates.symm (weightedSourceCoordinate w s hs) := by
  apply Eq.symm
  apply loadRiesz_unique
  intro f
  rw [weightedSourceLoad_apply]
  rfl

theorem weightedSourceLoad_norm (w : GW.Space → ℝ) (s : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (w k : ℂ)) 2 volume) :
    ‖weightedSourceLoad w s hs‖ = ‖weightedSourceCoordinate w s hs‖ := by
  rw [← loadRiesz_norm, weightedSourceLoad_riesz, LinearIsometryEquiv.norm_map]

theorem weightedSourceLoad_riesz_coordinate (w : GW.Space → ℝ) (s : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (w k : ℂ)) 2 volume) :
    GW.Spaces.WeightedL2.coordinates (loadRiesz (weightedSourceLoad w s hs)) =
      weightedSourceCoordinate w s hs := by
  rw [weightedSourceLoad_riesz, LinearIsometryEquiv.apply_symm_apply]

theorem weightedSource_pairing_ae (w : GW.Space → ℝ) (hw : Measurable w)
    (hw1 : ∀ k, 1 ≤ w k) (s : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (w k : ℂ)) 2 volume)
    (f : GW.Spaces.WeightedL2 ℂ w (volume : Measure GW.Space)) :
    (fun k => (starRingEnd ℂ) (GW.Spaces.WeightedL2.embed hw hw1 f k) * s k) =ᵐ[volume]
      (fun k => ⟪GW.Spaces.WeightedL2.coordinates f k, weightedSourceCoordinate w s hs k⟫_ℂ) := by
  filter_upwards [GW.Spaces.WeightedL2.weighted_embed_ae hw hw1 f,
    weightedSourceCoordinate_ae w s hs] with k hf hk
  rw [RCLike.inner_apply', hk, ← hf]
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
  have hne : (w k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans_le (hw1 k)))
  field_simp [hne] <;> ring

theorem weightedSource_pairing_integrable (w : GW.Space → ℝ) (hw : Measurable w)
    (hw1 : ∀ k, 1 ≤ w k) (s : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (w k : ℂ)) 2 volume)
    (f : GW.Spaces.WeightedL2 ℂ w (volume : Measure GW.Space)) :
    Integrable (fun k => (starRingEnd ℂ) (GW.Spaces.WeightedL2.embed hw hw1 f k) * s k) volume :=
  (L2.integrable_inner (𝕜 := ℂ) (GW.Spaces.WeightedL2.coordinates f) (weightedSourceCoordinate w s hs)).congr
    (weightedSource_pairing_ae w hw hw1 s hs f).symm

theorem weightedSourceLoad_integral (w : GW.Space → ℝ) (hw : Measurable w)
    (hw1 : ∀ k, 1 ≤ w k) (s : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (w k : ℂ)) 2 volume)
    (f : GW.Spaces.WeightedL2 ℂ w (volume : Measure GW.Space)) :
    weightedSourceLoad w s hs f =
      ∫ k : GW.Space, (starRingEnd ℂ) (GW.Spaces.WeightedL2.embed hw hw1 f k) * s k := by
  rw [weightedSourceLoad_apply, L2.inner_def]
  exact integral_congr_ae (weightedSource_pairing_ae w hw hw1 s hs f).symm

theorem weightedSourceLoad_norm_sub (w : GW.Space → ℝ) (s t : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (w k : ℂ)) 2 volume)
    (ht : MemLp (fun k => t k / (w k : ℂ)) 2 volume) :
    ‖weightedSourceLoad w s hs - weightedSourceLoad w t ht‖ =
      ‖weightedSourceCoordinate w s hs - weightedSourceCoordinate w t ht‖ := by
  have hsub := (loadRieszLinearIsometry
    (V := GW.Spaces.WeightedL2 ℂ w (volume : Measure GW.Space))).map_sub
      (weightedSourceLoad w s hs) (weightedSourceLoad w t ht)
  change loadRiesz (weightedSourceLoad w s hs - weightedSourceLoad w t ht) =
    loadRiesz (weightedSourceLoad w s hs) - loadRiesz (weightedSourceLoad w t ht) at hsub
  rw [← loadRiesz_norm, hsub, weightedSourceLoad_riesz, weightedSourceLoad_riesz]
  rfl

theorem weightedSourceLoad_tendsto {ι : Type*} {l : Filter ι}
    (w : GW.Space → ℝ) (s : ι → GW.Space → ℂ) (t : GW.Space → ℂ)
    (hs : ∀ i, MemLp (fun k => s i k / (w k : ℂ)) 2 volume)
    (ht : MemLp (fun k => t k / (w k : ℂ)) 2 volume)
    (h : Tendsto (fun i => weightedSourceCoordinate w (s i) (hs i)) l
      (𝓝 (weightedSourceCoordinate w t ht))) :
    Tendsto (fun i => weightedSourceLoad w (s i) (hs i)) l (𝓝 (weightedSourceLoad w t ht)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [weightedSourceLoad_norm_sub] using tendsto_iff_norm_sub_tendsto_zero.mp h

/-- The source's exact squared-error dominated-convergence criterion, on the
already constructed L² classes. Its majorant is an integrable real function. -/
theorem weightedSourceLoad_tendsto_dominated (w : GW.Space → ℝ)
    (s : ℕ → GW.Space → ℂ) (t : GW.Space → ℂ)
    (hs : ∀ n, MemLp (fun k => s n k / (w k : ℂ)) 2 volume)
    (ht : MemLp (fun k => t k / (w k : ℂ)) 2 volume)
    (hl : ∀ᵐ k ∂(volume : Measure GW.Space),
      Tendsto (fun n => s n k / (w k : ℂ)) atTop (𝓝 (t k / (w k : ℂ))))
    (M : GW.Space → ℝ) (hM : Integrable M volume)
    (hb : ∀ n, ∀ᵐ k ∂(volume : Measure GW.Space),
      ‖(s n k - t k) / (w k : ℂ)‖ ^ 2 ≤ M k) :
    Tendsto (fun n => weightedSourceLoad w (s n) (hs n)) atTop (𝓝 (weightedSourceLoad w t ht)) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun k => ‖s n k / (w k : ℂ) - t k / (w k : ℂ)‖ ^ 2) volume :=
    ((hs n).aestronglyMeasurable.sub ht.aestronglyMeasurable).norm.pow (2 : ℕ)
  have hbound (n : ℕ) : ∀ᵐ k ∂(volume : Measure GW.Space),
      ‖‖s n k / (w k : ℂ) - t k / (w k : ℂ)‖ ^ 2‖ ≤ M k := by
    filter_upwards [hb n] with k hk
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [sub_div] using hk
  have hpoint : ∀ᵐ k ∂(volume : Measure GW.Space),
      Tendsto (fun n => ‖s n k / (w k : ℂ) - t k / (w k : ℂ)‖ ^ 2) atTop (𝓝 0) := by
    filter_upwards [hl] with k hk
    simpa using ((hk.sub_const (t k / (w k : ℂ))).norm.pow (2 : ℕ))
  have hi := tendsto_integral_of_dominated_convergence M hm hM hbound hpoint
  have hnormsq : Tendsto (fun n =>
      ‖weightedSourceCoordinate w (s n) (hs n) - weightedSourceCoordinate w t ht‖ ^ 2)
        atTop (𝓝 0) := by
    simpa only [weightedSourceCoordinate, GW.Analysis.l2_class_sub_norm_sq (𝕜 := ℂ), integral_zero]
      using hi
  have hnorm : Tendsto (fun n =>
      ‖weightedSourceCoordinate w (s n) (hs n) - weightedSourceCoordinate w t ht‖)
        atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hnormsq
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using h
  apply weightedSourceLoad_tendsto w s t hs ht
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

/-- Approximate quotient membership follows from the source's squared-error
majorant; it need not be assumed as an additional analytical hypothesis. -/
theorem weightedSource_approximants_memLp_dominated (w : GW.Space → ℝ) (hw : Measurable w)
    (s : ℕ → GW.Space → ℂ) (hsm : ∀ n, Measurable (s n)) (t : GW.Space → ℂ)
    (ht : MemLp (fun k => t k / (w k : ℂ)) 2 volume)
    (M : GW.Space → ℝ) (hM : Integrable M volume)
    (hb : ∀ n, ∀ᵐ k ∂(volume : Measure GW.Space),
      ‖(s n k - t k) / (w k : ℂ)‖ ^ 2 ≤ M k) :
    ∀ n, MemLp (fun k => s n k / (w k : ℂ)) 2 volume := by
  intro n
  have hm : AEStronglyMeasurable (fun k : GW.Space => s n k / (w k : ℂ)) volume :=
    ((hsm n).div (Complex.continuous_ofReal.measurable.comp hw)).aestronglyMeasurable
  have he : AEStronglyMeasurable
      (fun k : GW.Space => s n k / (w k : ℂ) - t k / (w k : ℂ)) volume :=
    hm.sub ht.aestronglyMeasurable
  have hi : Integrable (fun k : GW.Space => ‖s n k / (w k : ℂ) - t k / (w k : ℂ)‖ ^ 2) volume :=
    hM.mono' (he.norm.pow (2 : ℕ)) ((hb n).mono (fun k hk => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa only [sub_div] using hk))
  have heLp := (memLp_two_iff_integrable_sq_norm he).mpr hi
  apply (heLp.add ht).ae_eq
  exact Eventually.of_forall (fun k => sub_add_cancel (s n k / (w k : ℂ)) (t k / (w k : ℂ)))

theorem weightedSourceLoad_tendsto_of_dominated (w : GW.Space → ℝ) (hw : Measurable w)
    (s : ℕ → GW.Space → ℂ) (hsm : ∀ n, Measurable (s n)) (t : GW.Space → ℂ)
    (ht : MemLp (fun k => t k / (w k : ℂ)) 2 volume)
    (hl : ∀ᵐ k ∂(volume : Measure GW.Space),
      Tendsto (fun n => s n k / (w k : ℂ)) atTop (𝓝 (t k / (w k : ℂ))))
    (M : GW.Space → ℝ) (hM : Integrable M volume)
    (hb : ∀ n, ∀ᵐ k ∂(volume : Measure GW.Space),
      ‖(s n k - t k) / (w k : ℂ)‖ ^ 2 ≤ M k) :
    ∃ hs : ∀ n, MemLp (fun k => s n k / (w k : ℂ)) 2 volume,
      Tendsto (fun n => weightedSourceLoad w (s n) (hs n)) atTop (𝓝 (weightedSourceLoad w t ht)) := by
  let hs := weightedSource_approximants_memLp_dominated w hw s hsm t ht M hM hb
  exact ⟨hs, weightedSourceLoad_tendsto_dominated w s t hs ht hl M hM hb⟩

theorem weightedSource_factor_memLp (w : GW.Space → ℝ) (s b : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (w k : ℂ)) 2 volume) (hb : Measurable b)
    {B : ℝ} (hB : ∀ k, ‖b k‖ ≤ B) :
    MemLp (fun k => (b k * s k) / (w k : ℂ)) 2 volume := by
  have hm : MemLp (fun k => b k * (s k / (w k : ℂ))) 2 volume :=
    hs.of_le_mul (c := B) (hb.aestronglyMeasurable.mul hs.aestronglyMeasurable)
      (Eventually.of_forall (fun k => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hB k) (norm_nonneg _)))
  have he : (fun k : GW.Space => (b k * s k) / (w k : ℂ)) =
      (fun k : GW.Space => b k * (s k / (w k : ℂ))) := by funext k; ring
  rw [he]
  exact hm

theorem weightedSourceCoordinate_factor (w : GW.Space → ℝ) (s b : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (w k : ℂ)) 2 volume)
    (hbs : MemLp (fun k => (b k * s k) / (w k : ℂ)) 2 volume)
    (hb : Measurable b) {B : ℝ} (hB : ∀ k, ‖b k‖ ≤ B) :
    weightedSourceCoordinate w (fun k => b k * s k) hbs =
      GW.Analysis.boundedMultiplier b hb (Eventually.of_forall hB) (weightedSourceCoordinate w s hs) := by
  apply Lp.ext
  filter_upwards [weightedSourceCoordinate_ae w (fun k => b k * s k) hbs,
    weightedSourceCoordinate_ae w s hs,
    GW.Analysis.boundedMultiplier_ae b hb (Eventually.of_forall hB) (weightedSourceCoordinate w s hs)]
      with k hnew hold hmul
  rw [hnew, ← hmul, hold]
  change (b k * s k) / (w k : ℂ) = b k * (s k / (w k : ℂ))
  ring

theorem weightedSource_factor_norm (w : GW.Space → ℝ) (s b : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (w k : ℂ)) 2 volume)
    (hbs : MemLp (fun k => (b k * s k) / (w k : ℂ)) 2 volume)
    (hb : Measurable b) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ k, ‖b k‖ ≤ B) :
    ‖weightedSourceLoad w (fun k => b k * s k) hbs‖ ≤ B * ‖weightedSourceLoad w s hs‖ := by
  rw [weightedSourceLoad_norm, weightedSourceLoad_norm, weightedSourceCoordinate_factor w s b hs hbs hb hB]
  let A : GW.OnePhonon →L[ℂ] GW.OnePhonon :=
    GW.Analysis.boundedMultiplier b hb (Eventually.of_forall hB)
  let q : GW.OnePhonon := weightedSourceCoordinate w s hs
  have hA : ‖A‖ ≤ B := GW.Analysis.boundedMultiplier_opNorm_le b hb hB0 (Eventually.of_forall hB)
  exact (A.le_opNorm q).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg q))

/-- The full Fock load uses the actual physical one-particle projection. -/
def fockWeightedSourceLoad (P : GW.Space) (s : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (oneParticleEnergyWeight P k : ℂ)) 2 volume) :
    ConjugateLoad (EnergySpace P) :=
  (weightedSourceLoad (oneParticleEnergyWeight P) s hs).comp (oneParticleEnergyProjection P)

/-- The isolated norm is an upper bound here, not an asserted equality with
the dual norm for the inherited Fock graph structure. -/
theorem fockWeightedSourceLoad_norm_le (P : GW.Space) (s : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (oneParticleEnergyWeight P k : ℂ)) 2 volume) :
    ‖fockWeightedSourceLoad P s hs‖ ≤ ‖weightedSourceLoad (oneParticleEnergyWeight P) s hs‖ := by
  let F : ConjugateLoad (OneParticleEnergySpace P) := weightedSourceLoad (oneParticleEnergyWeight P) s hs
  change ‖fockWeightedSourceLoad P s hs‖ ≤ ‖F‖
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
  intro x
  change ‖F (oneParticleEnergyProjection P x)‖ ≤ _
  exact (F.le_opNorm (oneParticleEnergyProjection P x)).trans
    (mul_le_mul_of_nonneg_left (oneParticleEnergyProjection_norm_le P x) (norm_nonneg F))

theorem fockWeightedSourceLoad_pairing_integrable (P : GW.Space) (s : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (oneParticleEnergyWeight P k : ℂ)) 2 volume)
    (x : EnergySpace P) :
    Integrable (fun k => (starRingEnd ℂ) (oneParticleExtraction (energyEmbedding P x) k) * s k) volume := by
  have h := weightedSource_pairing_integrable (oneParticleEnergyWeight P)
    (oneParticleEnergyWeight_measurable P) (oneParticleEnergyWeight_ge_one P) s hs
    (oneParticleEnergyProjection P x)
  change Integrable (fun k => (starRingEnd ℂ)
    (oneParticleEnergyEmbedding P (oneParticleEnergyProjection P x) k) * s k) volume at h
  rw [oneParticleEnergyProjection_intertwines] at h
  exact h

theorem fockWeightedSourceLoad_integral (P : GW.Space) (s : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (oneParticleEnergyWeight P k : ℂ)) 2 volume)
    (x : EnergySpace P) :
    fockWeightedSourceLoad P s hs x =
      ∫ k : GW.Space, (starRingEnd ℂ) (oneParticleExtraction (energyEmbedding P x) k) * s k := by
  change weightedSourceLoad (oneParticleEnergyWeight P) s hs (oneParticleEnergyProjection P x) = _
  rw [weightedSourceLoad_integral (oneParticleEnergyWeight P)
    (oneParticleEnergyWeight_measurable P) (oneParticleEnergyWeight_ge_one P)]
  change (∫ k : GW.Space, (starRingEnd ℂ)
    (oneParticleEnergyEmbedding P (oneParticleEnergyProjection P x) k) * s k) = _
  rw [oneParticleEnergyProjection_intertwines]

theorem fiberSource_quotient_norm_sq (g : ℝ) (P k : GW.Space) :
    ‖(fiberFormFactor g k : ℂ) / (oneParticleEnergyWeight P k : ℂ)‖ ^ 2 =
      g ^ 2 * shiftedSourceDensity (-P) k := by
  simp only [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [oneParticleEnergyWeight, Real.sq_sqrt (by positivity)]
  simp only [fiberFormFactor, div_pow, shiftedSourceDensity, sub_eq_add_neg,
    div_eq_mul_inv, mul_inv_rev]
  ring

theorem fiberSource_quotient_memLp (g : ℝ) (P : GW.Space) :
    MemLp (fun k => (fiberFormFactor g k : ℂ) / (oneParticleEnergyWeight P k : ℂ)) 2 volume := by
  have hm : Measurable (fun k : GW.Space => (fiberFormFactor g k : ℂ) /
      (oneParticleEnergyWeight P k : ℂ)) :=
    (Complex.continuous_ofReal.measurable.comp (fiberFormFactor_measurable g)).div
      (Complex.continuous_ofReal.measurable.comp (oneParticleEnergyWeight_measurable P))
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  obtain ⟨Cv, hCv, hsource⟩ := shiftedSourceDensity_uniform
  have hi := (hsource (-P)).1.const_mul (g ^ 2)
  have he : (fun k : GW.Space =>
      ‖(fiberFormFactor g k : ℂ) / (oneParticleEnergyWeight P k : ℂ)‖ ^ 2) =
        (fun k => g ^ 2 * shiftedSourceDensity (-P) k) := funext (fiberSource_quotient_norm_sq g P)
  rw [he]
  exact hi

def isolatedFiberSourceLoad (g : ℝ) (P : GW.Space) : ConjugateLoad (OneParticleEnergySpace P) :=
  weightedSourceLoad (oneParticleEnergyWeight P) (fun k => (fiberFormFactor g k : ℂ))
    (fiberSource_quotient_memLp g P)

def fiberSourceLoad (g : ℝ) (P : GW.Space) : ConjugateLoad (EnergySpace P) :=
  fockWeightedSourceLoad P (fun k => (fiberFormFactor g k : ℂ)) (fiberSource_quotient_memLp g P)

theorem fiberSourceCoordinate_norm_sq (g : ℝ) (P : GW.Space) :
    ‖weightedSourceCoordinate (oneParticleEnergyWeight P) (fun k => (fiberFormFactor g k : ℂ))
      (fiberSource_quotient_memLp g P)‖ ^ 2 =
        g ^ 2 * ∫ k : GW.Space, shiftedSourceDensity (-P) k := by
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  calc
    _ = ∫ k : GW.Space, g ^ 2 * shiftedSourceDensity (-P) k := by
      apply integral_congr_ae
      filter_upwards [weightedSourceCoordinate_ae (oneParticleEnergyWeight P)
        (fun k => (fiberFormFactor g k : ℂ)) (fiberSource_quotient_memLp g P)] with k hk
      rw [hk]
      exact fiberSource_quotient_norm_sq g P k
    _ = _ := integral_const_mul _ _

theorem fiberSourceLoad_integral (g : ℝ) (P : GW.Space) (x : EnergySpace P) :
    fiberSourceLoad g P x = ∫ k : GW.Space,
      (starRingEnd ℂ) (oneParticleExtraction (energyEmbedding P x) k) * (fiberFormFactor g k : ℂ) :=
  fockWeightedSourceLoad_integral P _ _ x

theorem fiberSourceLoads_uniform_bound : ∃ Cv : ℝ, 0 < Cv ∧ ∀ (g : ℝ) (P : GW.Space),
    ‖isolatedFiberSourceLoad g P‖ ^ 2 ≤ Cv * g ^ 2 ∧
      ‖fiberSourceLoad g P‖ ^ 2 ≤ Cv * g ^ 2 := by
  obtain ⟨Cv, hCv, hsource⟩ := shiftedSourceDensity_uniform
  refine ⟨Cv, hCv, fun g P => ?_⟩
  have hi : ‖isolatedFiberSourceLoad g P‖ ^ 2 ≤ Cv * g ^ 2 := by
    change ‖weightedSourceLoad (oneParticleEnergyWeight P) (fun k => (fiberFormFactor g k : ℂ))
      (fiberSource_quotient_memLp g P)‖ ^ 2 ≤ _
    rw [weightedSourceLoad_norm, fiberSourceCoordinate_norm_sq]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hsource (-P)).2 (sq_nonneg g)
  have hf : ‖fiberSourceLoad g P‖ ≤ ‖isolatedFiberSourceLoad g P‖ :=
    fockWeightedSourceLoad_norm_le P _ _
  exact ⟨hi, ((sq_le_sq₀ (norm_nonneg (fiberSourceLoad g P))
    (norm_nonneg (isolatedFiberSourceLoad g P))).mpr hf).trans hi⟩

theorem cutoffFiberSource_quotient_memLp (g Λ : ℝ) (P : GW.Space) :
    MemLp (fun k => (cutoffFormFactor g Λ k : ℂ) / (oneParticleEnergyWeight P k : ℂ)) 2 volume := by
  have hcut : Measurable (cutoffFormFactor g Λ) := by
    unfold cutoffFormFactor
    exact Measurable.ite (measurableSet_le measurable_norm measurable_const)
      (fiberFormFactor_measurable g) measurable_const
  have hm : Measurable (fun k : GW.Space => (cutoffFormFactor g Λ k : ℂ) /
      (oneParticleEnergyWeight P k : ℂ)) :=
    (Complex.continuous_ofReal.measurable.comp hcut).div
      (Complex.continuous_ofReal.measurable.comp (oneParticleEnergyWeight_measurable P))
  apply (fiberSource_quotient_memLp g P).of_le hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro k
  by_cases hk : ‖k‖ ≤ Λ
  · simp only [cutoffFormFactor, if_pos hk]
    exact le_refl _
  · simp only [cutoffFormFactor, if_neg hk, Complex.ofReal_zero, zero_div, norm_zero]
    exact norm_nonneg _

/-- The new cutoff coordinate is the reciprocal-weight image of the actual
retained closed-ball cutoff L² class, rather than another physical cutoff. -/
theorem cutoffFiberSourceCoordinate_eq_cutoffClass (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space) :
    weightedSourceCoordinate (oneParticleEnergyWeight P) (fun k => (cutoffFormFactor g Λ k : ℂ))
      (cutoffFiberSource_quotient_memLp g Λ P) =
        oneParticleEnergyEmbedding P
          (GW.Spaces.WeightedL2.coordinates.symm (cutoffFormFactorL2 g Λ hΛ)) := by
  apply Lp.ext
  have he := GW.Spaces.WeightedL2.embed_ae (oneParticleEnergyWeight_measurable P)
    (oneParticleEnergyWeight_ge_one P)
    (GW.Spaces.WeightedL2.coordinates.symm (cutoffFormFactorL2 g Λ hΛ))
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  filter_upwards [weightedSourceCoordinate_ae (oneParticleEnergyWeight P)
    (fun k => (cutoffFormFactor g Λ k : ℂ)) (cutoffFiberSource_quotient_memLp g Λ P),
    he, cutoffFormFactorL2_ae g Λ hΛ] with k hq he hc
  change (((oneParticleEnergyWeight P k)⁻¹ : ℝ) : ℂ) • cutoffFormFactorL2 g Λ hΛ k =
    oneParticleEnergyEmbedding P (GW.Spaces.WeightedL2.coordinates.symm (cutoffFormFactorL2 g Λ hΛ)) k at he
  rw [hq, ← he, hc]
  simp only [smul_eq_mul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

def isolatedCutoffFiberSourceLoad (g : ℝ) (P : GW.Space) (Λ : ℝ) :
    ConjugateLoad (OneParticleEnergySpace P) :=
  weightedSourceLoad (oneParticleEnergyWeight P) (fun k => (cutoffFormFactor g Λ k : ℂ))
    (cutoffFiberSource_quotient_memLp g Λ P)

def cutoffFiberSourceLoad (g : ℝ) (P : GW.Space) (Λ : ℝ) : ConjugateLoad (EnergySpace P) :=
  fockWeightedSourceLoad P (fun k => (cutoffFormFactor g Λ k : ℂ)) (cutoffFiberSource_quotient_memLp g Λ P)

theorem fockWeightedSourceLoad_norm_sub_le (P : GW.Space) (s t : GW.Space → ℂ)
    (hs : MemLp (fun k => s k / (oneParticleEnergyWeight P k : ℂ)) 2 volume)
    (ht : MemLp (fun k => t k / (oneParticleEnergyWeight P k : ℂ)) 2 volume) :
    ‖fockWeightedSourceLoad P s hs - fockWeightedSourceLoad P t ht‖ ≤
      ‖weightedSourceLoad (oneParticleEnergyWeight P) s hs - weightedSourceLoad (oneParticleEnergyWeight P) t ht‖ := by
  let F : ConjugateLoad (OneParticleEnergySpace P) :=
    weightedSourceLoad (oneParticleEnergyWeight P) s hs - weightedSourceLoad (oneParticleEnergyWeight P) t ht
  change ‖fockWeightedSourceLoad P s hs - fockWeightedSourceLoad P t ht‖ ≤ ‖F‖
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
  intro x
  change ‖F (oneParticleEnergyProjection P x)‖ ≤ _
  exact (F.le_opNorm (oneParticleEnergyProjection P x)).trans
    (mul_le_mul_of_nonneg_left (oneParticleEnergyProjection_norm_le P x) (norm_nonneg F))

theorem cutoffFiberSourceCoordinate_error_norm_sq (g Λ : ℝ) (P : GW.Space) :
    ‖weightedSourceCoordinate (oneParticleEnergyWeight P) (fun k => (cutoffFormFactor g Λ k : ℂ))
      (cutoffFiberSource_quotient_memLp g Λ P) -
      weightedSourceCoordinate (oneParticleEnergyWeight P) (fun k => (fiberFormFactor g k : ℂ))
        (fiberSource_quotient_memLp g P)‖ ^ 2 =
      g ^ 2 * ∫ k : GW.Space in {k | Λ < ‖k‖}, shiftedSourceDensity (-P) k := by
  rw [weightedSourceCoordinate, weightedSourceCoordinate, GW.Analysis.l2_class_sub_norm_sq (𝕜 := ℂ)]
  calc
    _ = ∫ k : GW.Space, {k | Λ < ‖k‖}.indicator (fun k => g ^ 2 * shiftedSourceDensity (-P) k) k := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro k
      change ‖(cutoffFormFactor g Λ k : ℂ) / (oneParticleEnergyWeight P k : ℂ) -
        (fiberFormFactor g k : ℂ) / (oneParticleEnergyWeight P k : ℂ)‖ ^ 2 =
          {q : GW.Space | Λ < ‖q‖}.indicator (fun q => g ^ 2 * shiftedSourceDensity (-P) q) k
      by_cases hk : ‖k‖ ≤ Λ
      · rw [cutoffFormFactor, if_pos hk, Set.indicator_of_notMem (not_lt_of_ge hk)]
        simp
      · rw [cutoffFormFactor, if_neg hk, Complex.ofReal_zero, zero_div, zero_sub, norm_neg,
          Set.indicator_of_mem (lt_of_not_ge hk)]
        exact fiberSource_quotient_norm_sq g P k
    _ = ∫ k : GW.Space in {k | Λ < ‖k‖}, g ^ 2 * shiftedSourceDensity (-P) k :=
      integral_indicator (measurableSet_lt measurable_const measurable_norm)
    _ = _ := integral_const_mul _ _

theorem isolatedCutoffFiberSourceLoad_error_sq (g R Λ : ℝ) (P : GW.Space)
    (hP : ‖P‖ ≤ R) (hΛ : max 1 (2 * R) ≤ Λ) :
    ‖isolatedCutoffFiberSourceLoad g P Λ - isolatedFiberSourceLoad g P‖ ^ 2 ≤
      56 * GW.Model.unitBallVolume * g ^ 2 / Λ := by
  change ‖weightedSourceLoad (oneParticleEnergyWeight P) (fun k => (cutoffFormFactor g Λ k : ℂ))
    (cutoffFiberSource_quotient_memLp g Λ P) -
    weightedSourceLoad (oneParticleEnergyWeight P) (fun k => (fiberFormFactor g k : ℂ))
    (fiberSource_quotient_memLp g P)‖ ^ 2 ≤ _
  rw [weightedSourceLoad_norm_sub, cutoffFiberSourceCoordinate_error_norm_sq]
  have ht := (shiftedSourceDensity_tail R (-P) (by simpa only [norm_neg] using hP) Λ hΛ).2
  calc
    _ ≤ g ^ 2 * (56 * GW.Model.unitBallVolume / Λ) := mul_le_mul_of_nonneg_left ht (sq_nonneg g)
    _ = _ := by ring

theorem cutoffFiberSourceLoad_error_sq (g R Λ : ℝ) (P : GW.Space)
    (hP : ‖P‖ ≤ R) (hΛ : max 1 (2 * R) ≤ Λ) :
    ‖cutoffFiberSourceLoad g P Λ - fiberSourceLoad g P‖ ^ 2 ≤
      56 * GW.Model.unitBallVolume * g ^ 2 / Λ := by
  have h : ‖cutoffFiberSourceLoad g P Λ - fiberSourceLoad g P‖ ≤
      ‖isolatedCutoffFiberSourceLoad g P Λ - isolatedFiberSourceLoad g P‖ :=
    fockWeightedSourceLoad_norm_sub_le P _ _ _ _
  exact ((sq_le_sq₀ (norm_nonneg (cutoffFiberSourceLoad g P Λ - fiberSourceLoad g P))
    (norm_nonneg (isolatedCutoffFiberSourceLoad g P Λ - isolatedFiberSourceLoad g P))).mpr h).trans
      (isolatedCutoffFiberSourceLoad_error_sq g R Λ P hP hΛ)

theorem cutoffFiberSourceLoad_error (g R Λ : ℝ) (P : GW.Space)
    (hP : ‖P‖ ≤ R) (hΛ : max 1 (2 * R) ≤ Λ) :
    ‖cutoffFiberSourceLoad g P Λ - fiberSourceLoad g P‖ ≤
      Real.sqrt (56 * GW.Model.unitBallVolume) * |g| / Real.sqrt Λ := by
  have h := Real.sqrt_le_sqrt (cutoffFiberSourceLoad_error_sq g R Λ P hP hΛ)
  have hc : 0 ≤ 56 * GW.Model.unitBallVolume := mul_nonneg (by norm_num) GW.Model.unitBallVolume_pos.le
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_div (mul_nonneg hc (sq_nonneg g)),
    Real.sqrt_mul hc, Real.sqrt_sq_eq_abs] using h

theorem isolatedCutoffFiberSourceLoad_tendsto (g : ℝ) (P : GW.Space) :
    Tendsto (isolatedCutoffFiberSourceLoad g P) atTop (𝓝 (isolatedFiberSourceLoad g P)) := by
  have hbound : ∀ᶠ Λ : ℝ in atTop,
      ‖isolatedCutoffFiberSourceLoad g P Λ - isolatedFiberSourceLoad g P‖ ^ 2 ≤
        (56 * GW.Model.unitBallVolume * g ^ 2) / Λ :=
    (eventually_ge_atTop (max 1 (2 * ‖P‖))).mono
      (fun Λ hΛ => isolatedCutoffFiberSourceLoad_error_sq g ‖P‖ Λ P le_rfl hΛ)
  have hlim : Tendsto (fun Λ : ℝ => (56 * GW.Model.unitBallVolume * g ^ 2) / Λ)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      ((tendsto_inv_atTop_zero : Tendsto (fun Λ : ℝ => Λ⁻¹) atTop (𝓝 0)).const_mul
        (56 * GW.Model.unitBallVolume * g ^ 2))
  have hsq := squeeze_zero' (Eventually.of_forall (fun Λ : ℝ =>
    sq_nonneg ‖isolatedCutoffFiberSourceLoad g P Λ - isolatedFiberSourceLoad g P‖)) hbound hlim
  have hn : Tendsto (fun Λ : ℝ => ‖isolatedCutoffFiberSourceLoad g P Λ - isolatedFiberSourceLoad g P‖)
      atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

theorem cutoffFiberSourceLoad_tendsto (g : ℝ) (P : GW.Space) :
    Tendsto (cutoffFiberSourceLoad g P) atTop (𝓝 (fiberSourceLoad g P)) := by
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp (isolatedCutoffFiberSourceLoad_tendsto g P)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun Λ : ℝ => norm_nonneg (cutoffFiberSourceLoad g P Λ - fiberSourceLoad g P)) _ hn
  intro Λ
  exact fockWeightedSourceLoad_norm_sub_le P _ _ _ _

theorem fiberSource_factor_memLp (g : ℝ) (P : GW.Space) (b : GW.Space → ℂ)
    (hb : Measurable b) {B : ℝ} (hB : ∀ k, ‖b k‖ ≤ B) :
    MemLp (fun k => (b k * (fiberFormFactor g k : ℂ)) / (oneParticleEnergyWeight P k : ℂ)) 2 volume :=
  weightedSource_factor_memLp (oneParticleEnergyWeight P) (fun k => (fiberFormFactor g k : ℂ)) b
    (fiberSource_quotient_memLp g P) hb hB

def fiberSourceFactorLoad (g : ℝ) (P : GW.Space) (b : GW.Space → ℂ)
    (hb : Measurable b) {B : ℝ} (hB : ∀ k, ‖b k‖ ≤ B) : ConjugateLoad (EnergySpace P) :=
  fockWeightedSourceLoad P (fun k => b k * (fiberFormFactor g k : ℂ))
    (fiberSource_factor_memLp g P b hb hB)

theorem fiberSourceFactorLoad_norm_le (g : ℝ) (P : GW.Space) (b : GW.Space → ℂ)
    (hb : Measurable b) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ k, ‖b k‖ ≤ B) :
    ‖fiberSourceFactorLoad g P b hb hB‖ ≤ B * ‖isolatedFiberSourceLoad g P‖ := by
  apply (fockWeightedSourceLoad_norm_le P (fun k => b k * (fiberFormFactor g k : ℂ))
    (fiberSource_factor_memLp g P b hb hB)).trans
  exact weightedSource_factor_norm (oneParticleEnergyWeight P) (fun k => (fiberFormFactor g k : ℂ)) b
    (fiberSource_quotient_memLp g P) (fiberSource_factor_memLp g P b hb hB) hb hB0 hB

end Froehlich
