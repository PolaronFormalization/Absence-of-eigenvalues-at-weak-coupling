import Froehlich.Nodes.SE01SourceProjection

/-! u₀(k)=|k|f₀(k) is a genuine L² vector, obtained from the existing
isolated energy norm; no extra one-particle domain assumption is imposed. -/
noncomputable section
open MeasureTheory
namespace Froehlich

theorem oneParticleRadial_memLp (f : OneParticleEnergySpace 0) :
    MemLp (fun k : GW.Space => (‖k‖ : ℂ)*oneParticleEnergyEmbedding 0 f k) 2 volume := by
  let fc : GW.OnePhonon := GW.Spaces.WeightedL2.coordinates f
  have hm : AEStronglyMeasurable
      (fun k : GW.Space => (‖k‖ : ℂ)*oneParticleEnergyEmbedding 0 f k) volume :=
    (Complex.continuous_ofReal.comp continuous_norm).measurable.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable (oneParticleEnergyEmbedding 0 f))
  apply (Lp.memLp fc).mono hm
  have hf := GW.Spaces.WeightedL2.weighted_embed_ae
    (oneParticleEnergyWeight_measurable 0) (oneParticleEnergyWeight_ge_one 0) f
  filter_upwards [hf] with k hk
  change (oneParticleEnergyWeight 0 k : ℂ)*oneParticleEnergyEmbedding 0 f k = fc k at hk
  rw [←hk]
  have hW0 : 0 ≤ oneParticleEnergyWeight 0 k := zero_le_one.trans (oneParticleEnergyWeight_ge_one 0 k)
  have hWsq : oneParticleEnergyWeight 0 k ^ 2 = 1+‖k‖^2 := by
    unfold oneParticleEnergyWeight
    rw [sub_zero,Real.sq_sqrt (by positivity)]
  have hW : ‖k‖ ≤ oneParticleEnergyWeight 0 k := by nlinarith [norm_nonneg k]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_norm,abs_of_nonneg hW0]
  exact mul_le_mul_of_nonneg_right hW (norm_nonneg _)

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

def groundSourceRadialVector : GW.OnePhonon :=
  (oneParticleRadial_memLp (groundSourceOneEnergy e he g hg hs)).toLp
    (fun k => (‖k‖ : ℂ)*oneParticleEnergyEmbedding 0 (groundSourceOneEnergy e he g hg hs) k)

theorem groundSourceRadialVector_ae :
    groundSourceRadialVector e he g hg hs =ᵐ[volume]
      (fun k => (‖k‖ : ℂ)*oneParticleEnergyEmbedding 0 (groundSourceOneEnergy e he g hg hs) k) :=
  (oneParticleRadial_memLp (groundSourceOneEnergy e he g hg hs)).coeFn_toLp

end Froehlich
