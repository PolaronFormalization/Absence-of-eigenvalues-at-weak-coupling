import Froehlich.Nodes.SE01RadialSource
import Froehlich.Nodes.TR01

/-! The actual radial map used in OP02, including at zero momentum.
Its boundedness comes from the existing graph coordinates. -/
noncomputable section
open MeasureTheory
namespace Froehlich

private def radialRatio (q : GW.Space) : ℂ :=
  ((‖q‖/oneParticleEnergyWeight 0 q : ℝ) : ℂ)

private theorem radialRatio_measurable : Measurable radialRatio :=
  Complex.continuous_ofReal.measurable.comp
    (measurable_norm.div (oneParticleEnergyWeight_measurable 0))

private theorem radialRatio_bound : ∀ᵐ q : GW.Space ∂volume, ‖radialRatio q‖ ≤ (1 : ℝ) := by
  apply Filter.Eventually.of_forall
  intro q
  have hw : 0 < oneParticleEnergyWeight 0 q :=
    lt_of_lt_of_le zero_lt_one (oneParticleEnergyWeight_ge_one 0 q)
  have hs : oneParticleEnergyWeight 0 q ^ 2 = 1+‖q‖^2 := by
    unfold oneParticleEnergyWeight
    rw [sub_zero,Real.sq_sqrt (by positivity)]
  have h : ‖q‖ ≤ oneParticleEnergyWeight 0 q := by nlinarith [norm_nonneg q]
  simpa only [radialRatio,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (norm_nonneg q) hw.le)] using (div_le_one hw).mpr h

def oneParticleRadialMap : OneParticleEnergySpace 0 →L[ℂ] GW.OnePhonon :=
  (GW.Analysis.boundedMultiplier radialRatio radialRatio_measurable radialRatio_bound).comp
    (isolatedEnergyCoordinates 0).toLinearIsometry.toContinuousLinearMap

theorem oneParticleRadialMap_norm_le : ‖oneParticleRadialMap‖ ≤ 1 := by
  have hm : ‖(GW.Analysis.boundedMultiplier radialRatio radialRatio_measurable
      radialRatio_bound : GW.OnePhonon →L[ℂ] GW.OnePhonon)‖ ≤ 1 :=
    GW.Analysis.boundedMultiplier_opNorm_le radialRatio radialRatio_measurable
      (by norm_num : (0 : ℝ) ≤ 1) radialRatio_bound
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  have h := (GW.Analysis.boundedMultiplier radialRatio radialRatio_measurable radialRatio_bound).le_opNorm
    (isolatedEnergyCoordinates 0 f)
  exact h.trans (by simpa only [LinearIsometryEquiv.norm_map,one_mul] using
    mul_le_mul_of_nonneg_right hm (norm_nonneg (isolatedEnergyCoordinates 0 f)))

theorem oneParticleRadialMap_ae (f : OneParticleEnergySpace 0) :
    oneParticleRadialMap f =ᵐ[volume]
      (fun q => (‖q‖ : ℂ)*oneParticleEnergyEmbedding 0 f q) := by
  have hm := GW.Analysis.boundedMultiplier_ae radialRatio radialRatio_measurable
    radialRatio_bound (isolatedEnergyCoordinates 0 f)
  have hf := GW.Spaces.WeightedL2.weighted_embed_ae
    (oneParticleEnergyWeight_measurable 0) (oneParticleEnergyWeight_ge_one 0) f
  filter_upwards [hm,hf] with q hm hf
  change (radialRatio q) • isolatedEnergyCoordinates 0 f q = oneParticleRadialMap f q at hm
  change (oneParticleEnergyWeight 0 q : ℂ)*oneParticleEnergyEmbedding 0 f q =
    isolatedEnergyCoordinates 0 f q at hf
  rw [←hm,←hf]
  have hw : (oneParticleEnergyWeight 0 q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one (oneParticleEnergyWeight_ge_one 0 q)))
  simp only [radialRatio,Complex.ofReal_div,smul_eq_mul]
  field_simp

theorem oneParticleRadialMap_ground (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) :
    oneParticleRadialMap (groundSourceOneEnergy e he g hg hs) =
      groundSourceRadialVector e he g hg hs := by
  apply Lp.ext
  exact (oneParticleRadialMap_ae _).trans (groundSourceRadialVector_ae e he g hg hs).symm

end Froehlich
