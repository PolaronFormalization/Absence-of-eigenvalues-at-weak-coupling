import Froehlich.Nodes.OP02RadialMap

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Froehlich
open scoped Classical

/-- The manuscript's annulus, with a real radius at least one. -/
def se03Annulus (M : ℝ) : Set GW.Space := {q | M⁻¹ ≤ ‖q‖ ∧ ‖q‖ ≤ M}

private def se03AnnularRatio (M : ℝ) (q : GW.Space) : ℂ :=
  if q ∈ se03Annulus M then ((oneParticleEnergyWeight 0 q/‖q‖ : ℝ) : ℂ) else 0

private theorem se03AnnularRatio_measurable (M : ℝ) : Measurable (se03AnnularRatio M) := by
  have hA : MeasurableSet (se03Annulus M) :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  exact Measurable.ite hA (Complex.continuous_ofReal.measurable.comp
    ((oneParticleEnergyWeight_measurable 0).div measurable_norm)) measurable_const

private theorem se03AnnularRatio_bound (M : ℝ) (hM : 1 ≤ M) :
    ∀ᵐ q : GW.Space ∂volume, ‖se03AnnularRatio M q‖ ≤ (1+M)*M := by
  apply Filter.Eventually.of_forall
  intro q
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  by_cases hq : q ∈ se03Annulus M
  · have hqp : 0 < ‖q‖ := lt_of_lt_of_le (inv_pos.mpr hMp) hq.1
    have hw : oneParticleEnergyWeight 0 q ≤ 1+M := by
      have hs : oneParticleEnergyWeight 0 q ^ 2 = 1+‖q‖^2 := by
        unfold oneParticleEnergyWeight
        rw [sub_zero,Real.sq_sqrt (by positivity)]
      have hn := oneParticleEnergyWeight_ge_one 0 q
      nlinarith [hq.2,norm_nonneg q]
    have hinv : ‖q‖⁻¹ ≤ M := (inv_le_comm₀ hqp hMp).mpr hq.1
    have hw0 : 0 ≤ oneParticleEnergyWeight 0 q :=
      le_trans zero_le_one (oneParticleEnergyWeight_ge_one 0 q)
    have hratio : 0 ≤ oneParticleEnergyWeight 0 q/‖q‖ := div_nonneg hw0 hqp.le
    calc
      ‖se03AnnularRatio M q‖ = oneParticleEnergyWeight 0 q/‖q‖ := by
        simp only [se03AnnularRatio,if_pos hq,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg hratio]
      _ ≤ (1+M)*M := by
        rw [div_eq_mul_inv]
        exact mul_le_mul hw hinv (inv_nonneg.mpr hqp.le) (by linarith)
  · simp only [se03AnnularRatio,if_neg hq,norm_zero]
    positivity

/-- An actual Q1 test obtained by dividing an annular L2 input by its radius. -/
def se03AnnularTest (M : ℝ) (hM : 1 ≤ M) (z : GW.OnePhonon) : OneParticleEnergySpace 0 :=
  (isolatedEnergyCoordinates 0).symm
    (GW.Analysis.boundedMultiplier (se03AnnularRatio M) (se03AnnularRatio_measurable M)
      (se03AnnularRatio_bound M hM) z)

theorem se03AnnularTest_radial (M : ℝ) (hM : 1 ≤ M) (z : GW.OnePhonon)
    (hz : ∀ᵐ q ∂volume, q ∉ se03Annulus M → z q = 0) :
    oneParticleRadialMap (se03AnnularTest M hM z) = z := by
  let f := se03AnnularTest M hM z
  have hf := GW.Spaces.WeightedL2.weighted_embed_ae
    (oneParticleEnergyWeight_measurable 0) (oneParticleEnergyWeight_ge_one 0) f
  have hm := GW.Analysis.boundedMultiplier_ae (se03AnnularRatio M)
    (se03AnnularRatio_measurable M) (se03AnnularRatio_bound M hM) z
  have hr := oneParticleRadialMap_ae f
  apply Lp.ext
  filter_upwards [hf,hm,hr,hz] with q hf hm hr hz
  change (oneParticleEnergyWeight 0 q : ℂ)*oneParticleEnergyEmbedding 0 f q =
    isolatedEnergyCoordinates 0 f q at hf
  have hcoord : isolatedEnergyCoordinates 0 f =
      GW.Analysis.boundedMultiplier (se03AnnularRatio M) (se03AnnularRatio_measurable M)
        (se03AnnularRatio_bound M hM) z := (isolatedEnergyCoordinates 0).apply_symm_apply _
  rw [hcoord,←hm] at hf
  rw [hr]
  by_cases hq : q ∈ se03Annulus M
  · have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
    have hqp : 0 < ‖q‖ := lt_of_lt_of_le (inv_pos.mpr hMp) hq.1
    have hw : (oneParticleEnergyWeight 0 q : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one (oneParticleEnergyWeight_ge_one 0 q)))
    simp only [se03AnnularRatio,if_pos hq,smul_eq_mul,Complex.ofReal_div] at hf
    have hn : (‖q‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqp.ne'
    apply mul_left_cancel₀ hw
    calc
      (oneParticleEnergyWeight 0 q : ℂ)*((‖q‖ : ℂ)*oneParticleEnergyEmbedding 0 f q) =
          (‖q‖ : ℂ)*((oneParticleEnergyWeight 0 q : ℂ)*oneParticleEnergyEmbedding 0 f q) := by ring
      _ = (‖q‖ : ℂ)*(((oneParticleEnergyWeight 0 q : ℂ)/(‖q‖ : ℂ))*z q) := by rw [hf]
      _ = (oneParticleEnergyWeight 0 q : ℂ)*z q := by field_simp
  · have hz0 := hz hq
    simp only [se03AnnularRatio,if_neg hq,zero_smul] at hf
    have hw : (oneParticleEnergyWeight 0 q : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one (oneParticleEnergyWeight_ge_one 0 q)))
    have hf0 := (mul_eq_zero.mp hf).resolve_left hw
    rw [hf0,hz0,mul_zero]

end Froehlich
