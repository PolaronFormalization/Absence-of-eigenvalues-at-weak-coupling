import Froehlich.Nodes.EN02OneParticle
import Mathlib.MeasureTheory.Function.L2Space

/-! The full complex off-diagonal isolated free term on its actual weighted
one-particle domain. No coupling or energy-sign assumption is needed. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

private theorem weightedScalarInner_sub (a e t : ℝ) (ha : a^2=1+t) (x y : ℂ) :
    ⟪(a : ℂ)*x,(a : ℂ)*y⟫_ℂ - ((1+e : ℝ) : ℂ)*⟪x,y⟫_ℂ =
      ((t-e : ℝ) : ℂ)*(starRingEnd ℂ x)*y := by
  simp only [RCLike.inner_apply',map_mul,Complex.conj_ofReal]
  have hc : (a : ℂ)^2=((1+t : ℝ) : ℂ) := by exact_mod_cast ha
  calc
    _ = ((a : ℂ)^2-((1+e : ℝ) : ℂ))*(starRingEnd ℂ x)*y := by ring
    _ = _ := by rw [hc]; push_cast; ring

theorem oneParticle_threshold_free_integral (e : ℝ) (P : GW.Space)
    (f h : OneParticleEnergySpace P) :
    Integrable (fun k : GW.Space => ((‖k-P‖^2-e : ℝ) : ℂ) *
      (starRingEnd ℂ (oneParticleEnergyEmbedding P f k)) * oneParticleEnergyEmbedding P h k) volume ∧
    ⟪f,h⟫_ℂ - ((1+e : ℝ) : ℂ)*⟪oneParticleEnergyEmbedding P f,oneParticleEnergyEmbedding P h⟫_ℂ =
      ∫ k : GW.Space, ((‖k-P‖^2-e : ℝ) : ℂ) *
        (starRingEnd ℂ (oneParticleEnergyEmbedding P f k)) * oneParticleEnergyEmbedding P h k := by
  let F := oneParticleEnergyEmbedding P f
  let H := oneParticleEnergyEmbedding P h
  let fc : GW.OnePhonon := GW.Spaces.WeightedL2.coordinates f
  let hc : GW.OnePhonon := GW.Spaces.WeightedL2.coordinates h
  have hf := GW.Spaces.WeightedL2.weighted_embed_ae
    (oneParticleEnergyWeight_measurable P) (oneParticleEnergyWeight_ge_one P) f
  have hh := GW.Spaces.WeightedL2.weighted_embed_ae
    (oneParticleEnergyWeight_measurable P) (oneParticleEnergyWeight_ge_one P) h
  change (fun k => (oneParticleEnergyWeight P k : ℂ)*F k) =ᵐ[volume] fc at hf
  change (fun k => (oneParticleEnergyWeight P k : ℂ)*H k) =ᵐ[volume] hc at hh
  have hpoint : (fun k => ⟪fc k,hc k⟫_ℂ - ((1+e : ℝ) : ℂ)*⟪F k,H k⟫_ℂ) =ᵐ[volume]
      (fun k => ((‖k-P‖^2-e : ℝ) : ℂ)*(starRingEnd ℂ (F k))*H k) := by
    filter_upwards [hf,hh] with k hfk hhk
    rw [←hfk,←hhk]
    have hw : oneParticleEnergyWeight P k ^ 2 = 1+‖k-P‖^2 := by
      exact Real.sq_sqrt (by positivity)
    exact weightedScalarInner_sub (oneParticleEnergyWeight P k) e (‖k-P‖^2) hw (F k) (H k)
  have hci := L2.integrable_inner (𝕜 := ℂ) fc hc
  have hpi := L2.integrable_inner (𝕜 := ℂ) F H
  refine ⟨(hci.sub (hpi.const_mul ((1+e : ℝ) : ℂ))).congr hpoint,?_⟩
  have hpair : ⟪f,h⟫_ℂ = ⟪fc,hc⟫_ℂ :=
    (GW.Spaces.WeightedL2.coordinates.inner_map_map f h).symm
  rw [hpair,L2.inner_def,L2.inner_def,←integral_const_mul]
  exact (integral_sub hci (hpi.const_mul ((1+e : ℝ) : ℂ))).symm.trans (integral_congr_ae hpoint)

end Froehlich
