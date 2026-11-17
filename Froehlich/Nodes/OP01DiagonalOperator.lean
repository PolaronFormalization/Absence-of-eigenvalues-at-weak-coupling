import Froehlich.Nodes.OP01Multiplier

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)
  (C : ℝ) (hC : 0 ≤ C)
  (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ C*g^2*‖q‖^2)

private theorem multiplierError_measurable :
    Measurable (fun q : GW.Space => ((thresholdDiagonalMultiplier e he g hg hs q-1 : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.measurable.comp
    ((thresholdDiagonalMultiplier_measurable e he g hg hs).sub measurable_const)

include hC hquad in
private theorem multiplierError_bound :
    ∀ᵐ q : GW.Space ∂volume,
      ‖((thresholdDiagonalMultiplier e he g hg hs q-1 : ℝ) : ℂ)‖ ≤ C*g^2 := by
  exact Filter.Eventually.of_forall (fun q => by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using
      thresholdDiagonalMultiplier_sub_one_bound e he g hg hs C hC hquad q)

/-- The actual bounded multiplication operator. The perturbation presentation
keeps its quantitative distance from the identity explicit. -/
def thresholdDiagonalOperator : GW.OnePhonon →L[ℂ] GW.OnePhonon :=
  ContinuousLinearMap.id ℂ GW.OnePhonon +
    GW.Analysis.boundedMultiplier (fun q : GW.Space =>
      ((thresholdDiagonalMultiplier e he g hg hs q-1 : ℝ) : ℂ))
      (multiplierError_measurable e he g hg hs) (multiplierError_bound e he g hg hs C hC hquad)

theorem thresholdDiagonalOperator_sub_id_norm :
    ‖thresholdDiagonalOperator e he g hg hs C hC hquad-ContinuousLinearMap.id ℂ GW.OnePhonon‖ ≤ C*g^2 := by
  unfold thresholdDiagonalOperator
  rw [add_sub_cancel_left]
  exact GW.Analysis.boundedMultiplier_opNorm_le _ _ (mul_nonneg hC (sq_nonneg g)) _

theorem thresholdDiagonalOperator_ae (f : GW.OnePhonon) :
    thresholdDiagonalOperator e he g hg hs C hC hquad f =ᵐ[volume]
      (fun q => (thresholdDiagonalMultiplier e he g hg hs q : ℂ)*f q) := by
  let E : GW.OnePhonon →L[ℂ] GW.OnePhonon := GW.Analysis.boundedMultiplier
    (fun q : GW.Space => ((thresholdDiagonalMultiplier e he g hg hs q-1 : ℝ) : ℂ))
    (multiplierError_measurable e he g hg hs) (multiplierError_bound e he g hg hs C hC hquad)
  have hE := GW.Analysis.boundedMultiplier_ae
    (fun q : GW.Space => ((thresholdDiagonalMultiplier e he g hg hs q-1 : ℝ) : ℂ))
    (multiplierError_measurable e he g hg hs) (multiplierError_bound e he g hg hs C hC hquad) f
  change f+E f =ᵐ[volume] (fun q => (thresholdDiagonalMultiplier e he g hg hs q : ℂ)*f q)
  filter_upwards [Lp.coeFn_add f (E f),hE] with q hadd herror
  change ((thresholdDiagonalMultiplier e he g hg hs q-1 : ℝ) : ℂ) • f q = E f q at herror
  rw [hadd]
  change f q+E f q = (thresholdDiagonalMultiplier e he g hg hs q : ℂ)*f q
  rw [←herror]
  simp only [smul_eq_mul,Complex.ofReal_sub,Complex.ofReal_one]
  ring

end Froehlich
