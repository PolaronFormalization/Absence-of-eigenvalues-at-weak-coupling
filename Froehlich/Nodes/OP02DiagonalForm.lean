import Froehlich.Nodes.OP02RadialMap
import Froehlich.Nodes.OP01DiagonalOperator

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

theorem thresholdDiagonalMultiplier_radial_square (q : GW.Space) (hq : q ≠ 0) :
    thresholdDiagonalMultiplier e he g hg hs q*‖q‖^2 = ‖q‖^2+auxiliarySelfEnergy e q he g hg hs-e := by
  have hn : ‖q‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hq)
  rw [thresholdDiagonalMultiplier,if_neg hq,add_mul,one_mul,div_mul_cancel₀ _ hn]
  ring

private theorem op02_diagonal_scalar (q : GW.Space) (hq : q ≠ 0) (z w : ℂ) :
    (starRingEnd ℂ) ((‖q‖ : ℂ)*z)*
        ((thresholdDiagonalMultiplier e he g hg hs q : ℂ)*((‖q‖ : ℂ)*w)) =
      (starRingEnd ℂ) z*((‖q‖^2+auxiliarySelfEnergy e q he g hg hs-e : ℝ) : ℂ)*w := by
  calc
    _ = (starRingEnd ℂ) z*
        ((thresholdDiagonalMultiplier e he g hg hs q*‖q‖^2 : ℝ) : ℂ)*w := by
      simp only [map_mul,Complex.conj_ofReal,Complex.ofReal_mul,Complex.ofReal_pow]
      ring
    _ = _ := by rw [thresholdDiagonalMultiplier_radial_square e he g hg hs q hq]

variable (C : ℝ) (hC : 0 ≤ C)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ C*g^2*‖q‖^2)

theorem radialDiagonal_inner_integral (f h : OneParticleEnergySpace 0) :
    Integrable (fun q : GW.Space => (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q)*
      ((‖q‖^2+auxiliarySelfEnergy e q he g hg hs-e : ℝ) : ℂ)*oneParticleEnergyEmbedding 0 h q) volume ∧
    ⟪oneParticleRadialMap f,thresholdDiagonalOperator e he g hg hs C hC hquad (oneParticleRadialMap h)⟫_ℂ =
      ∫ q : GW.Space, (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q)*
        ((‖q‖^2+auxiliarySelfEnergy e q he g hg hs-e : ℝ) : ℂ)*oneParticleEnergyEmbedding 0 h q := by
  let D := thresholdDiagonalOperator e he g hg hs C hC hquad
  have hi := L2.integrable_inner (𝕜 := ℂ) (oneParticleRadialMap f) (D (oneParticleRadialMap h))
  have hp : (fun q : GW.Space => ⟪oneParticleRadialMap f q,D (oneParticleRadialMap h) q⟫_ℂ) =ᵐ[volume]
      (fun q : GW.Space => (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q)*
        ((‖q‖^2+auxiliarySelfEnergy e q he g hg hs-e : ℝ) : ℂ)*oneParticleEnergyEmbedding 0 h q) := by
    filter_upwards [oneParticleRadialMap_ae f,oneParticleRadialMap_ae h,
      thresholdDiagonalOperator_ae e he g hg hs C hC hquad (oneParticleRadialMap h),
      (volume : Measure GW.Space).ae_ne 0] with q hf hh hd hq
    rw [hf,hd,hh,RCLike.inner_apply']
    exact op02_diagonal_scalar e he g hg hs q hq
      (oneParticleEnergyEmbedding 0 f q) (oneParticleEnergyEmbedding 0 h q)
  refine ⟨hi.congr hp,?_⟩
  rw [L2.inner_def]
  exact integral_congr_ae hp

end Froehlich
