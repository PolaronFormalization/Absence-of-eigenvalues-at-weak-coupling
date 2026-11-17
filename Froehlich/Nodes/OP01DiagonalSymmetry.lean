import Froehlich.Nodes.OP01DiagonalOperator
import Froehlich.Nodes.SY01Annihilation

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)
  (C : ℝ) (hC : 0 ≤ C)
  (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ C*g^2*‖q‖^2)

/-- The bounded diagonal operator inherits the same real-multiplier pairing
calculation as GW.Analysis.realMultiplier_symmetric. -/
theorem thresholdDiagonalOperator_selfadjoint :
    (thresholdDiagonalOperator e he g hg hs C hC hquad).adjoint =
      thresholdDiagonalOperator e he g hg hs C hC hquad := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f h
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [thresholdDiagonalOperator_ae e he g hg hs C hC hquad f,
    thresholdDiagonalOperator_ae e he g hg hs C hC hquad h] with q hf hh
  rw [hf,hh]
  change ⟪(thresholdDiagonalMultiplier e he g hg hs q : ℂ) • f q,h q⟫_ℂ =
    ⟪f q,(thresholdDiagonalMultiplier e he g hg hs q : ℂ) • h q⟫_ℂ
  rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal]

theorem thresholdDiagonalOperator_conjugation (f : GW.OnePhonon) :
    thresholdDiagonalOperator e he g hg hs C hC hquad (conjugateOnePhonon f) =
      conjugateOnePhonon (thresholdDiagonalOperator e he g hg hs C hC hquad f) := by
  apply Lp.ext
  filter_upwards [thresholdDiagonalOperator_ae e he g hg hs C hC hquad (conjugateOnePhonon f),
    thresholdDiagonalOperator_ae e he g hg hs C hC hquad f,
    conjugateOnePhonon_ae f,
    conjugateOnePhonon_ae (thresholdDiagonalOperator e he g hg hs C hC hquad f)] with q hc hf hconj hresult
  rw [hc,hresult,hf,hconj,map_mul,Complex.conj_ofReal]

end Froehlich
