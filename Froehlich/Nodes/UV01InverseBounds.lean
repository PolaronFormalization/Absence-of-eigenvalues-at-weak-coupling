import Froehlich.Nodes.UV01CommonSourceSolutions

/-! Uniform bounds for the actual inverse maps from energy dual to energy.
These concern the original graph and its fixed reference coordinates. -/
noncomputable section
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem cutoffAuxiliaryEnergyInverse_norm_le (Λ : GW.Operators.PositiveCutoff) :
    ‖cutoffAuxiliaryEnergyInverse n e p hn he g hg hsmall Λ‖ ≤ 6 := by
  let L := (auxiliaryEnergyLiftEquivalence n e p hn he).toContinuousLinearMap
  let Q := cutoffAuxiliaryNormalizedInverse g Λ.val Λ.property n e p he.2 hg hsmall
  have hL : ‖L‖ ≤ Real.sqrt 3 := auxiliaryEnergyLiftEquivalence_opNorm_le n e p hn he
  have hLa : ‖L.adjoint‖ ≤ Real.sqrt 3 := (ContinuousLinearMap.adjoint.norm_map L).trans_le hL
  have hQ : ‖Q‖ ≤ 2 := cutoffAuxiliaryNormalizedInverse_norm_le g Λ.val Λ.property n e p he.2 hg hsmall
  change ‖L.comp (Q.comp L.adjoint)‖ ≤ _
  calc
    _ ≤ ‖L‖ * ‖Q.comp L.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖L‖ * (‖Q‖*‖L.adjoint‖) := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg L)
    _ ≤ Real.sqrt 3 * (2*Real.sqrt 3) := mul_le_mul hL
      (mul_le_mul hQ hLa (norm_nonneg _) (by norm_num))
      (mul_nonneg (ContinuousLinearMap.opNorm_nonneg Q) (ContinuousLinearMap.opNorm_nonneg L.adjoint)) (Real.sqrt_nonneg _)
    _ = 6 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem cutoffCommonEnergyInverse_norm_le (p0 : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (R : ℝ) (hR : 0 ≤ R) (hdist : ‖p0-p‖ ≤ R) :
    ‖cutoffCommonEnergyInverse n e p0 p hn he g hg hsmall Λ‖ ≤ 12*(1+R^2) := by
  let B := highEnergyCoordinateChange (-p0) (-p) n
  let Q := cutoffAuxiliaryEnergyInverse n e p hn he g hg hsmall Λ
  have hp : ‖B‖*‖B.adjoint‖ ≤ 2*(1+R^2) := by
    rw [ContinuousLinearMap.adjoint.norm_map B,← pow_two]
    exact highEnergyCoordinateChange_norm_sq p0 p n R hR hdist
  change ‖B.comp (Q.comp B.adjoint)‖ ≤ _
  calc
    _ ≤ ‖B‖ * ‖Q.comp B.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖B‖ * (‖Q‖*‖B.adjoint‖) := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg B)
    _ = (‖B‖*‖B.adjoint‖)*‖Q‖ := by ring
    _ ≤ (2*(1+R^2))*‖Q‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg Q)
    _ ≤ (2*(1+R^2))*6 := mul_le_mul_of_nonneg_left
      (cutoffAuxiliaryEnergyInverse_norm_le n e p hn he g hg hsmall Λ) (by positivity)
    _ = _ := by ring

end Froehlich
