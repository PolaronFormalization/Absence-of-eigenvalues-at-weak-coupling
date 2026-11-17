import Froehlich.Nodes.UV01InverseBounds

/-! The source proof's actual add-and-subtract estimate in one fixed graph. -/
noncomputable section
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p0 p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem cutoffCommonSourceSolution_error (Λ : GW.Operators.PositiveCutoff) (hΛone : 1 ≤ Λ.val)
    (R S : ℝ) (hR : 0 ≤ R) (hdist : ‖p0-p‖ ≤ R)
    (hp : ‖p‖ ≤ S) (hΛ : max 1 (2*S) ≤ Λ.val) :
    ‖cutoffCommonSourceSolution n e p0 p hn he g hg hsmall Λ -
      singularCommonSourceSolution n e p0 p hn he g hg hsmall‖ ≤
      (12*(1+R^2))*((Real.sqrt (56*GW.Model.unitBallVolume)*|g|/Real.sqrt Λ.val)*
        momentumChangeConstant (-p) (-p0)) +
      (72*(1+R^2)*lyHighConstant*|g|/Real.sqrt Λ.val)*
        ‖singularCommonSourceLoad g p0 p n‖ := by
  let Q := cutoffCommonEnergyInverse n e p0 p hn he g hg hsmall Λ
  let T := singularCommonEnergyInverse n e p0 p hn he g hg hsmall
  let F := cutoffCommonSourceLoad g p0 p n Λ.val
  let H := singularCommonSourceLoad g p0 p n
  let z := loadRiesz F
  let w := loadRiesz H
  have hid : Q z - T w = Q (z-w) + (Q-T) w := by
    rw [Q.map_sub]
    change Q z - T w = (Q z-Q w)+(Q w-T w)
    abel
  have hz : ‖z-w‖ = ‖F-H‖ := by
    have hmap := (loadRieszLinearIsometry (V := HighEnergySpace (-p0) n)).map_sub F H
    change loadRiesz (F-H) = z-w at hmap
    rw [← hmap]
    exact loadRiesz_norm (F-H)
  change ‖Q z-T w‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖Q (z-w)‖ + ‖(Q-T) w‖ := norm_add_le _ _
    _ ≤ ‖Q‖*‖z-w‖ + ‖Q-T‖*‖w‖ := add_le_add (Q.le_opNorm _) ((Q-T).le_opNorm _)
    _ = ‖Q‖*‖F-H‖ + ‖Q-T‖*‖H‖ := by rw [hz,loadRiesz_norm]
    _ ≤ _ := add_le_add
      (mul_le_mul (cutoffCommonEnergyInverse_norm_le n e p hn he g hg hsmall p0 Λ R hR hdist)
        (cutoffCommonSourceLoad_error g S Λ.val p0 p n hp hΛ) (norm_nonneg _) (by positivity))
      (mul_le_mul_of_nonneg_right
        (cutoffCommonEnergyInverse_error n e p0 p hn he g hg hsmall Λ hΛone R hR hdist) (norm_nonneg H))

end Froehlich
