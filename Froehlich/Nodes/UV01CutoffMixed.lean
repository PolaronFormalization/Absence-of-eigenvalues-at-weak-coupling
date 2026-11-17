import Froehlich.Nodes.FB02

/-! The same fixed mixed-field constant works for every actual cutoff.
This estimate chooses no cutoff-dependent reference energy. -/
noncomputable section
namespace Froehlich

theorem cutoffInteraction_diagonal_small (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space)
    (u : EnergySpace P) (hg1 : |g| ≤ 1) :
    ‖cutoffInteractionForm g Λ hΛ P u u‖ ≤ (max 1 lySmallConstant * |g|)*‖u‖^2 := by
  by_cases hg : g = 0
  · subst g
    rw [cutoffInteraction_zero_coupling]
    simp
  have hs : 0 < |g| := abs_pos.mpr hg
  have h := liebYamazaki_cutoff_small g Λ hΛ P u |g| hs le_rfl
  change ‖cutoffInteractionForm g Λ hΛ P u u‖ ≤ |g| * freeEnergy P (energyEmbedding P u) +
    (lySmallConstant*g^2/|g|)*‖energyEmbedding P u‖^2 at h
  have hr : lySmallConstant*g^2/|g| = lySmallConstant*|g| := by
    rw [← sq_abs g]
    field_simp [ne_of_gt hs]
    <;> ring
  rw [hr] at h
  have hE := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) lySmallConstant)
    (mul_nonneg (abs_nonneg g) (freeEnergy_nonneg P (energyEmbedding P u)))
  have hU := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) lySmallConstant)
    (mul_nonneg (abs_nonneg g) (sq_nonneg ‖energyEmbedding P u‖))
  have he : freeEnergy P (energyEmbedding P u) + ‖energyEmbedding P u‖^2 = ‖u‖^2 := by
    linarith [energyEmbedding_norm_identity P u]
  calc
    _ ≤ |g| * freeEnergy P (energyEmbedding P u) + lySmallConstant*|g| * ‖energyEmbedding P u‖^2 := h
    _ ≤ max 1 lySmallConstant*(|g| * freeEnergy P (energyEmbedding P u)) +
        max 1 lySmallConstant*(|g| * ‖energyEmbedding P u‖^2) := by
      simpa only [one_mul,mul_assoc] using add_le_add hE hU
    _ = (max 1 lySmallConstant*|g|)*(freeEnergy P (energyEmbedding P u)+‖energyEmbedding P u‖^2) := by ring
    _ = _ := by rw [he]

theorem cutoffInteraction_mixed_small (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space)
    (w u : EnergySpace P) (hg1 : |g| ≤ 1) :
    ‖cutoffInteractionForm g Λ hΛ P w u‖ ≤ phiMixedConstant * |g| * ‖w‖ * ‖u‖ := by
  have h := diagonal_to_mixed_bound (GW.Operators.boundedFormAlgebraic (cutoffInteractionForm g Λ hΛ P))
    (cutoffInteractionForm_hermitian g Λ hΛ P)
    (mul_nonneg (zero_le_one.trans (le_max_left _ _)) (abs_nonneg g))
    (fun x => cutoffInteraction_diagonal_small g Λ hΛ P x hg1) w u
  exact h.trans_eq (by unfold phiMixedConstant; ring)

end Froehlich
