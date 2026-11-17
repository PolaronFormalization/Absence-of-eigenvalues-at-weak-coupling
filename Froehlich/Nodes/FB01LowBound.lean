import Froehlich.Nodes.FB01Forms

/-! The low-frequency Lieb--Yamazaki bound on the actual common form domain. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem smearedField_diagonal_bound (f : GW.OnePhonon) (u : NumberFormSpace) :
    ‖⟪numberFormEmbedding u,fieldRestriction f u⟫_ℂ‖ ≤
      2 * ‖f‖ * ‖numberFormEmbedding u‖ *
        ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput u)‖ := by
  have hc : ‖⟪numberFormEmbedding u,creationRestriction f u⟫_ℂ‖ =
      ‖⟪numberFormEmbedding u,annihilationRestriction f u⟫_ℂ‖ := by
    rw [norm_inner_symm, smeared_adjoint_pairing]
  have ha : ‖⟪numberFormEmbedding u,annihilationRestriction f u⟫_ℂ‖ ≤
      ‖numberFormEmbedding u‖ * ‖annihilationRestriction f u‖ :=
    norm_inner_le_norm (numberFormEmbedding u) (annihilationRestriction f u)
  have hb := smeared_operator_annihilation_bound f u
  change ‖⟪numberFormEmbedding u,annihilationRestriction f u + creationRestriction f u⟫_ℂ‖ ≤ _
  rw [inner_add_right]
  calc
    _ ≤ ‖⟪numberFormEmbedding u,annihilationRestriction f u⟫_ℂ‖ +
        ‖⟪numberFormEmbedding u,creationRestriction f u⟫_ℂ‖ := norm_add_le _ _
    _ ≤ 2 * (‖numberFormEmbedding u‖ * (‖f‖ *
        ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput u)‖)) := by
      rw [hc]
      have h := ha.trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
      linarith
    _ = _ := by ring

theorem boundedEnergyInteraction_diagonal_bound (P : GW.Space) (f : GW.OnePhonon) (u : EnergySpace P) :
    ‖boundedEnergyInteraction P f u u‖ ≤ 2 * ‖f‖ * ‖energyEmbedding P u‖ *
      ‖GW.Fock.numberPower GW.Fock.Sector (1/2)
        (numberFormRootInput (energyNumberCoordinates P u))‖ := by
  have h := smearedField_diagonal_bound f (energyNumberCoordinates P u)
  rw [energyNumberCoordinates_intertwines] at h
  exact h

theorem boundedEnergyInteraction_young (P : GW.Space) (f : GW.OnePhonon)
    (u : EnergySpace P) (theta : ℝ) (htheta : 0 < theta) :
    ‖boundedEnergyInteraction P f u u‖ ≤
      theta / 2 * ‖GW.Fock.numberPower GW.Fock.Sector (1/2)
        (numberFormRootInput (energyNumberCoordinates P u))‖ ^ 2 +
          (2 / theta) * ‖f‖ ^ 2 * ‖energyEmbedding P u‖ ^ 2 := by
  have hy := two_mul_le_add_mul_sq
    (a := ‖GW.Fock.numberPower GW.Fock.Sector (1/2)
      (numberFormRootInput (energyNumberCoordinates P u))‖)
    (b := ‖f‖ * ‖energyEmbedding P u‖) (show 0 < theta/2 by positivity)
  apply (boundedEnergyInteraction_diagonal_bound P f u).trans
  convert hy using 1 <;> field_simp [ne_of_gt htheta] <;> ring

theorem cutoffInteraction_low_bound (g R : ℝ) (hR : 0 < R) (P : GW.Space)
    (u : EnergySpace P) (theta : ℝ) (htheta : 0 < theta) :
    ‖cutoffInteractionForm g R hR P u u‖ ≤
      theta / 2 * ‖GW.Fock.numberPower GW.Fock.Sector (1/2)
        (numberFormRootInput (energyNumberCoordinates P u))‖ ^ 2 +
          (14 * GW.Model.unitBallVolume * g^2 * R / theta) * ‖energyEmbedding P u‖ ^ 2 := by
  have h := boundedEnergyInteraction_young P (cutoffFormFactorL2 g R hR) u theta htheta
  change ‖cutoffInteractionForm g R hR P u u‖ ≤ _ at h
  apply h.trans
  apply add_le_add (le_refl _) 
  have hb := mul_le_mul_of_nonneg_left (cutoffFormFactorL2_norm_sq g R hR)
    (show 0 ≤ 2/theta by positivity)
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖energyEmbedding P u‖)
  convert hm using 1 <;> ring

end Froehlich
