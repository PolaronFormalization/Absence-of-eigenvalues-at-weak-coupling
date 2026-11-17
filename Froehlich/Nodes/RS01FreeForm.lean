import Froehlich.Nodes.RS01FreeNorm
import Froehlich.Nodes.RS01Sandwich

/-! The literal normalized free form on the complete auxiliary domain.
The retained Hermitian polarization theorem transfers its exact diagonal. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)

include hn in
theorem auxiliaryFreeForm_normalization (w u : AuxiliaryEnergySpace n e p he.2) :
    freeFiberForm (-p) (auxiliaryToEnergy n e p he.2 w) (auxiliaryToEnergy n e p he.2 u) +
      ((1-(n : ℝ)-e : ℝ) : ℂ) *
        ⟪energyEmbedding (-p) (auxiliaryToEnergy n e p he.2 w),
          energyEmbedding (-p) (auxiliaryToEnergy n e p he.2 u)⟫_ℂ = ⟪w,u⟫_ℂ := by
  let L := auxiliaryToEnergy n e p he.2
  let J := (energyEmbedding (-p)).comp L
  let c : ℝ := (n : ℝ)+e
  let b : GW.Operators.AlgebraicForm (AuxiliaryEnergySpace n e p he.2) :=
    GW.Operators.embeddingForm L - (c : ℂ) • GW.Operators.embeddingForm J - innerₛₗ ℂ
  have hb : ∀ v z, b v z = star (b z v) := by
    intro v z
    change ⟪L v,L z⟫_ℂ - (c : ℂ)*⟪J v,J z⟫_ℂ - ⟪v,z⟫_ℂ =
      star (⟪L z,L v⟫_ℂ - (c : ℂ)*⟪J z,J v⟫_ℂ - ⟪z,v⟫_ℂ)
    simp only [star_sub,star_mul,Complex.star_def,Complex.conj_ofReal,inner_conj_symm]
    ring
  have hd : ∀ v, ‖b v v‖ ≤ (0 : ℝ)*‖v‖^2 := by
    intro v
    have ha := auxiliaryWeighted_norm_identity n e p hn he v
    have hx := energyEmbedding_norm_identity (-p) (L v)
    have hj : J v = auxiliaryFullEmbedding n e p he.2 (v : AuxiliaryFullEnergy n e p he.2) :=
      auxiliaryToEnergy_physical n e p hn he v
    change ‖L v‖^2 = ‖J v‖^2 + freeEnergy (-p) (J v) at hx
    rw [hj] at hx
    have hr : ‖L v‖^2 - c*‖J v‖^2 - ‖v‖^2 = 0 := by
      rw [hj]
      dsimp only [c]
      nlinarith
    have hc := congrArg Complex.ofReal hr
    simp only [Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_zero] at hc
    have hz : b v v = 0 := by
      change ⟪L v,L v⟫_ℂ - (c : ℂ)*⟪J v,J v⟫_ℂ - ⟪v,v⟫_ℂ = 0
      rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K]
      exact hc
    rw [hz,norm_zero,zero_mul]
  have hbound := GW.Operators.hermitian_mixed_bound b hb (show (0 : ℝ) ≤ 0 by norm_num) hd w u
  have hz : b w u = 0 := norm_eq_zero.mp
    (le_antisymm (by simpa only [zero_mul] using hbound) (norm_nonneg _))
  change ⟪L w,L u⟫_ℂ - (c : ℂ)*⟪J w,J u⟫_ℂ - ⟪w,u⟫_ℂ = 0 at hz
  rw [freeFiberForm_apply]
  change ⟪L w,L u⟫_ℂ - ⟪J w,J u⟫_ℂ + ((1-(n : ℝ)-e : ℝ) : ℂ)*⟪J w,J u⟫_ℂ = ⟪w,u⟫_ℂ
  dsimp only [c] at hz
  push_cast
  push_cast at hz
  linear_combination hz

include hn in
theorem auxiliaryEnergyLift_freeForm (w u : HighSectorSpace n) :
    freeFiberForm (-p) (auxiliaryEnergyLift n e p he.2 w) (auxiliaryEnergyLift n e p he.2 u) +
      ((1-(n : ℝ)-e : ℝ) : ℂ) *
        ⟪energyEmbedding (-p) (auxiliaryEnergyLift n e p he.2 w),
          energyEmbedding (-p) (auxiliaryEnergyLift n e p he.2 u)⟫_ℂ = ⟪w,u⟫_ℂ := by
  have h := auxiliaryFreeForm_normalization n e p hn he
    (auxiliaryFreeInverseEnergy n e p he.2 w) (auxiliaryFreeInverseEnergy n e p he.2 u)
  rw [LinearIsometryEquiv.inner_map_map] at h
  exact h

end Froehlich
