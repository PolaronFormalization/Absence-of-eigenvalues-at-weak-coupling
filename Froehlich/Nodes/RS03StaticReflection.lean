import Froehlich.Nodes.RS02SourceEnergy
import Froehlich.Nodes.SY01SourceLoads

set_option autoImplicit false

/-! True reflection of the actual auxiliary source solution and evenness
of the canonical self-energy, using full energy weak uniqueness. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (e : ℝ) (p : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2)

theorem rs03GroundSourceEnergy_unique (u : HighEnergySpace (-p) 1)
    (hu : ∀ w : HighEnergySpace (-p) 1,
      (fiberFormData g (-p) none).form (w : EnergySpace (-p)) (u : EnergySpace (-p))-
      (e : ℂ)*⟪energyEmbedding (-p) (w : EnergySpace (-p)),energyEmbedding (-p) (u : EnergySpace (-p))⟫_ℂ =
        highFiberSourceLoad g (-p) 1 w) :
    u = auxiliaryGroundSourceEnergy e p he g hg hsmall := by
  let T := auxiliaryCompressedEnergyOperator 1 e p (by norm_num) he g
  let Q := auxiliaryCompressedEnergyInverse 1 e p (by norm_num) he g hg hsmall
  have hleft : Function.LeftInverse Q T := by
    intro x
    have h := congrArg (fun A : HighEnergySpace (-p) 1 →L[ℂ] HighEnergySpace (-p) 1 => A x)
      (auxiliaryCompressedEnergyInverse_left 1 e p (by norm_num) he g hg hsmall)
    change Q (T x) = x at h
    exact h
  have hspec (w v : HighEnergySpace (-p) 1) : ⟪w,T v⟫_ℂ =
      (fiberFormData g (-p) none).form (w : EnergySpace (-p)) (v : EnergySpace (-p))-
      (e : ℂ)*⟪energyEmbedding (-p) (w : EnergySpace (-p)),energyEmbedding (-p) (v : EnergySpace (-p))⟫_ℂ := by
    have h := auxiliaryCompressedEnergyOperator_spec 1 e p (by norm_num) he g w v
    simp only [Nat.cast_one,sub_add_cancel] at h
    exact h
  apply hleft.injective
  apply ext_inner_left ℂ
  intro w
  rw [hspec w u,hspec w (auxiliaryGroundSourceEnergy e p he g hg hsmall),hu w,
    auxiliaryGroundSourceEnergy_weak e p he g hg hsmall w]

theorem auxiliaryGroundSourceEnergy_reflection :
    highEnergyReflection (-p) 1 (auxiliaryGroundSourceEnergy e p he g hg hsmall) =
      auxiliaryGroundSourceEnergy e (-p) he g hg hsmall := by
  apply rs03GroundSourceEnergy_unique e (-p) he g hg hsmall
  have hx (w : HighEnergySpace (-p) 1) :
      (compressedFiberFormData g (-p) 1 none).form w (auxiliaryGroundSourceEnergy e p he g hg hsmall)-
      (e : ℂ)*⟪highEnergyEmbedding (-p) 1 w,
        highEnergyEmbedding (-p) 1 (auxiliaryGroundSourceEnergy e p he g hg hsmall)⟫_ℂ =
      highFiberSourceLoad g (-p) 1 w :=
    auxiliaryGroundSourceEnergy_weak e p he g hg hsmall w
  have hr := compressedWeak_reflection g e (-p) 1 none (highFiberSourceLoad g (-p) 1)
    (auxiliaryGroundSourceEnergy e p he g hg hsmall) hx
  intro w
  have h := hr w
  rw [←highFiberSourceLoad_reflection g (-p) 1 (highEnergyReflectionInv (-p) 1 w),
    highEnergyReflection_apply_inverse] at h
  exact h

theorem auxiliarySelfEnergy_even :
    auxiliarySelfEnergy e (-p) he g hg hsmall = auxiliarySelfEnergy e p he g hg hsmall := by
  unfold auxiliarySelfEnergy
  rw [←auxiliaryGroundSourceEnergy_reflection e p he g hg hsmall,
    highFiberSourceLoad_reflection g (-p) 1 (auxiliaryGroundSourceEnergy e p he g hg hsmall)]

end Froehlich
