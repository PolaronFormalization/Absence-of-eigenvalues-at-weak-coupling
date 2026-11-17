import Froehlich.Nodes.UV01Neumann
import Froehlich.Nodes.RS01NormalizedForm

/-! Cutoff normalized inverses solve the literal compressed cutoff form
on every original energy test, with the same fixed reference e. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)

include hn in
theorem cutoffAuxiliaryNormalizedOperator_form (g : ℝ) (Λ : GW.Operators.PositiveCutoff)
    (w u : HighSectorSpace n) :
    ⟪w,cutoffAuxiliaryNormalizedOperator g Λ.val Λ.property n e p he.2 u⟫_ℂ =
      (fiberFormData g (-p) (some Λ)).form (auxiliaryEnergyLift n e p he.2 w) (auxiliaryEnergyLift n e p he.2 u) +
      ((1-(n : ℝ)-e : ℝ) : ℂ)*
        ⟪energyEmbedding (-p) (auxiliaryEnergyLift n e p he.2 w),
          energyEmbedding (-p) (auxiliaryEnergyLift n e p he.2 u)⟫_ℂ := by
  have hf := auxiliaryEnergyLift_freeForm n e p hn he w u
  have ht := (formRepresentative_spec (cutoffAuxiliaryInteractionForm g Λ.val Λ.property n e p he.2) w u).symm
  rw [cutoffAuxiliaryInteractionForm_apply] at ht
  change ⟪w,cutoffAuxiliaryInteractionOperator g Λ.val Λ.property n e p he.2 u⟫_ℂ =
    cutoffInteractionForm g Λ.val Λ.property (-p)
      (auxiliaryEnergyLift n e p he.2 w) (auxiliaryEnergyLift n e p he.2 u) at ht
  simp only [cutoffAuxiliaryNormalizedOperator,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply,inner_add_right]
  rw [ht,fiberFormData_cutoff_apply]
  linear_combination -hf

variable (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2)

def cutoffAuxiliaryDualSolution (Λ : GW.Operators.PositiveCutoff)
    (F : ConjugateLoad (HighEnergySpace (-p) n)) : HighEnergySpace (-p) n :=
  auxiliaryEnergyLiftEquivalence n e p hn he
    (cutoffAuxiliaryNormalizedInverse g Λ.val Λ.property n e p he.2 hg hsmall
      (loadRiesz (F.comp (auxiliaryEnergyLiftEquivalence n e p hn he).toContinuousLinearMap)))

theorem cutoffAuxiliaryDualSolution_weak (Λ : GW.Operators.PositiveCutoff)
    (F : ConjugateLoad (HighEnergySpace (-p) n)) (w : HighEnergySpace (-p) n) :
    (fiberFormData g (-p) (some Λ)).form (w : EnergySpace (-p))
      (cutoffAuxiliaryDualSolution n e p hn he g hg hsmall Λ F : EnergySpace (-p)) +
      ((1-(n : ℝ)-e : ℝ) : ℂ)*
        ⟪energyEmbedding (-p) (w : EnergySpace (-p)),
          energyEmbedding (-p) (cutoffAuxiliaryDualSolution n e p hn he g hg hsmall Λ F : EnergySpace (-p))⟫_ℂ = F w := by
  let L := auxiliaryEnergyLiftEquivalence n e p hn he
  let v := L.symm w
  let z := loadRiesz (F.comp L.toContinuousLinearMap)
  let y := cutoffAuxiliaryNormalizedInverse g Λ.val Λ.property n e p he.2 hg hsmall z
  have hm : cutoffAuxiliaryNormalizedOperator g Λ.val Λ.property n e p he.2 y = z :=
    congrArg (fun T : HighSectorSpace n →L[ℂ] HighSectorSpace n => T z)
      (cutoffAuxiliaryNormalizedInverse_right g Λ.val Λ.property n e p he.2 hg hsmall)
  have hl : ⟪v,z⟫_ℂ = F w := by
    calc
      _ = (F.comp L.toContinuousLinearMap) v := (loadRiesz_spec (F.comp L.toContinuousLinearMap) v).symm
      _ = F w := by change F (L (L.symm w)) = F w; rw [L.apply_symm_apply]
  have hw : auxiliaryEnergyLift n e p he.2 v = (w : EnergySpace (-p)) := by
    rw [← auxiliaryEnergyLiftEquivalence_val n e p hn he,L.apply_symm_apply]
  have hy : auxiliaryEnergyLift n e p he.2 y =
      (cutoffAuxiliaryDualSolution n e p hn he g hg hsmall Λ F : EnergySpace (-p)) := rfl
  have h := cutoffAuxiliaryNormalizedOperator_form n e p hn he g Λ v y
  rw [hm,hl,hw,hy] at h
  exact h.symm

end Froehlich
