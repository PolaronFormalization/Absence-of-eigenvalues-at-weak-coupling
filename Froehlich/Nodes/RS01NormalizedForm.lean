import Froehlich.Nodes.RS01FreeForm
import Froehlich.Nodes.RS01Neumann

/-! Exact M form correspondence and a weak solution for every conjugate
load on the full original compressed energy domain, using its onto lift. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)

def auxiliaryEnergyLiftEquivalence : HighSectorSpace n ≃L[ℂ] HighEnergySpace (-p) n :=
  (auxiliaryFreeInverseEnergy n e p he.2).toContinuousLinearEquiv.trans
    (auxiliaryHighEnergyEquivalence n e p hn he)

theorem auxiliaryEnergyLiftEquivalence_val (u : HighSectorSpace n) :
    (auxiliaryEnergyLiftEquivalence n e p hn he u : EnergySpace (-p)) =
      auxiliaryEnergyLift n e p he.2 u := rfl

include hn in
theorem auxiliaryNormalizedOperator_form (g : ℝ) (w u : HighSectorSpace n) :
    ⟪w,auxiliaryNormalizedOperator g n e p he.2 u⟫_ℂ =
      (fiberFormData g (-p) none).form (auxiliaryEnergyLift n e p he.2 w) (auxiliaryEnergyLift n e p he.2 u) +
      ((1-(n : ℝ)-e : ℝ) : ℂ)*
        ⟪energyEmbedding (-p) (auxiliaryEnergyLift n e p he.2 w),
          energyEmbedding (-p) (auxiliaryEnergyLift n e p he.2 u)⟫_ℂ := by
  have hf := auxiliaryEnergyLift_freeForm n e p hn he w u
  have ht := (formRepresentative_spec (auxiliaryInteractionForm g n e p he.2) w u).symm
  rw [auxiliaryInteractionForm_apply] at ht
  change ⟪w,auxiliaryInteractionOperator g n e p he.2 u⟫_ℂ =
    singularInteraction g (-p) (auxiliaryEnergyLift n e p he.2 w) (auxiliaryEnergyLift n e p he.2 u) at ht
  simp only [auxiliaryNormalizedOperator,ContinuousLinearMap.add_apply,ContinuousLinearMap.one_apply,inner_add_right]
  rw [ht,fiberFormData_singular_apply]
  linear_combination -hf

variable (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2)

def auxiliaryDualSolution (F : ConjugateLoad (HighEnergySpace (-p) n)) : HighEnergySpace (-p) n :=
  auxiliaryEnergyLiftEquivalence n e p hn he
    (auxiliaryNormalizedInverse g n e p he.2 hg hsmall
      (loadRiesz (F.comp (auxiliaryEnergyLiftEquivalence n e p hn he).toContinuousLinearMap)))

theorem auxiliaryDualSolution_weak (F : ConjugateLoad (HighEnergySpace (-p) n))
    (w : HighEnergySpace (-p) n) :
    (fiberFormData g (-p) none).form (w : EnergySpace (-p))
      (auxiliaryDualSolution n e p hn he g hg hsmall F : EnergySpace (-p)) +
      ((1-(n : ℝ)-e : ℝ) : ℂ)*
        ⟪energyEmbedding (-p) (w : EnergySpace (-p)),
          energyEmbedding (-p) (auxiliaryDualSolution n e p hn he g hg hsmall F : EnergySpace (-p))⟫_ℂ = F w := by
  let L := auxiliaryEnergyLiftEquivalence n e p hn he
  let v := L.symm w
  let z := loadRiesz (F.comp L.toContinuousLinearMap)
  let y := auxiliaryNormalizedInverse g n e p he.2 hg hsmall z
  have hm : auxiliaryNormalizedOperator g n e p he.2 y = z :=
    congrArg (fun T : HighSectorSpace n →L[ℂ] HighSectorSpace n => T z)
      (auxiliaryNormalizedInverse_right g n e p he.2 hg hsmall)
  have hl : ⟪v,z⟫_ℂ = F w := by
    calc
      _ = (F.comp L.toContinuousLinearMap) v := (loadRiesz_spec (F.comp L.toContinuousLinearMap) v).symm
      _ = F w := by
        change F (L (L.symm w)) = F w
        rw [L.apply_symm_apply]
  have hw : auxiliaryEnergyLift n e p he.2 v = (w : EnergySpace (-p)) := by
    rw [← auxiliaryEnergyLiftEquivalence_val n e p hn he,L.apply_symm_apply]
  have hy : auxiliaryEnergyLift n e p he.2 y =
      (auxiliaryDualSolution n e p hn he g hg hsmall F : EnergySpace (-p)) := rfl
  have h := auxiliaryNormalizedOperator_form n e p hn he g v y
  rw [hm,hl,hw,hy] at h
  exact h.symm

end Froehlich
