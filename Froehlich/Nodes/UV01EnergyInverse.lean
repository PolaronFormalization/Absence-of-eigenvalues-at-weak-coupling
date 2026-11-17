import Froehlich.Nodes.UV01NormalizedForm
import Froehlich.Nodes.RS01CompressedInverse

/-! Actual original-energy inverse maps in Riesz coordinates. The same
onto lift and the same e are used on the cutoff and singular sides. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)

theorem auxiliaryLoad_pullback_riesz (F : ConjugateLoad (HighEnergySpace (-p) n)) :
    loadRiesz (F.comp (auxiliaryEnergyLiftEquivalence n e p hn he).toContinuousLinearMap) =
      (auxiliaryEnergyLiftEquivalence n e p hn he).toContinuousLinearMap.adjoint (loadRiesz F) := by
  apply Eq.symm
  apply loadRiesz_unique
  intro w
  change F (auxiliaryEnergyLiftEquivalence n e p hn he w) = _
  rw [loadRiesz_spec]
  exact ((auxiliaryEnergyLiftEquivalence n e p hn he).toContinuousLinearMap.adjoint_inner_right w (loadRiesz F)).symm

theorem auxiliaryEnergyLiftEquivalence_opNorm_le :
    ‖(auxiliaryEnergyLiftEquivalence n e p hn he).toContinuousLinearMap‖ ≤ Real.sqrt 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  change ‖(auxiliaryEnergyLiftEquivalence n e p hn he u : EnergySpace (-p))‖ ≤ _
  rw [auxiliaryEnergyLiftEquivalence_val]
  exact auxiliaryEnergyLift_norm_le n e p he.2 u

variable (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2)

def cutoffAuxiliaryEnergyInverse (Λ : GW.Operators.PositiveCutoff) :
    HighEnergySpace (-p) n →L[ℂ] HighEnergySpace (-p) n :=
  (auxiliaryEnergyLiftEquivalence n e p hn he).toContinuousLinearMap.comp
    ((cutoffAuxiliaryNormalizedInverse g Λ.val Λ.property n e p he.2 hg hsmall).comp
      (auxiliaryEnergyLiftEquivalence n e p hn he).toContinuousLinearMap.adjoint)

theorem cutoffAuxiliaryEnergyInverse_load (Λ : GW.Operators.PositiveCutoff)
    (F : ConjugateLoad (HighEnergySpace (-p) n)) :
    cutoffAuxiliaryEnergyInverse n e p hn he g hg hsmall Λ (loadRiesz F) =
      cutoffAuxiliaryDualSolution n e p hn he g hg hsmall Λ F := by
  change auxiliaryEnergyLiftEquivalence n e p hn he
    (cutoffAuxiliaryNormalizedInverse g Λ.val Λ.property n e p he.2 hg hsmall
      ((auxiliaryEnergyLiftEquivalence n e p hn he).toContinuousLinearMap.adjoint (loadRiesz F))) = _
  rw [← auxiliaryLoad_pullback_riesz n e p hn he F]
  rfl

theorem cutoffAuxiliaryEnergyInverse_weak (Λ : GW.Operators.PositiveCutoff)
    (F : ConjugateLoad (HighEnergySpace (-p) n)) (w : HighEnergySpace (-p) n) :
    (fiberFormData g (-p) (some Λ)).form (w : EnergySpace (-p))
      (cutoffAuxiliaryEnergyInverse n e p hn he g hg hsmall Λ (loadRiesz F) : EnergySpace (-p)) +
      ((1-(n : ℝ)-e : ℝ) : ℂ)*
        ⟪energyEmbedding (-p) (w : EnergySpace (-p)),
          energyEmbedding (-p) (cutoffAuxiliaryEnergyInverse n e p hn he g hg hsmall Λ (loadRiesz F) : EnergySpace (-p))⟫_ℂ = F w := by
  rw [cutoffAuxiliaryEnergyInverse_load]
  exact cutoffAuxiliaryDualSolution_weak n e p hn he g hg hsmall Λ F w

theorem cutoffAuxiliaryEnergyInverse_difference (Λ : GW.Operators.PositiveCutoff) :
    cutoffAuxiliaryEnergyInverse n e p hn he g hg hsmall Λ - auxiliaryCompressedEnergyInverse n e p hn he g hg hsmall =
      (auxiliaryEnergyLiftEquivalence n e p hn he).toContinuousLinearMap.comp
        (((cutoffAuxiliaryNormalizedInverse g Λ.val Λ.property n e p he.2 hg hsmall) -
          auxiliaryNormalizedInverse g n e p he.2 hg hsmall).comp
            (auxiliaryEnergyLiftEquivalence n e p hn he).toContinuousLinearMap.adjoint) := by
  apply ContinuousLinearMap.ext
  intro u
  change auxiliaryEnergyLiftEquivalence n e p hn he _ - auxiliaryEnergyLiftEquivalence n e p hn he _ =
    auxiliaryEnergyLiftEquivalence n e p hn he (_-_)
  exact ((auxiliaryEnergyLiftEquivalence n e p hn he).map_sub _ _).symm

theorem cutoffAuxiliaryEnergyInverse_error (Λ : GW.Operators.PositiveCutoff) (hΛ : 1 ≤ Λ.val) :
    ‖cutoffAuxiliaryEnergyInverse n e p hn he g hg hsmall Λ - auxiliaryCompressedEnergyInverse n e p hn he g hg hsmall‖ ≤
      36*lyHighConstant * |g| / Real.sqrt Λ.val := by
  let L := (auxiliaryEnergyLiftEquivalence n e p hn he).toContinuousLinearMap
  let D := cutoffAuxiliaryNormalizedInverse g Λ.val Λ.property n e p he.2 hg hsmall -
    auxiliaryNormalizedInverse g n e p he.2 hg hsmall
  have hL : ‖L‖ ≤ Real.sqrt 3 := auxiliaryEnergyLiftEquivalence_opNorm_le n e p hn he
  have hLa : ‖L.adjoint‖ ≤ Real.sqrt 3 :=
    (ContinuousLinearMap.adjoint.norm_map L).trans_le hL
  have hpair : ‖L‖*‖L.adjoint‖ ≤ 3 := by
    have h := mul_le_mul hL hLa (norm_nonneg L.adjoint) (Real.sqrt_nonneg 3)
    simpa only [← pow_two,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] using h
  have hD : ‖D‖ ≤ 12*lyHighConstant * |g| / Real.sqrt Λ.val :=
    cutoffAuxiliaryNormalizedInverse_error g Λ.val Λ.property n e p he.2 hg hsmall hΛ
  rw [cutoffAuxiliaryEnergyInverse_difference]
  change ‖L.comp (D.comp L.adjoint)‖ ≤ _
  calc
    _ ≤ ‖L‖*‖D.comp L.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖L‖*(‖D‖*‖L.adjoint‖) := mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg L)
    _ = (‖L‖*‖L.adjoint‖)*‖D‖ := by ring
    _ ≤ 3*‖D‖ := mul_le_mul_of_nonneg_right hpair (norm_nonneg D)
    _ ≤ 3*(12*lyHighConstant * |g| / Real.sqrt Λ.val) := mul_le_mul_of_nonneg_left hD (by norm_num)
    _ = _ := by ring

end Froehlich
