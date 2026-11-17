import Froehlich.Nodes.UV01CommonSourceSolutions
import Froehlich.Nodes.RS01AuxiliaryFields

/-! The cutoff form-source solution and the accepted singular h, expressed
in the same fixed reference energy graph. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem auxiliaryCompressedEnergyInverse_load (n : ℕ) (e : ℝ) (p : GW.Space)
    (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2) (F : ConjugateLoad (HighEnergySpace (-p) n)) :
    auxiliaryCompressedEnergyInverse n e p hn he g hg hsmall (loadRiesz F) =
      auxiliaryDualSolution n e p hn he g hg hsmall F := by
  change auxiliaryEnergyLiftEquivalence n e p hn he
    (auxiliaryNormalizedInverse g n e p he.2 hg hsmall
      ((auxiliaryEnergyLiftEquivalence n e p hn he).toContinuousLinearMap.adjoint (loadRiesz F))) = _
  rw [←auxiliaryLoad_pullback_riesz n e p hn he F]
  rfl

variable (e : ℝ) (p : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2)

def cutoffGroundSourceEnergy (Λ : GW.Operators.PositiveCutoff) : HighEnergySpace (-p) 1 :=
  cutoffAuxiliaryDualSolution 1 e p (by norm_num) he g hg hsmall Λ
    (cutoffHighFiberSourceLoad g (-p) 1 Λ.val)

theorem cutoffGroundSourceEnergy_weak (Λ : GW.Operators.PositiveCutoff) (w : HighEnergySpace (-p) 1) :
    (fiberFormData g (-p) (some Λ)).form (w : EnergySpace (-p))
      (cutoffGroundSourceEnergy e p he g hg hsmall Λ : EnergySpace (-p)) -
      (e : ℂ)*⟪energyEmbedding (-p) (w : EnergySpace (-p)),
        energyEmbedding (-p) (cutoffGroundSourceEnergy e p he g hg hsmall Λ : EnergySpace (-p))⟫_ℂ =
      cutoffHighFiberSourceLoad g (-p) 1 Λ.val w := by
  have h := cutoffAuxiliaryDualSolution_weak 1 e p (by norm_num) he g hg hsmall Λ
    (cutoffHighFiberSourceLoad g (-p) 1 Λ.val) w
  simpa only [Nat.cast_one,sub_self,zero_sub,zero_add,Complex.ofReal_neg,neg_mul,
    sub_eq_add_neg,cutoffGroundSourceEnergy] using! h

theorem cutoffCommonGroundSourceSolution_eq (p0 : GW.Space) (Λ : GW.Operators.PositiveCutoff) :
    cutoffCommonSourceSolution 1 e p0 p (by norm_num) he g hg hsmall Λ =
      highEnergyCoordinateChange (-p0) (-p) 1 (cutoffGroundSourceEnergy e p he g hg hsmall Λ) :=
  cutoffCommonSourceSolution_eq 1 e p0 p (by norm_num) he g hg hsmall Λ

theorem singularCommonGroundSourceSolution_eq (p0 : GW.Space) :
    singularCommonSourceSolution 1 e p0 p (by norm_num) he g hg hsmall =
      highEnergyCoordinateChange (-p0) (-p) 1 (auxiliaryGroundSourceEnergy e p he g hg hsmall) := by
  rw [singularCommonSourceSolution_eq,auxiliaryCompressedEnergyInverse_load]
  rfl

end Froehlich
