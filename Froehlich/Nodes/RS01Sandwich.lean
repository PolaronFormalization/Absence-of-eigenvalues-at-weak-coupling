import Froehlich.Nodes.RS01ComparisonPhysical
import Froehlich.Nodes.FB02

/-! The actual bounded interaction sandwich on the physical high sector.
It uses the checked energy-valued free inverse and BA01's Riesz orientation. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def auxiliaryPhysicalFreeInverse (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  (auxiliaryEnergyEmbedding n e p he).comp
    (auxiliaryFreeInverseEnergy n e p he).toLinearIsometry.toContinuousLinearMap

def auxiliaryEnergyLift (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    HighSectorSpace n →L[ℂ] EnergySpace (-p) :=
  (auxiliaryToEnergy n e p he).comp
    (auxiliaryFreeInverseEnergy n e p he).toLinearIsometry.toContinuousLinearMap

theorem auxiliaryEnergyLift_norm_le (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (u : HighSectorSpace n) : ‖auxiliaryEnergyLift n e p he u‖ ≤ Real.sqrt 3 * ‖u‖ := by
  exact (auxiliaryToEnergy_norm_le n e p he (auxiliaryFreeInverseEnergy n e p he u)).trans_eq
    (congrArg (fun a : ℝ => Real.sqrt 3*a) ((auxiliaryFreeInverseEnergy n e p he).norm_map u))

theorem auxiliaryEnergyLift_physical (n : ℕ) (e : ℝ) (p : GW.Space)
    (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (u : HighSectorSpace n) :
    energyEmbedding (-p) (auxiliaryEnergyLift n e p he.2 u) =
      (auxiliaryPhysicalFreeInverse n e p he.2 u : GW.Fock.Carrier) := by
  change energyEmbedding (-p) (auxiliaryToEnergy n e p he.2 (auxiliaryFreeInverseEnergy n e p he.2 u)) = _
  rw [auxiliaryToEnergy_physical n e p hn he]
  rfl

def auxiliaryInteractionForm (g : ℝ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    GW.Analysis.BoundedForm (HighSectorSpace n) :=
  ((ContinuousLinearMap.compL ℂ (HighSectorSpace n) (EnergySpace (-p)) ℂ).flip
    (auxiliaryEnergyLift n e p he)).comp
      ((singularInteraction g (-p)).comp (auxiliaryEnergyLift n e p he))

theorem auxiliaryInteractionForm_apply (g : ℝ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (w u : HighSectorSpace n) :
    auxiliaryInteractionForm g n e p he w u =
      singularInteraction g (-p) (auxiliaryEnergyLift n e p he w) (auxiliaryEnergyLift n e p he u) := rfl

def auxiliaryInteractionOperator (g : ℝ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  formRepresentative (auxiliaryInteractionForm g n e p he)

def auxiliaryResolventConstant : ℝ := 3*phiMixedConstant

theorem auxiliaryResolventConstant_pos : 0 < auxiliaryResolventConstant :=
  mul_pos (by norm_num) phiMixedConstant_pos

theorem auxiliaryInteractionOperator_selfadjoint (g : ℝ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    (auxiliaryInteractionOperator g n e p he).adjoint = auxiliaryInteractionOperator g n e p he := by
  apply formRepresentative_selfadjoint
  intro w u
  exact singularInteraction_hermitian g (-p) (auxiliaryEnergyLift n e p he w) (auxiliaryEnergyLift n e p he u)

theorem auxiliaryInteractionOperator_norm_le (g : ℝ) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (hg : |g| ≤ 1) : ‖auxiliaryInteractionOperator g n e p he‖ ≤ auxiliaryResolventConstant* |g| := by
  apply formRepresentative_norm_le _ (mul_nonneg auxiliaryResolventConstant_pos.le (abs_nonneg g))
  intro w u
  rw [auxiliaryInteractionForm_apply]
  have h := fb02_smallCoupling_mixed g (-p) (auxiliaryEnergyLift n e p he w) (auxiliaryEnergyLift n e p he u) hg
  have hm := mul_le_mul (auxiliaryEnergyLift_norm_le n e p he w) (auxiliaryEnergyLift_norm_le n e p he u)
    (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg w))
  calc
    _ ≤ phiMixedConstant* |g| *‖auxiliaryEnergyLift n e p he w‖ *‖auxiliaryEnergyLift n e p he u‖ := h
    _ = (phiMixedConstant* |g|)*(‖auxiliaryEnergyLift n e p he w‖ *‖auxiliaryEnergyLift n e p he u‖) := by ring
    _ ≤ (phiMixedConstant* |g|)*((Real.sqrt 3*‖w‖)*(Real.sqrt 3*‖u‖)) :=
      mul_le_mul_of_nonneg_left hm (mul_nonneg phiMixedConstant_pos.le (abs_nonneg g))
    _ = auxiliaryResolventConstant* |g| *‖w‖ *‖u‖ := by
      dsimp [auxiliaryResolventConstant]
      calc
        _ = (Real.sqrt 3)^2*phiMixedConstant* |g| *‖w‖ *‖u‖ := by simp only [Submodule.norm_coe]; ring
        _ = _ := by
          rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
          simp only [Submodule.norm_coe]

end Froehlich
