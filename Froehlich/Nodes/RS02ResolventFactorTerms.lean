import Froehlich.Nodes.RS02WeightAdjoints
import Froehlich.Nodes.RS02RelativeJets

/-! Every actual differentiated outer weight admits the required two-sided
factorization by G; the middle factor is bounded on the physical high sector. -/
noncomputable section
namespace Froehlich

theorem auxiliaryPhysicalWeightJet_right_factor (is : List (Fin 3)) (n : ℕ)
    (e : ℝ) (he : e ≤ 0) (p : GW.Space) :
    auxiliaryPhysicalWeightJet is n e p he =
      (auxiliaryRelativeWeightJet is n e p he).adjoint.comp (auxiliaryPhysicalFreeInverse n e p he) := by
  have h := congrArg ContinuousLinearMap.adjoint (auxiliaryRelativeWeightJet_factor is n e p he)
  rw [ContinuousLinearMap.adjoint_comp,auxiliaryPhysicalFreeInverse_selfadjoint,
    auxiliaryPhysicalWeightJet_selfadjoint] at h
  exact h.symm

def auxiliaryResolventMiddleTerm (is js : List (Fin 3)) (n : ℕ) (e : ℝ)
    (p : GW.Space) (he : e ≤ 0) (A : HighSectorSpace n →L[ℂ] HighSectorSpace n) :
    HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  (auxiliaryRelativeWeightJet is n e p he).comp
    (A.comp (auxiliaryRelativeWeightJet js n e p he).adjoint)

theorem auxiliaryResolventMiddleTerm_factor (is js : List (Fin 3)) (n : ℕ) (e : ℝ)
    (p : GW.Space) (he : e ≤ 0) (A : HighSectorSpace n →L[ℂ] HighSectorSpace n) :
    (auxiliaryPhysicalWeightJet is n e p he).comp
      (A.comp (auxiliaryPhysicalWeightJet js n e p he)) =
    (auxiliaryPhysicalFreeInverse n e p he).comp
      ((auxiliaryResolventMiddleTerm is js n e p he A).comp (auxiliaryPhysicalFreeInverse n e p he)) := by
  rw [←auxiliaryRelativeWeightJet_factor is n e p he,
    auxiliaryPhysicalWeightJet_right_factor js n e he p]
  simp only [auxiliaryResolventMiddleTerm,ContinuousLinearMap.comp_assoc]

end Froehlich
