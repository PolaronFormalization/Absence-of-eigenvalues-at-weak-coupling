import Froehlich.Nodes.RS02RelativeJets
import Froehlich.Nodes.FB02A

/-! Literal fixed-energy interaction jet pairs and their bounded Riesz
representatives. These are the summands in the source product formula. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def auxiliaryOriginalWeightJet (is : List (Fin 3)) (n : ℕ) (e : ℝ)
    (p0 p : GW.Space) (he : e ≤ 0) : HighSectorSpace n →L[ℂ] EnergySpace (-p0) :=
  (auxiliaryToEnergy n e p0 he).comp (auxiliaryFixedEnergyWeightJet is n e p0 p he)

theorem auxiliaryOriginalWeightJet_physical (is : List (Fin 3)) (n : ℕ) (e : ℝ)
    (p0 p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (u : HighSectorSpace n) :
    energyEmbedding (-p0) (auxiliaryOriginalWeightJet is n e p0 p he.2 u) =
      (auxiliaryPhysicalWeightJet is n e p he.2 u : GW.Fock.Carrier) := by
  change energyEmbedding (-p0) (auxiliaryToEnergy n e p0 he.2
    (auxiliaryFixedEnergyWeightJet is n e p0 p he.2 u)) = _
  rw [auxiliaryToEnergy_physical n e p0 hn he]
  have h := congrArg (fun A : HighSectorSpace n →L[ℂ] HighSectorSpace n => (A u : GW.Fock.Carrier))
    (auxiliaryFixedEnergyWeightJet_physical is n e p0 p he.2)
  exact h

theorem auxiliaryOriginalWeightJet_change (is : List (Fin 3)) (n : ℕ) (e : ℝ)
    (p0 p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (u : HighSectorSpace n) :
    auxiliaryOriginalWeightJet is n e p0 p he.2 u =
      energyCoordinateChange (-p0) (-p)
        (auxiliaryEnergyLift n e p he.2 (auxiliaryRelativeWeightJet is n e p he.2 u)) := by
  apply energyEmbedding_injective (-p0)
  rw [auxiliaryOriginalWeightJet_physical is n e p0 p hn he,
    energyCoordinateChange_intertwines,auxiliaryEnergyLift_physical n e p hn he]
  have h := congrArg (fun A : HighSectorSpace n →L[ℂ] HighSectorSpace n => (A u : GW.Fock.Carrier))
    (auxiliaryRelativeWeightJet_factor is n e p he.2)
  exact h.symm

def auxiliaryInteractionJetPair (g : ℝ) (is js : List (Fin 3)) (n : ℕ) (e : ℝ)
    (p : GW.Space) (he : e ≤ 0) : HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  (auxiliaryRelativeWeightJet is n e p he).adjoint.comp
    ((auxiliaryInteractionOperator g n e p he).comp (auxiliaryRelativeWeightJet js n e p he))

theorem auxiliaryInteractionJetPair_spec (g : ℝ) (is js : List (Fin 3)) (n : ℕ) (e : ℝ)
    (p0 p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (w u : HighSectorSpace n) :
    singularInteraction g (-p0) (auxiliaryOriginalWeightJet is n e p0 p he.2 w)
      (auxiliaryOriginalWeightJet js n e p0 p he.2 u) =
        ⟪w,auxiliaryInteractionJetPair g is js n e p he.2 u⟫_ℂ := by
  rw [auxiliaryOriginalWeightJet_change is n e p0 p hn he,
    auxiliaryOriginalWeightJet_change js n e p0 p hn he,singularInteraction_change]
  simp only [auxiliaryInteractionJetPair,ContinuousLinearMap.comp_apply,
    (auxiliaryRelativeWeightJet is n e p he.2).adjoint_inner_right]
  exact formRepresentative_spec (auxiliaryInteractionForm g n e p he.2) _ _

theorem auxiliaryInteractionJetPair_norm_le (g : ℝ) (is js : List (Fin 3)) (n : ℕ) (e : ℝ)
    (p : GW.Space) (he : e ≤ 0) (hg : |g| ≤ 1) :
    ‖auxiliaryInteractionJetPair g is js n e p he‖ ≤
      scalarDerivativeCoefficientBound is.length * scalarDerivativeCoefficientBound js.length *
        auxiliaryResolventConstant * |g| := by
  let A := auxiliaryRelativeWeightJet is n e p he
  let B := auxiliaryRelativeWeightJet js n e p he
  let T := auxiliaryInteractionOperator g n e p he
  have hA : ‖A.adjoint‖ ≤ scalarDerivativeCoefficientBound is.length :=
    (ContinuousLinearMap.adjoint.norm_map A).trans_le (auxiliaryRelativeWeightJet_norm_le is n e p he)
  have hB : ‖B‖ ≤ scalarDerivativeCoefficientBound js.length := auxiliaryRelativeWeightJet_norm_le js n e p he
  have hT : ‖T‖ ≤ auxiliaryResolventConstant*|g| := auxiliaryInteractionOperator_norm_le g n e p he hg
  have hc : 0 ≤ auxiliaryResolventConstant*|g| := mul_nonneg auxiliaryResolventConstant_pos.le (abs_nonneg g)
  have hTB := mul_le_mul hT hB B.opNorm_nonneg hc
  have hprod := mul_le_mul hA hTB (mul_nonneg T.opNorm_nonneg B.opNorm_nonneg)
    (scalarDerivativeCoefficientBound_nonnegative is.length)
  change ‖A.adjoint.comp (T.comp B)‖ ≤ _
  calc
    _ ≤ ‖A.adjoint‖*‖T.comp B‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A.adjoint‖*(‖T‖*‖B‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) A.adjoint.opNorm_nonneg
    _ ≤ scalarDerivativeCoefficientBound is.length *
        ((auxiliaryResolventConstant*|g|)*scalarDerivativeCoefficientBound js.length) := hprod
    _ = _ := by ring

end Froehlich
