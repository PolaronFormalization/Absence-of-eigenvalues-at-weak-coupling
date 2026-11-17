import Froehlich.Nodes.SY01Creation
import Froehlich.Nodes.SY01CutoffFactors
import Froehlich.Nodes.FB02A

/-! Reality and reflection of the actual finite forms and their constructed
norm limits. No uncut form factor is assigned a physical L² class. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace Topology
namespace Froehlich

theorem fieldRestriction_conjugation (f : GW.OnePhonon) (x : NumberFormSpace) :
    fieldRestriction (conjugateOnePhonon f) (numberConjugation x) =
      fockConjugation (fieldRestriction f x) := by
  change annihilationRestriction _ _ + creationRestriction _ _ =
    fockConjugation (annihilationRestriction f x + creationRestriction f x)
  rw [annihilationRestriction_conjugation, creationRestriction_conjugation, fockConjugation_add]

theorem fieldRestriction_reflection (f : GW.OnePhonon) (x : NumberFormSpace) :
    fieldRestriction (reflectOnePhonon f) (numberReflection x) =
      fockReflection (fieldRestriction f x) := by
  change annihilationRestriction _ _ + creationRestriction _ _ =
    fockReflection (annihilationRestriction f x + creationRestriction f x)
  rw [annihilationRestriction_reflection, creationRestriction_reflection, map_add]

theorem cutoffField_conjugation (g Λ : ℝ) (hΛ : 0 < Λ) (x : NumberFormSpace) :
    fieldRestriction (cutoffFormFactorL2 g Λ hΛ) (numberConjugation x) =
      fockConjugation (fieldRestriction (cutoffFormFactorL2 g Λ hΛ) x) := by
  simpa only [cutoffFormFactorL2_conjugation] using
    fieldRestriction_conjugation (cutoffFormFactorL2 g Λ hΛ) x

theorem cutoffField_reflection (g Λ : ℝ) (hΛ : 0 < Λ) (x : NumberFormSpace) :
    fieldRestriction (cutoffFormFactorL2 g Λ hΛ) (numberReflection x) =
      fockReflection (fieldRestriction (cutoffFormFactorL2 g Λ hΛ) x) := by
  simpa only [cutoffFormFactorL2_reflection] using
    fieldRestriction_reflection (cutoffFormFactorL2 g Λ hΛ) x

theorem cutoffInteraction_conjugation (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space) (w u : EnergySpace P) :
    cutoffInteractionForm g Λ hΛ P (energyConjugation P w) (energyConjugation P u) =
      (starRingEnd ℂ) (cutoffInteractionForm g Λ hΛ P w u) := by
  change ⟪energyEmbedding P (energyConjugation P w),
      fieldRestriction (cutoffFormFactorL2 g Λ hΛ)
        (energyNumberCoordinates P (energyConjugation P u))⟫_ℂ =
    (starRingEnd ℂ) ⟪energyEmbedding P w,
      fieldRestriction (cutoffFormFactorL2 g Λ hΛ) (energyNumberCoordinates P u)⟫_ℂ
  rw [energyConjugation_intertwines, energyNumberCoordinates_conjugation, cutoffField_conjugation,
    fockConjugation_inner]

theorem cutoffInteraction_reflection (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space) (w u : EnergySpace P) :
    cutoffInteractionForm g Λ hΛ (-P) (energyReflection P w) (energyReflection P u) =
      cutoffInteractionForm g Λ hΛ P w u := by
  change ⟪energyEmbedding (-P) (energyReflection P w),
      fieldRestriction (cutoffFormFactorL2 g Λ hΛ)
        (energyNumberCoordinates (-P) (energyReflection P u))⟫_ℂ =
    ⟪energyEmbedding P w,
      fieldRestriction (cutoffFormFactorL2 g Λ hΛ) (energyNumberCoordinates P u)⟫_ℂ
  rw [energyReflection_intertwines, energyNumberCoordinates_reflection, cutoffField_reflection]
  exact fockReflectionEquiv.inner_map_map _ _

theorem singularInteraction_conjugation (g : ℝ) (P : GW.Space) (w u : EnergySpace P) :
    singularInteraction g P (energyConjugation P w) (energyConjugation P u) =
      (starRingEnd ℂ) (singularInteraction g P w u) := by
  have hJ := boundedForm_eval_tendsto (cutoffInteraction_tendsto g P)
    (energyConjugation P w) (energyConjugation P u)
  have h := boundedForm_eval_tendsto (cutoffInteraction_tendsto g P) w u
  have hstar := (Complex.conjCLE.continuous.tendsto (singularInteraction g P w u)).comp h
  have he : (fun Λ : GW.Operators.PositiveCutoff =>
      cutoffInteractionForm g Λ.val Λ.property P (energyConjugation P w) (energyConjugation P u)) =
      (fun Λ : GW.Operators.PositiveCutoff =>
        (starRingEnd ℂ) (cutoffInteractionForm g Λ.val Λ.property P w u)) :=
    funext (fun Λ => cutoffInteraction_conjugation g Λ.val Λ.property P w u)
  rw [he] at hJ
  exact tendsto_nhds_unique hJ hstar

theorem singularInteraction_reflection (g : ℝ) (P : GW.Space) (w u : EnergySpace P) :
    singularInteraction g (-P) (energyReflection P w) (energyReflection P u) =
      singularInteraction g P w u := by
  have hR := boundedForm_eval_tendsto (cutoffInteraction_tendsto g (-P))
    (energyReflection P w) (energyReflection P u)
  have h := boundedForm_eval_tendsto (cutoffInteraction_tendsto g P) w u
  have he : (fun Λ : GW.Operators.PositiveCutoff =>
      cutoffInteractionForm g Λ.val Λ.property (-P) (energyReflection P w) (energyReflection P u)) =
      (fun Λ : GW.Operators.PositiveCutoff => cutoffInteractionForm g Λ.val Λ.property P w u) :=
    funext (fun Λ => cutoffInteraction_reflection g Λ.val Λ.property P w u)
  rw [he] at hR
  exact tendsto_nhds_unique hR h

end Froehlich
