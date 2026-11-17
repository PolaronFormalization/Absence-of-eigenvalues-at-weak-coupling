import Froehlich.Nodes.FB02UniformData
import Froehlich.Nodes.FB02Transport

/-! The actual singular interaction as the retained GW cutoff norm limit.
No uncut form factor is treated as a physical one-particle vector. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich

def singularInteraction (g : ℝ) (P : GW.Space) : GW.Analysis.BoundedForm (EnergySpace P) :=
  GW.Operators.uniformLimitForm (fiberUniformData g P)

theorem uniformCutoffForm_eq (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) :
    GW.Operators.uniformBoundedForm (fiberUniformData g P) Λ =
      cutoffInteractionForm g Λ.val Λ.property P := by
  ext w u
  exact GW.Operators.uniformBoundedForm_source (fiberUniformData g P) Λ w u

theorem cutoffInteraction_tendsto (g : ℝ) (P : GW.Space) :
    Tendsto (fun Λ : GW.Operators.PositiveCutoff => cutoffInteractionForm g Λ.val Λ.property P)
      atTop (𝓝 (singularInteraction g P)) := by
  have h := GW.Operators.uniformLimitForm_tendsto (fiberUniformData g P)
  have he : GW.Operators.uniformBoundedForm (fiberUniformData g P) =
      fun Λ : GW.Operators.PositiveCutoff => cutoffInteractionForm g Λ.val Λ.property P :=
    funext (uniformCutoffForm_eq g P)
  rw [he] at h
  exact h

theorem singularInteraction_hermitian (g : ℝ) (P : GW.Space) (w u : EnergySpace P) :
    singularInteraction g P w u = star (singularInteraction g P u w) :=
  GW.Operators.uniformLimitForm_hermitian (fiberUniformData g P) w u

theorem cutoffInteraction_limit_error (g R Λ : ℝ) (hR : 0 < R) (hΛ : 0 < Λ)
    (hRΛ : R ≤ Λ) (P : GW.Space) :
    ‖cutoffInteractionForm g Λ hΛ P - singularInteraction g P‖ ≤ cutoffTailError g R := by
  have h := GW.Operators.uniformLimitForm_error (fiberUniformData g P) R hR ⟨Λ,hΛ⟩ hRΛ
  rw [uniformCutoffForm_eq] at h
  exact h

theorem singularInteraction_unique (g : ℝ) (P : GW.Space)
    (b : GW.Analysis.BoundedForm (EnergySpace P))
    (hb : Tendsto (fun Λ : GW.Operators.PositiveCutoff => cutoffInteractionForm g Λ.val Λ.property P)
      atTop (𝓝 b)) : b = singularInteraction g P :=
  tendsto_nhds_unique hb (cutoffInteraction_tendsto g P)

theorem singularInteraction_change (g : ℝ) (P Q : GW.Space) (w u : EnergySpace Q) :
    singularInteraction g P (energyCoordinateChange P Q w) (energyCoordinateChange P Q u) =
      singularInteraction g Q w u := by
  have hP := boundedForm_eval_tendsto (cutoffInteraction_tendsto g P)
    (energyCoordinateChange P Q w) (energyCoordinateChange P Q u)
  have hQ := boundedForm_eval_tendsto (cutoffInteraction_tendsto g Q) w u
  have he : (fun Λ : GW.Operators.PositiveCutoff => cutoffInteractionForm g Λ.val Λ.property P
      (energyCoordinateChange P Q w) (energyCoordinateChange P Q u)) =
      (fun Λ : GW.Operators.PositiveCutoff => cutoffInteractionForm g Λ.val Λ.property Q w u) :=
    funext (fun Λ => cutoffInteractionForm_change g Λ.val Λ.property P Q w u)
  rw [he] at hP
  exact tendsto_nhds_unique hP hQ

theorem liebYamazaki_singular (g : ℝ) (P : GW.Space) (u : EnergySpace P)
    (theta : ℝ) (ht : 0 < theta) :
    ‖singularInteraction g P u u‖ ≤ theta * freeEnergy P (energyEmbedding P u) +
      lyRemainderConstant * (g^2/theta + g^4/theta^3) * ‖energyEmbedding P u‖^2 :=
  le_of_tendsto ((boundedForm_eval_tendsto (cutoffInteraction_tendsto g P) u u).norm)
    (Eventually.of_forall (fun Λ => liebYamazaki_cutoff g Λ.val Λ.property P u theta ht))

theorem liebYamazaki_singular_small (g : ℝ) (P : GW.Space) (u : EnergySpace P)
    (theta : ℝ) (ht : 0 < theta) (hg : |g| ≤ theta) :
    ‖singularInteraction g P u u‖ ≤ theta * freeEnergy P (energyEmbedding P u) +
      (2*lyRemainderConstant*g^2/theta) * ‖energyEmbedding P u‖^2 :=
  le_of_tendsto ((boundedForm_eval_tendsto (cutoffInteraction_tendsto g P) u u).norm)
    (Eventually.of_forall (fun Λ => liebYamazaki_cutoff_small g Λ.val Λ.property P u theta ht hg))

end Froehlich
