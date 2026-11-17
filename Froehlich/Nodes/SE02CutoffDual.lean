import Froehlich.Nodes.SE02CutoffLambdaCancellation
import Froehlich.Nodes.PT03FormThreshold
import Mathlib.Tactic.LinearCombination

/-! The actual cutoff Q1-conjugate-dual identity. The auxiliary physical
right vector exists only at finite cutoff; its integral is the literal
vΛ(1-JΛ) load. All sector equations retain the same fixed e. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

def se02CutoffRightVector (Λ : GW.Operators.PositiveCutoff) : GW.OnePhonon :=
  cutoffFormFactorL2 g Λ.val Λ.property -
    oneParticleEnergyEmbedding 0 (cutoffGroundSourceOneEnergy e he g hg hs Λ) +
      oneToHighAdjoint (cutoffFormFactorL2 g Λ.val Λ.property) (se02CutoffXHighVector e he g hg hs Λ)

theorem se02CutoffRightVector_ae (Λ : GW.Operators.PositiveCutoff) :
    se02CutoffRightVector e he g hg hs Λ =ᵐ[volume]
      (fun k => (cutoffFormFactor g Λ.val k : ℂ)*(1-cutoffThresholdKernelJ e he g hg hs Λ 0 k 0)) := by
  filter_upwards [Lp.coeFn_add
    (cutoffFormFactorL2 g Λ.val Λ.property-oneParticleEnergyEmbedding 0 (cutoffGroundSourceOneEnergy e he g hg hs Λ))
    (oneToHighAdjoint (cutoffFormFactorL2 g Λ.val Λ.property) (se02CutoffXHighVector e he g hg hs Λ)),
    Lp.coeFn_sub (cutoffFormFactorL2 g Λ.val Λ.property)
      (oneParticleEnergyEmbedding 0 (cutoffGroundSourceOneEnergy e he g hg hs Λ)),
    cutoffFormFactorL2_ae g Λ.val Λ.property,se02_cutoff_lambda_cancellation e he g hg hs Λ]
    with k hadd hsub hv hlambda
  change ((cutoffFormFactorL2 g Λ.val Λ.property-
    oneParticleEnergyEmbedding 0 (cutoffGroundSourceOneEnergy e he g hg hs Λ) +
    oneToHighAdjoint (cutoffFormFactorL2 g Λ.val Λ.property) (se02CutoffXHighVector e he g hg hs Λ)) k) = _
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hv]
  linear_combination hlambda

private theorem se02_cutoff_coupling_pair (Λ : GW.Operators.PositiveCutoff)
    (w : OneParticleEnergySpace 0) (r : HighEnergySpace 0 2) :
    ⟪w,(cutoffTwoSectorCoupling g 0 Λ).adjoint r⟫_ℂ =
      ⟪(oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) (oneParticleEnergyEmbedding 0 w) : GW.Fock.Carrier),
        energyEmbedding 0 (r : EnergySpace 0)⟫_ℂ := by
  have h := (cutoffTwoSectorCoupling g 0 Λ).adjoint_inner_right w r
  rw [cutoffTwoSectorCoupling_physicalLoad,(highEnergyEmbedding 0 2).adjoint_inner_left] at h
  exact h

private theorem se02_cutoff_source_pair (Λ : GW.Operators.PositiveCutoff) (w : OneParticleEnergySpace 0) :
    isolatedCutoffFiberSourceLoad g 0 Λ.val w =
      ⟪oneParticleEnergyEmbedding 0 w,cutoffFormFactorL2 g Λ.val Λ.property⟫_ℂ := by
  rw [←se01_cutoffSource_one g 0 Λ w,cutoffFiberSourceLoad_eq_inner,
    onePhononEnergyLift_physical,oneParticleExtraction_inclusion]

theorem se02_cutoff_adjoint_inverse_pair (Λ : GW.Operators.PositiveCutoff) (w : OneParticleEnergySpace 0) :
    ⟪oneParticleEnergyEmbedding 0 w,
      oneToHighAdjoint (cutoffFormFactorL2 g Λ.val Λ.property) (se02CutoffXHighVector e he g hg hs Λ)⟫_ℂ =
      -⟪w,(cutoffTwoSectorCoupling g 0 Λ).adjoint (cutoffGroundSourceHighEnergy e he g hg hs Λ)⟫_ℂ -
        ⟪w,cutoffEnergySchurCorrection e 0 he g hg hs Λ (cutoffGroundSourceOneEnergy e he g hg hs Λ)⟫_ℂ := by
  have hx := (se02CutoffXHighVector_physical e he g hg hs Λ).trans
    (cutoffGroundSource_high_inverse_physical e he g hg hs Λ)
  have h0 := se02_cutoff_coupling_pair g Λ w (cutoffGroundSourceHighEnergy e he g hg hs Λ)
  have h1 := se02_cutoff_coupling_pair g Λ w (cutoffGroundSourceCouplingResponseEnergy e he g hg hs Λ)
  rw [←oneToHighAdjoint_pairing (cutoffFormFactorL2 g Λ.val Λ.property) (oneParticleEnergyEmbedding 0 w)
    (se02CutoffXHighVector e he g hg hs Λ)]
  change ⟪(oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) (oneParticleEnergyEmbedding 0 w) : GW.Fock.Carrier),
    (se02CutoffXHighVector e he g hg hs Λ : GW.Fock.Carrier)⟫_ℂ = _
  rw [hx,inner_sub_right,inner_neg_right]
  calc
    _ = -⟪w,(cutoffTwoSectorCoupling g 0 Λ).adjoint (cutoffGroundSourceHighEnergy e he g hg hs Λ)⟫_ℂ -
        ⟪w,(cutoffTwoSectorCoupling g 0 Λ).adjoint (cutoffGroundSourceCouplingResponseEnergy e he g hg hs Λ)⟫_ℂ :=
      (congrArg₂ (fun a b : ℂ => -a-b) h0 h1).symm
    _ = _ := rfl

def se02CutoffLeftEnergy (Λ : GW.Operators.PositiveCutoff) : OneParticleEnergySpace 0 :=
  (1-(((1+e : ℝ) : ℂ) • onePhononMassOperator 0)-cutoffEnergySchurCorrection e 0 he g hg hs Λ)
    (cutoffGroundSourceOneEnergy e he g hg hs Λ)

def se02CutoffRightLoad (Λ : GW.Operators.PositiveCutoff) : ConjugateLoad (OneParticleEnergySpace 0) :=
  (innerSLFlip ℂ (se02CutoffRightVector e he g hg hs Λ)).comp (oneParticleEnergyEmbedding 0)

theorem se02_cutoff_dual_pairing (Λ : GW.Operators.PositiveCutoff) (w : OneParticleEnergySpace 0) :
    ⟪w,se02CutoffLeftEnergy e he g hg hs Λ⟫_ℂ = se02CutoffRightLoad e he g hg hs Λ w := by
  have hone := cutoffGroundSource_one_equation e he g hg hs Λ w
  rw [se02_cutoff_source_pair g Λ w] at hone
  have hadj := se02_cutoff_adjoint_inverse_pair e he g hg hs Λ w
  change ⟪w,se02CutoffLeftEnergy e he g hg hs Λ⟫_ℂ =
    ⟪oneParticleEnergyEmbedding 0 w,se02CutoffRightVector e he g hg hs Λ⟫_ℂ
  simp only [se02CutoffLeftEnergy,sub_apply,one_apply_eq_self,smul_apply,
    inner_sub_right,inner_smul_right,pt03_onePhononMassOperator_pairing]
  rw [se02CutoffRightVector,inner_add_right,inner_sub_right,hadj]
  push_cast
  linear_combination hone

theorem se02_cutoff_dual_identity (Λ : GW.Operators.PositiveCutoff) :
    innerSLFlip ℂ (se02CutoffLeftEnergy e he g hg hs Λ) = se02CutoffRightLoad e he g hg hs Λ := by
  apply ContinuousLinearMap.ext
  intro w
  exact se02_cutoff_dual_pairing e he g hg hs Λ w

theorem se02_cutoff_rhs_integral (Λ : GW.Operators.PositiveCutoff) (w : OneParticleEnergySpace 0) :
    Integrable (fun k => (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k)) *
      (cutoffFormFactor g Λ.val k : ℂ)*(1-cutoffThresholdKernelJ e he g hg hs Λ 0 k 0)) volume ∧
    se02CutoffRightLoad e he g hg hs Λ w =
      ∫ k, (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k)) *
        (cutoffFormFactor g Λ.val k : ℂ)*(1-cutoffThresholdKernelJ e he g hg hs Λ 0 k 0) := by
  have h := L2.integrable_inner (𝕜 := ℂ) (oneParticleEnergyEmbedding 0 w) (se02CutoffRightVector e he g hg hs Λ)
  have hp : (fun k => ⟪oneParticleEnergyEmbedding 0 w k,se02CutoffRightVector e he g hg hs Λ k⟫_ℂ) =ᵐ[volume]
      (fun k => (starRingEnd ℂ (oneParticleEnergyEmbedding 0 w k)) *
        (cutoffFormFactor g Λ.val k : ℂ)*(1-cutoffThresholdKernelJ e he g hg hs Λ 0 k 0)) := by
    filter_upwards [se02CutoffRightVector_ae e he g hg hs Λ] with k hk
    rw [hk,RCLike.inner_apply']
    ring
  refine ⟨h.congr hp,?_⟩
  change ⟪oneParticleEnergyEmbedding 0 w,se02CutoffRightVector e he g hg hs Λ⟫_ℂ = _
  rw [L2.inner_def]
  exact integral_congr_ae hp

end Froehlich
