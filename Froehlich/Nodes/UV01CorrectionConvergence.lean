import Froehlich.Nodes.UV01Coupling
import Froehlich.Nodes.UV01PhysicalResolvent
import Froehlich.Nodes.FB02VacuumColumn

/-! Actual original-energy one-to-high Schur products at the same e. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich
local instance uvCorrectionHighNormedGroup (P : GW.Space) : NormedAddCommGroup (HighEnergySpace P 2) :=
  Submodule.normedAddCommGroup (HighEnergySpace P 2)
local instance uvCorrectionCouplingNormedGroup (P : GW.Space) :
    NormedAddCommGroup (OneParticleEnergySpace P →L[ℂ] HighEnergySpace P 2) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance uvCorrectionInverseNormedGroup (P : GW.Space) :
    NormedAddCommGroup (HighEnergySpace P 2 →L[ℂ] HighEnergySpace P 2) :=
  ContinuousLinearMap.toNormedAddCommGroup

theorem cutoffNormRate_tendsto {V : Type*} [NormedAddCommGroup V]
    (f : GW.Operators.PositiveCutoff → V) (v : V) (C : ℝ)
    (h : ∀ Λ : GW.Operators.PositiveCutoff, 1 ≤ Λ.val → ‖f Λ-v‖ ≤ C/Real.sqrt Λ.val) :
    Tendsto f atTop (𝓝 v) := by
  have hi := (Real.continuous_sqrt.tendsto 0).comp
    ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp positiveCutoff_coe_tendsto)
  change Tendsto (fun Λ : GW.Operators.PositiveCutoff => Real.sqrt (Λ.val⁻¹)) atTop (𝓝 (Real.sqrt (0 : ℝ))) at hi
  have ht : Tendsto (fun Λ : GW.Operators.PositiveCutoff => C/Real.sqrt Λ.val) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_inv,Real.sqrt_zero,div_eq_mul_inv,mul_zero] using hi.const_mul C
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun Λ => norm_nonneg (f Λ-v))) _ ht
  exact (positiveCutoff_coe_tendsto.eventually (eventually_ge_atTop 1)).mono (fun Λ hΛ => h Λ hΛ)

theorem cutoffTwoSectorCoupling_tendsto (g : ℝ) (P : GW.Space) :
    Tendsto (cutoffTwoSectorCoupling g P) atTop (𝓝 (twoSectorCoupling g P)) :=
  cutoffNormRate_tendsto _ _ (Real.sqrt 2*lyHighConstant*|g|) (cutoffTwoSectorCoupling_error g P)

variable (e : ℝ) (P : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2)

def cutoffTwoSectorReferenceInverse (Λ : GW.Operators.PositiveCutoff) :
    HighEnergySpace P 2 →L[ℂ] HighEnergySpace P 2 := by
  simpa only [neg_neg] using! cutoffAuxiliaryEnergyInverse 2 e (-P) (by norm_num) he g hg hsmall Λ

def singularTwoSectorReferenceInverse : HighEnergySpace P 2 →L[ℂ] HighEnergySpace P 2 := by
  simpa only [neg_neg] using! auxiliaryCompressedEnergyInverse 2 e (-P) (by norm_num) he g hg hsmall

def cutoffEnergySchurCorrection (Λ : GW.Operators.PositiveCutoff) :
    OneParticleEnergySpace P →L[ℂ] OneParticleEnergySpace P :=
  (cutoffTwoSectorCoupling g P Λ).adjoint.comp
    ((cutoffTwoSectorReferenceInverse e P he g hg hsmall Λ).comp
      (cutoffTwoSectorCoupling g P Λ))

def singularEnergySchurCorrection : OneParticleEnergySpace P →L[ℂ] OneParticleEnergySpace P :=
  (twoSectorCoupling g P).adjoint.comp
    ((singularTwoSectorReferenceInverse e P he g hg hsmall).comp
      (twoSectorCoupling g P))

end Froehlich
