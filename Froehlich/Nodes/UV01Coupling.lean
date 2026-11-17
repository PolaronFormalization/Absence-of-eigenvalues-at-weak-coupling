import Froehlich.Nodes.SP03Coupling
import Froehlich.Nodes.UV01CutoffMixed

/-! Literal cutoff one-to-high form couplings on the same original graphs. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def cutoffTwoSectorCouplingLoad (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) (f : OneParticleEnergySpace P) :
    ConjugateLoad (HighEnergySpace P 2) :=
  ((cutoffInteractionForm g Λ.val Λ.property P).flip (onePhononEnergyLift P f)).comp (HighEnergySpace P 2).subtypeL

theorem cutoffTwoSectorCouplingLoad_apply (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (f : OneParticleEnergySpace P) (w : HighEnergySpace P 2) :
    cutoffTwoSectorCouplingLoad g P Λ f w = cutoffInteractionForm g Λ.val Λ.property P w (onePhononEnergyLift P f) := rfl

def cutoffTwoSectorCoupling (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) :
    OneParticleEnergySpace P →L[ℂ] HighEnergySpace P 2 :=
  (HighEnergySpace P 2).subtypeL.adjoint.comp
    ((formRepresentative (cutoffInteractionForm g Λ.val Λ.property P)).comp (onePhononEnergyLift P))

theorem cutoffTwoSectorCoupling_spec (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (f : OneParticleEnergySpace P) (w : HighEnergySpace P 2) :
    ⟪w,cutoffTwoSectorCoupling g P Λ f⟫_ℂ = cutoffTwoSectorCouplingLoad g P Λ f w := by
  rw [cutoffTwoSectorCoupling,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    (HighEnergySpace P 2).subtypeL.adjoint_inner_right]
  exact (formRepresentative_spec (cutoffInteractionForm g Λ.val Λ.property P) w (onePhononEnergyLift P f)).symm

theorem cutoffTwoSectorCoupling_eq_loadRiesz (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) (f : OneParticleEnergySpace P) :
    cutoffTwoSectorCoupling g P Λ f = loadRiesz (cutoffTwoSectorCouplingLoad g P Λ f) := by
  apply loadRiesz_unique
  intro w
  exact (cutoffTwoSectorCoupling_spec g P Λ f w).symm

theorem cutoffTwoSectorCouplingLoad_norm_le (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) (hg : |g| ≤ 1)
    (f : OneParticleEnergySpace P) :
    ‖cutoffTwoSectorCouplingLoad g P Λ f‖ ≤ Real.sqrt 2 * phiMixedConstant * |g| * ‖f‖ := by
  have hc := phiMixedConstant_pos
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [cutoffTwoSectorCouplingLoad_apply]
  have h := cutoffInteraction_mixed_small g Λ.val Λ.property P (w : EnergySpace P) (onePhononEnergyLift P f) hg
  calc
    _ ≤ phiMixedConstant * |g| * ‖w‖ * ‖onePhononEnergyLift P f‖ := h
    _ ≤ phiMixedConstant * |g| * ‖w‖ * (Real.sqrt 2 * ‖f‖) :=
      mul_le_mul_of_nonneg_left (onePhononEnergyLift_norm_le P f) (by positivity)
    _ = _ := by ring

theorem cutoffTwoSectorCoupling_norm_le (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) (hg : |g| ≤ 1) :
    ‖cutoffTwoSectorCoupling g P Λ‖ ≤ Real.sqrt 2 * phiMixedConstant * |g| := by
  have hc := phiMixedConstant_pos
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [cutoffTwoSectorCoupling_eq_loadRiesz,loadRiesz_norm]
  exact cutoffTwoSectorCouplingLoad_norm_le g P Λ hg f

theorem cutoffTwoSectorCouplingLoad_error (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (hΛ : 1 ≤ Λ.val) (f : OneParticleEnergySpace P) :
    ‖cutoffTwoSectorCouplingLoad g P Λ f - twoSectorCouplingLoad g P f‖ ≤
      (Real.sqrt 2*lyHighConstant*|g|/Real.sqrt Λ.val)*‖f‖ := by
  have hc := lyHighConstant_pos
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  have h := fb02_tail_mixed g Λ.val hΛ P (w : EnergySpace P) (onePhononEnergyLift P f)
  have hd : ‖(cutoffTwoSectorCouplingLoad g P Λ f-twoSectorCouplingLoad g P f) w‖ =
      ‖(singularInteraction g P-cutoffInteractionForm g Λ.val Λ.property P) w (onePhononEnergyLift P f)‖ := by
    change ‖cutoffInteractionForm g Λ.val Λ.property P w (onePhononEnergyLift P f)-
      singularInteraction g P w (onePhononEnergyLift P f)‖ =
      ‖singularInteraction g P w (onePhononEnergyLift P f)-
        cutoffInteractionForm g Λ.val Λ.property P w (onePhononEnergyLift P f)‖
    exact norm_sub_rev _ _
  rw [hd]
  calc
    _ ≤ (lyHighConstant*|g|/Real.sqrt Λ.val)*‖w‖*‖onePhononEnergyLift P f‖ := h
    _ ≤ (lyHighConstant*|g|/Real.sqrt Λ.val)*‖w‖*(Real.sqrt 2*‖f‖) :=
      mul_le_mul_of_nonneg_left (onePhononEnergyLift_norm_le P f) (by positivity)
    _ = _ := by ring

theorem cutoffTwoSectorCoupling_error (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (hΛ : 1 ≤ Λ.val) :
    ‖cutoffTwoSectorCoupling g P Λ-twoSectorCoupling g P‖ ≤
      Real.sqrt 2*lyHighConstant*|g|/Real.sqrt Λ.val := by
  have hc := lyHighConstant_pos
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖cutoffTwoSectorCoupling g P Λ f-twoSectorCoupling g P f‖ ≤ _
  rw [cutoffTwoSectorCoupling_eq_loadRiesz,twoSectorCoupling_eq_loadRiesz]
  have hm := (loadRieszLinearIsometry (V := HighEnergySpace P 2)).map_sub
    (cutoffTwoSectorCouplingLoad g P Λ f) (twoSectorCouplingLoad g P f)
  change loadRiesz (cutoffTwoSectorCouplingLoad g P Λ f-twoSectorCouplingLoad g P f) =
    loadRiesz (cutoffTwoSectorCouplingLoad g P Λ f)-loadRiesz (twoSectorCouplingLoad g P f) at hm
  rw [←hm,loadRiesz_norm]
  exact cutoffTwoSectorCouplingLoad_error g P Λ hΛ f

end Froehlich
