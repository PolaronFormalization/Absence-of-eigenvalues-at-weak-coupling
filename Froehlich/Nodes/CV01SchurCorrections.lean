import Froehlich.Nodes.CV01OneParticleCoordinates
import Froehlich.Nodes.UV01CorrectionError

/-! Schur corrections represented on a fixed isolated one-particle energy
space, with genuine uniform operator-norm convergence on bounded sets. -/
noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace Froehlich
attribute [local irreducible] cutoffEnergySchurCorrection singularEnergySchurCorrection
  oneParticleEnergyCoordinateChange

def energyCorrectionPullback {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : E →L[ℂ] H) (D : H →L[ℂ] H) : E →L[ℂ] E :=
  L.adjoint.comp (D.comp L)

private theorem energyCorrectionPullback_pairing {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : E →L[ℂ] H) (D : H →L[ℂ] H) (f h : E) :
    ⟪f,energyCorrectionPullback L D h⟫_ℂ=⟪L f,D (L h)⟫_ℂ :=
  L.adjoint_inner_right f (D (L h))

private theorem adjointPullback_error {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : E →L[ℂ] H) (D T : H →L[ℂ] H) :
    ‖energyCorrectionPullback L D-energyCorrectionPullback L T‖ ≤ ‖L‖^2*‖D-T‖ := by
  unfold energyCorrectionPullback
  have hid : L.adjoint.comp (D.comp L)-L.adjoint.comp (T.comp L)=L.adjoint.comp ((D-T).comp L) := by
    simp only [ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_sub]
  rw [hid]
  calc
    _ ≤ ‖L.adjoint‖*‖(D-T).comp L‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖L.adjoint‖*(‖D-T‖*‖L‖) := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.opNorm_comp_le _ _) L.adjoint.opNorm_nonneg
    _ = _ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring

def schurCutoffRateConstant (g : ℝ) : ℝ :=
  12*(Real.sqrt 2*phiMixedConstant*|g|)*(Real.sqrt 2*lyHighConstant*|g|) +
    36*(Real.sqrt 2*phiMixedConstant*|g|)^2*lyHighConstant*|g|

theorem schurCutoffRateConstant_nonneg (g : ℝ) : 0 ≤ schurCutoffRateConstant g := by
  have hc := phiMixedConstant_pos
  have hh := lyHighConstant_pos
  unfold schurCutoffRateConstant
  positivity

variable (e : ℝ) (P0 P : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2)

def cutoffCommonSchurCorrection (Λ : GW.Operators.PositiveCutoff) :
    OneParticleEnergySpace P0 →L[ℂ] OneParticleEnergySpace P0 :=
  energyCorrectionPullback (E := OneParticleEnergySpace P0) (H := OneParticleEnergySpace P) (oneParticleEnergyCoordinateChange P P0)
    (cutoffEnergySchurCorrection e P he g hg hsmall Λ)

def singularCommonSchurCorrection : OneParticleEnergySpace P0 →L[ℂ] OneParticleEnergySpace P0 :=
  energyCorrectionPullback (E := OneParticleEnergySpace P0) (H := OneParticleEnergySpace P) (oneParticleEnergyCoordinateChange P P0)
    (singularEnergySchurCorrection e P he g hg hsmall)

theorem cutoffCommonSchurCorrection_spec (Λ : GW.Operators.PositiveCutoff) (f h : OneParticleEnergySpace P0) :
    ⟪f,cutoffCommonSchurCorrection e P0 P he g hg hsmall Λ h⟫_ℂ =
      ⟪oneParticleEnergyCoordinateChange P P0 f,
        cutoffEnergySchurCorrection e P he g hg hsmall Λ (oneParticleEnergyCoordinateChange P P0 h)⟫_ℂ := by
  unfold cutoffCommonSchurCorrection
  exact energyCorrectionPullback_pairing (E := OneParticleEnergySpace P0) (H := OneParticleEnergySpace P) (oneParticleEnergyCoordinateChange P P0)
    (cutoffEnergySchurCorrection e P he g hg hsmall Λ) f h

theorem commonSchurCorrection_norm_error (Λ : GW.Operators.PositiveCutoff) (hΛ : 1 ≤ Λ.val)
    (R : ℝ) (hR : 0 ≤ R) (hdist : ‖P-P0‖ ≤ R) :
    ‖cutoffCommonSchurCorrection e P0 P he g hg hsmall Λ-singularCommonSchurCorrection e P0 P he g hg hsmall‖ ≤
      (4*(1+R^2)*schurCutoffRateConstant g)/Real.sqrt Λ.val := by
  have h1 : ‖cutoffCommonSchurCorrection e P0 P he g hg hsmall Λ-
      singularCommonSchurCorrection e P0 P he g hg hsmall‖ ≤
      ‖oneParticleEnergyCoordinateChange P P0‖^2*
        ‖cutoffEnergySchurCorrection e P he g hg hsmall Λ-singularEnergySchurCorrection e P he g hg hsmall‖ := by
    unfold cutoffCommonSchurCorrection singularCommonSchurCorrection
    exact adjointPullback_error (E := OneParticleEnergySpace P0) (H := OneParticleEnergySpace P) (oneParticleEnergyCoordinateChange P P0)
      (cutoffEnergySchurCorrection e P he g hg hsmall Λ) (singularEnergySchurCorrection e P he g hg hsmall)
  have h2 := oneParticleEnergyCoordinateChange_norm_sq P P0 R hR hdist
  have h3 := cutoffEnergySchurCorrection_error e P he g hg hsmall Λ hΛ
  exact h1.trans ((mul_le_mul h2 h3 (ContinuousLinearMap.opNorm_nonneg _)
    (by positivity)).trans_eq (by unfold schurCutoffRateConstant; ring))

include P0 in
theorem commonSchurCorrection_uniform_on_ball (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun Λ : GW.Operators.PositiveCutoff => fun P : GW.Space => cutoffCommonSchurCorrection e P0 P he g hg hsmall Λ)
      (fun P : GW.Space => singularCommonSchurCorrection e P0 P he g hg hsmall) atTop {P : GW.Space | ‖P-P0‖ ≤ R} := by
  letI : PseudoMetricSpace (OneParticleEnergySpace P0 →L[ℂ] OneParticleEnergySpace P0) :=
    ContinuousLinearMap.toPseudoMetricSpace
  have hi := (Real.continuous_sqrt.tendsto 0).comp
    ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp positiveCutoff_coe_tendsto)
  change Tendsto (fun Λ : GW.Operators.PositiveCutoff => Real.sqrt (Λ.val⁻¹)) atTop (𝓝 (Real.sqrt (0 : ℝ))) at hi
  have hr : Tendsto (fun Λ : GW.Operators.PositiveCutoff => (4*(1+R^2)*schurCutoffRateConstant g)/Real.sqrt Λ.val)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_inv,Real.sqrt_zero,div_eq_mul_inv,mul_zero] using hi.const_mul (4*(1+R^2)*schurCutoffRateConstant g)
  have hone : ∀ᶠ Λ : GW.Operators.PositiveCutoff in atTop, 1 ≤ Λ.val :=
    positiveCutoff_coe_tendsto.eventually (eventually_ge_atTop 1)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have hrate := (tendsto_order.1 hr).2 eps heps
  filter_upwards [hone,hrate] with Λ hΛ hrateΛ
  intro P hP
  change ‖-singularCommonSchurCorrection e P0 P he g hg hsmall+
    cutoffCommonSchurCorrection e P0 P he g hg hsmall Λ‖ < eps
  rw [add_comm,←sub_eq_add_neg]
  exact (commonSchurCorrection_norm_error e P0 P he g hg hsmall Λ hΛ R hR hP).trans_lt hrateΛ

end Froehlich
