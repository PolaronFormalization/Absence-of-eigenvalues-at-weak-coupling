import Froehlich.Nodes.PT03BoundsDiagonal
import Froehlich.Nodes.PT01InverseContinuity
import Froehlich.Nodes.RS03Smooth

set_option autoImplicit false

/-! The actual scalar diagonal terms are measurable and absolutely
integrable against two one-particle L2 functions. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

theorem cutoffThresholdDiagonal_continuous (Lambda : GW.Operators.PositiveCutoff) :
    Continuous (fun p : GW.Space => cutoffThresholdDiagonal e he g hg hs Lambda p) := by
  let v := cutoffOneParticleSource g Lambda
  have hR := cutoffAuxiliaryResolvent_continuous 1 e (by norm_num) he g hg hs Lambda
  have hi : Continuous (fun p : GW.Space =>
      ⟪v,cutoffAuxiliaryResolvent 1 e p he Lambda g hg hs v⟫_ℂ) :=
    continuous_const.inner (𝕜 := ℂ) (hR.clm_apply continuous_const)
  have heq : (fun p : GW.Space => cutoffThresholdDiagonal e he g hg hs Lambda p) =
      (fun p : GW.Space => ⟪v,cutoffAuxiliaryResolvent 1 e p he Lambda g hg hs v⟫_ℂ) := by
    funext p
    rw [cutoffThresholdDiagonal_hilbert]
    change ⟪(v : GW.Fock.Carrier),cutoffAuxiliaryExtendedResolvent 1 e p he Lambda g hg hs (v : GW.Fock.Carrier)⟫_ℂ = _
    rw [cutoffAuxiliaryExtendedResolvent_on_high]
    rfl
  rw [heq]
  exact hi

private theorem pt03_scalar_diagonal_integrable (D : GW.Space → ℂ)
    (hD : Measurable D) (B : ℝ) (hB : ∀ q, ‖D q‖ ≤ B) (f h : GW.OnePhonon) :
    Integrable (fun q => (starRingEnd ℂ) (f q)*D q*h q) volume := by
  have hmajor := (L2.integrable_inner (𝕜 := ℂ) f h).norm.const_mul B
  have hm : AEStronglyMeasurable (fun q => (starRingEnd ℂ) (f q)*D q*h q) volume :=
    ((Complex.conjCLE.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)).mul
      hD.aestronglyMeasurable).mul (Lp.aestronglyMeasurable h)
  apply hmajor.mono' hm
  exact Filter.Eventually.of_forall (fun q => by
    simp only [norm_mul,RCLike.norm_conj,RCLike.inner_apply']
    have hb := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hB q) (norm_nonneg (f q))) (norm_nonneg (h q))
    exact hb.trans_eq (by ring))

theorem cutoffThresholdDiagonal_integrable (Lambda : GW.Operators.PositiveCutoff) (f h : GW.OnePhonon) :
    Integrable (fun q => (starRingEnd ℂ) (f q)*cutoffThresholdDiagonal e he g hg hs Lambda q*h q) volume := by
  obtain ⟨C,hC,hBound⟩ := cutoffThresholdDiagonal_uniform
  exact pt03_scalar_diagonal_integrable _ (cutoffThresholdDiagonal_continuous e he g hg hs Lambda).measurable
    (C*g^2) (fun q => hBound g e he hg hs Lambda q) f h

theorem singularThresholdDiagonal_integrable (f h : GW.OnePhonon) :
    Integrable (fun q => (starRingEnd ℂ) (f q)*(-(auxiliarySelfEnergy e q he g hg hs : ℂ))*h q) volume := by
  obtain ⟨C,hC,hBound⟩ := auxiliarySelfEnergy_uniform_bound
  have hd : Continuous (fun q : GW.Space => -(auxiliarySelfEnergy e q he g hg hs : ℂ)) :=
    (Complex.continuous_ofReal.comp (auxiliarySelfEnergy_contDiff g e he hg hs).continuous).neg
  apply pt03_scalar_diagonal_integrable _ hd.measurable (C*g^2) _ f h
  intro q
  simpa only [norm_neg,Complex.norm_real,Real.norm_eq_abs] using hBound g e q he hg hs

theorem cutoffThresholdDiagonal_shift_integrable (Lambda : GW.Operators.PositiveCutoff)
    (P : GW.Space) (f h : GW.OnePhonon) :
    Integrable (fun q => (starRingEnd ℂ) (f q)*cutoffThresholdDiagonal e he g hg hs Lambda (q-P)*h q) volume := by
  obtain ⟨C,hC,hBound⟩ := cutoffThresholdDiagonal_uniform
  have hd : Continuous (fun q : GW.Space => cutoffThresholdDiagonal e he g hg hs Lambda (q-P)) :=
    (cutoffThresholdDiagonal_continuous e he g hg hs Lambda).comp (continuous_id.sub continuous_const)
  exact pt03_scalar_diagonal_integrable _ hd.measurable (C*g^2)
    (fun q => hBound g e he hg hs Lambda (q-P)) f h

theorem singularThresholdDiagonal_shift_integrable (P : GW.Space) (f h : GW.OnePhonon) :
    Integrable (fun q => (starRingEnd ℂ) (f q)*(-(auxiliarySelfEnergy e (q-P) he g hg hs : ℂ))*h q) volume := by
  obtain ⟨C,hC,hBound⟩ := auxiliarySelfEnergy_uniform_bound
  have hd : Continuous (fun q : GW.Space => -(auxiliarySelfEnergy e (q-P) he g hg hs : ℂ)) :=
    ((Complex.continuous_ofReal.comp (auxiliarySelfEnergy_contDiff g e he hg hs).continuous).neg).comp
      (continuous_id.sub continuous_const)
  apply pt03_scalar_diagonal_integrable _ hd.measurable (C*g^2) _ f h
  intro q
  simpa only [norm_neg,Complex.norm_real,Real.norm_eq_abs] using hBound g e (q-P) he hg hs

end Froehlich
