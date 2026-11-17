import Froehlich.Nodes.FB01CommutatorForm
import Froehlich.Nodes.FB01HighFactors
import Froehlich.Nodes.FB01Linearity
import Froehlich.Nodes.FB01CoreForms

/-! The finite-cutoff high-momentum estimate on the canonical core. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

def lyHighConstant : ℝ := 4 * Real.sqrt (42 * GW.Model.unitBallVolume)

theorem lyHighConstant_pos : 0 < lyHighConstant := by
  unfold lyHighConstant
  exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (mul_pos (by norm_num) GW.Model.unitBallVolume_pos))

theorem coreSkewField_bound (f : GW.OnePhonon) (u : boundedMomentumCore) :
    ‖coreSkewField f u‖ ≤ 2 * ‖f‖ * ‖coreNumberLift u‖ := by
  have ha : ‖annihilationRestriction f (coreNumberLift u)‖ ≤ ‖f‖ * ‖coreNumberLift u‖ :=
    ((annihilationRestriction f).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (annihilationRestriction_opNorm f) (norm_nonneg _))
  have hc : ‖creationRestriction f (coreNumberLift u)‖ ≤ ‖f‖ * ‖coreNumberLift u‖ :=
    ((creationRestriction f).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (creationRestriction_opNorm f) (norm_nonneg _))
  have htriangle : ‖coreSkewField f u‖ ≤ ‖creationRestriction f (coreNumberLift u)‖ +
      ‖annihilationRestriction f (coreNumberLift u)‖ :=
    norm_sub_le (creationRestriction f (coreNumberLift u)) (annihilationRestriction f (coreNumberLift u))
  exact htriangle.trans ((add_le_add hc ha).trans_eq (by ring))

theorem lyVector_sum_sqrt_bound (g L Λ : ℝ) (hL : 0 < L) :
    Real.sqrt (∑ j : Fin 3, ‖lyVectorL2 g L Λ hL j‖^2) ≤
      Real.sqrt (42 * GW.Model.unitBallVolume) * |g| / Real.sqrt L := by
  have hc : 0 ≤ 42 * GW.Model.unitBallVolume := mul_nonneg (by norm_num) GW.Model.unitBallVolume_pos.le
  have h := Real.sqrt_le_sqrt (lyVectorL2_sum_norm_sq g L Λ hL)
  simpa only [Real.sqrt_div (mul_nonneg hc (sq_nonneg g)),Real.sqrt_mul hc,Real.sqrt_sq_eq_abs] using h

theorem lyHighPairing_bound (g L Λ : ℝ) (hL : 0 < L) (P : GW.Space) (u : boundedMomentumCore) :
    |∑ j : Fin 3, 2 * (⟪coreKineticComponent P j u,coreSkewField (lyVectorL2 g L Λ hL j) u⟫_ℂ).re| ≤
      lyHighConstant * |g| / Real.sqrt L *
        Real.sqrt (∑ j : Fin 3, ‖coreKineticComponent P j u‖^2) * ‖coreNumberLift u‖ := by
  have hterm (j : Fin 3) :
      |2 * (⟪coreKineticComponent P j u,coreSkewField (lyVectorL2 g L Λ hL j) u⟫_ℂ).re| ≤
        4 * ‖coreKineticComponent P j u‖ * ‖lyVectorL2 g L Λ hL j‖ * ‖coreNumberLift u‖ := by
    have hi := (Complex.abs_re_le_norm
      ⟪coreKineticComponent P j u,coreSkewField (lyVectorL2 g L Λ hL j) u⟫_ℂ).trans
        (norm_inner_le_norm _ _)
    calc
      _ = 2 * |(⟪coreKineticComponent P j u,coreSkewField (lyVectorL2 g L Λ hL j) u⟫_ℂ).re| := by
        rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * (‖coreKineticComponent P j u‖ * ‖coreSkewField (lyVectorL2 g L Λ hL j) u‖) :=
        mul_le_mul_of_nonneg_left hi (by norm_num)
      _ = (2 * ‖coreKineticComponent P j u‖) * ‖coreSkewField (lyVectorL2 g L Λ hL j) u‖ := by ring
      _ ≤ (2 * ‖coreKineticComponent P j u‖) *
          (2 * ‖lyVectorL2 g L Λ hL j‖ * ‖coreNumberLift u‖) :=
        mul_le_mul_of_nonneg_left (coreSkewField_bound _ u) (by positivity)
      _ = _ := by ring
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun j : Fin 3 => ‖coreKineticComponent P j u‖) (fun j : Fin 3 => ‖lyVectorL2 g L Λ hL j‖)
  calc
    _ ≤ ∑ j : Fin 3, |2 * (⟪coreKineticComponent P j u,coreSkewField (lyVectorL2 g L Λ hL j) u⟫_ℂ).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, 4 * ‖coreKineticComponent P j u‖ * ‖lyVectorL2 g L Λ hL j‖ * ‖coreNumberLift u‖ :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = 4 * (∑ j : Fin 3, ‖coreKineticComponent P j u‖ * ‖lyVectorL2 g L Λ hL j‖) * ‖coreNumberLift u‖ := by
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ 4 * (Real.sqrt (∑ j : Fin 3, ‖coreKineticComponent P j u‖^2) *
        Real.sqrt (∑ j : Fin 3, ‖lyVectorL2 g L Λ hL j‖^2)) * ‖coreNumberLift u‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCS (by norm_num)) (norm_nonneg _)
    _ ≤ 4 * (Real.sqrt (∑ j : Fin 3, ‖coreKineticComponent P j u‖^2) *
        (Real.sqrt (42 * GW.Model.unitBallVolume) * |g| / Real.sqrt L)) * ‖coreNumberLift u‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
      exact mul_le_mul_of_nonneg_left (lyVector_sum_sqrt_bound g L Λ hL) (Real.sqrt_nonneg _)
    _ = _ := by unfold lyHighConstant; ring

theorem lyHighForm_core_identity (g L Λ : ℝ) (hL : 0 < L) (hLΛ : L ≤ Λ)
    (P : GW.Space) (u : boundedMomentumCore) (S : ℕ) (hSpos : 1 ≤ S)
    (hS : max 1 Λ ≤ (S : ℝ)) :
    (cutoffInteractionForm g Λ (hL.trans_le hLΛ) P (coreEnergyLift P u) (coreEnergyLift P u) -
      cutoffInteractionForm g L hL P (coreEnergyLift P u) (coreEnergyLift P u)).re =
        ∑ j : Fin 3, 2 * (⟪coreKineticComponent P j u,coreSkewField (lyVectorL2 g L Λ hL j) u⟫_ℂ).re := by
  let F := energyInteractionAddHom P
  have he : cutoffInteractionForm g Λ (hL.trans_le hLΛ) P - cutoffInteractionForm g L hL P =
      ∑ j : Fin 3, boundedEnergyInteraction P (momentumSmearing j S (lyVectorL2 g L Λ hL j)) := by
    calc
      _ = F (cutoffFormFactorL2 g Λ (hL.trans_le hLΛ) - cutoffFormFactorL2 g L hL) := by
        change F (cutoffFormFactorL2 g Λ (hL.trans_le hLΛ)) - F (cutoffFormFactorL2 g L hL) = _
        exact (map_sub F _ _).symm
      _ = F (∑ j : Fin 3, momentumSmearing j S (lyVectorL2 g L Λ hL j)) :=
        congrArg F (lyVector_momentumSmearing_sum g L Λ hL hLΛ S hS).symm
      _ = _ := map_sum F _ _
  have heval := congrArg (fun Q : GW.Analysis.BoundedForm (EnergySpace P) =>
    (Q (coreEnergyLift P u) (coreEnergyLift P u)).re) he
  simp only [sub_apply,sum_apply,Complex.re_sum] at heval
  apply heval.trans
  apply Finset.sum_congr rfl
  intro j _
  rw [boundedEnergyInteraction_core_apply]
  exact momentum_field_commutator_form P j S hSpos (lyVectorL2 g L Λ hL j)
    (lyVectorL2_support_nat g L Λ hL S hS j) u

theorem lyHighForm_core_re_bound (g L Λ : ℝ) (hL : 0 < L) (hLΛ : L ≤ Λ)
    (P : GW.Space) (u : boundedMomentumCore) :
    |(cutoffInteractionForm g Λ (hL.trans_le hLΛ) P (coreEnergyLift P u) (coreEnergyLift P u) -
      cutoffInteractionForm g L hL P (coreEnergyLift P u) (coreEnergyLift P u)).re| ≤
      lyHighConstant * |g| / Real.sqrt L *
        Real.sqrt (∑ j : Fin 3, ‖coreKineticComponent P j u‖^2) * ‖coreNumberLift u‖ := by
  obtain ⟨S,hS⟩ := exists_nat_ge (max 1 Λ)
  have hSpos : 1 ≤ S := by exact_mod_cast ((le_max_left 1 Λ).trans hS)
  rw [lyHighForm_core_identity g L Λ hL hLΛ P u S hSpos hS]
  exact lyHighPairing_bound g L Λ hL P u

theorem lyHighForm_core_bound (g L Λ : ℝ) (hL : 0 < L) (hLΛ : L ≤ Λ)
    (P : GW.Space) (u : boundedMomentumCore) :
    ‖cutoffInteractionForm g Λ (hL.trans_le hLΛ) P (coreEnergyLift P u) (coreEnergyLift P u) -
      cutoffInteractionForm g L hL P (coreEnergyLift P u) (coreEnergyLift P u)‖ ≤
      lyHighConstant * |g| / Real.sqrt L *
        Real.sqrt (∑ j : Fin 3, ‖coreKineticComponent P j u‖^2) * ‖coreNumberLift u‖ := by
  let z : ℂ := cutoffInteractionForm g Λ (hL.trans_le hLΛ) P (coreEnergyLift P u) (coreEnergyLift P u) -
    cutoffInteractionForm g L hL P (coreEnergyLift P u) (coreEnergyLift P u)
  have hz : z = star z := by
    dsimp [z]
    rw [map_sub]
    exact congrArg₂ (fun a b : ℂ => a-b)
      (cutoffInteractionForm_hermitian g Λ (hL.trans_le hLΛ) P (coreEnergyLift P u) (coreEnergyLift P u))
      (cutoffInteractionForm_hermitian g L hL P (coreEnergyLift P u) (coreEnergyLift P u))
  have him : z.im = 0 := by
    have hi := congrArg Complex.im hz
    simp only [Complex.star_def,Complex.conj_im] at hi
    linarith
  have he : z = (z.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using him
  calc
    _ = |z.re| := by
      change ‖z‖ = _
      rw [he,Complex.norm_real,Real.norm_eq_abs]
      simp only [Complex.ofReal_re]
    _ ≤ _ := lyHighForm_core_re_bound g L Λ hL hLΛ P u

end Froehlich
