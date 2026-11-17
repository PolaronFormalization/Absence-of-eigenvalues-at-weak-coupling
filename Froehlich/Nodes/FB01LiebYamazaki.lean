import Froehlich.Nodes.FB01LowBound
import Froehlich.Nodes.FB01HighBound
import Froehlich.Nodes.FB01KineticIdentity
import Froehlich.Nodes.FB01Optimization

/-! Finite-cutoff Lieb--Yamazaki on the actual canonical core. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

def lyAbsorptionConstant : ℝ := max (14 * GW.Model.unitBallVolume) (lyHighConstant^2 / 2)
def lyRemainderConstant : ℝ := lyScalarRemainderConstant lyAbsorptionConstant

theorem lyAbsorptionConstant_pos : 0 < lyAbsorptionConstant :=
  (mul_pos (by norm_num) GW.Model.unitBallVolume_pos).trans_le (le_max_left _ _)

theorem lyRemainderConstant_pos : 0 < lyRemainderConstant :=
  lyScalarRemainderConstant_pos _ lyAbsorptionConstant_pos.le

theorem lyHighYoung_scalar (H g L theta D N : ℝ) (hL : 0 < L) (ht : 0 < theta) (hD : 0 ≤ D) :
    H * |g| / Real.sqrt L * Real.sqrt D * N ≤
      theta/2 * D + H^2 * g^2 / (2*theta*L) * N^2 := by
  have hy := two_mul_le_add_mul_sq (a := Real.sqrt D)
    (b := H * |g| / (2 * Real.sqrt L) * N) (show 0 < theta/2 by positivity)
  have he : theta/2 * (Real.sqrt D)^2 + (theta/2)⁻¹ * (H * |g| / (2 * Real.sqrt L) * N)^2 =
      theta/2 * D + H^2 * g^2 / (2*theta*L) * N^2 := by
    rw [Real.sq_sqrt hD]
    simp only [mul_pow,div_pow,sq_abs,Real.sq_sqrt hL.le]
    field_simp [ne_of_gt ht,ne_of_gt hL]
    <;> ring
  calc
    _ = 2 * Real.sqrt D * (H * |g| / (2 * Real.sqrt L) * N) := by ring
    _ ≤ _ := hy.trans_eq he

theorem lyCutoff_low_core (g L : ℝ) (hL : 0 < L) (P : GW.Space)
    (u : boundedMomentumCore) (theta : ℝ) (ht : 0 < theta) :
    ‖cutoffInteractionForm g L hL P (coreEnergyLift P u) (coreEnergyLift P u)‖ ≤
      theta/2 * ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput (coreNumberLift u))‖^2 +
        (lyAbsorptionConstant*g^2*L/theta) * ‖(u : GW.Fock.Carrier)‖^2 := by
  have h := cutoffInteraction_low_bound g L hL P (coreEnergyLift P u) theta ht
  rw [coreEnergyNumberCoordinates_eq,coreEnergyLift_embedding] at h
  apply h.trans
  apply add_le_add (le_refl _)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_right (le_max_left (14*GW.Model.unitBallVolume) (lyHighConstant^2/2))
    (show 0 ≤ g^2*L/theta by positivity)
  unfold lyAbsorptionConstant
  convert hm using 1 <;> ring

theorem lyCutoff_high_young_core (g L Λ : ℝ) (hL : 0 < L) (hLΛ : L ≤ Λ)
    (P : GW.Space) (u : boundedMomentumCore) (theta : ℝ) (ht : 0 < theta) :
    ‖cutoffInteractionForm g Λ (hL.trans_le hLΛ) P (coreEnergyLift P u) (coreEnergyLift P u) -
      cutoffInteractionForm g L hL P (coreEnergyLift P u) (coreEnergyLift P u)‖ ≤
      theta/2 * (∑ j : Fin 3, ‖coreKineticComponent P j u‖^2) +
        (lyAbsorptionConstant*g^2/(theta*L)) * ‖coreNumberLift u‖^2 := by
  have hy := lyHighYoung_scalar lyHighConstant g L theta
    (∑ j : Fin 3, ‖coreKineticComponent P j u‖^2) ‖coreNumberLift u‖ hL ht
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  apply (lyHighForm_core_bound g L Λ hL hLΛ P u).trans (hy.trans _)
  apply add_le_add (le_refl _)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_right (le_max_right (14*GW.Model.unitBallVolume) (lyHighConstant^2/2))
    (show 0 ≤ g^2/(theta*L) by positivity)
  unfold lyAbsorptionConstant
  convert hm using 1 <;> ring

end Froehlich
