import Froehlich.Nodes.FB01LiebYamazaki

/-! Source splitting-radius absorption on the actual bounded-coordinate core. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

theorem liebYamazaki_cutoff_core (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space)
    (u : boundedMomentumCore) (theta : ℝ) (ht : 0 < theta) :
    ‖cutoffInteractionForm g Λ hΛ P (coreEnergyLift P u) (coreEnergyLift P u)‖ ≤
      theta * freeEnergy P (u : GW.Fock.Carrier) +
        lyRemainderConstant * (g^2/theta + g^4/theta^3) * ‖(u : GW.Fock.Carrier)‖^2 := by
  let L := lySplittingRadius lyAbsorptionConstant g theta
  have hL1 : 1 ≤ L := lySplittingRadius_lower _ _ _
  have hL : 0 < L := zero_lt_one.trans_le hL1
  let D : ℝ := ∑ j : Fin 3, ‖coreKineticComponent P j u‖^2
  let N : ℝ := ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput (coreNumberLift u))‖^2
  let U : ℝ := ‖(u : GW.Fock.Carrier)‖^2
  let V : ℝ := ‖coreNumberLift u‖^2
  let A : ℝ := lyAbsorptionConstant*g^2*L/theta
  let B : ℝ := lyAbsorptionConstant*g^2/(theta*L)
  let R : ℝ := lyRemainderConstant*(g^2/theta+g^4/theta^3)
  let X : ℝ := ‖cutoffInteractionForm g Λ hΛ P (coreEnergyLift P u) (coreEnergyLift P u)‖
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hN : 0 ≤ N := sq_nonneg _
  have hU : 0 ≤ U := sq_nonneg _
  have hVnonneg : 0 ≤ V := sq_nonneg _
  have hC : 0 ≤ lyAbsorptionConstant := lyAbsorptionConstant_pos.le
  have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
  have hB : B ≤ theta/2 := lySplittingRadius_tail lyAbsorptionConstant g theta ht
  have hR : A+B ≤ R := lyScalarRemainder_bound lyAbsorptionConstant g theta lyAbsorptionConstant_pos.le ht
  have hV : V = U+N := by
    simpa only [coreNumberLift_embedding] using numberForm_norm_identity (coreNumberLift u)
  have hE : D+N = freeEnergy P (u : GW.Fock.Carrier) := coreKineticNumber_identity P u
  have hraw : X ≤ theta/2*N + A*U + theta/2*D + B*V := by
    by_cases hLΛ : L ≤ Λ
    · let a : ℂ := cutoffInteractionForm g Λ hΛ P (coreEnergyLift P u) (coreEnergyLift P u)
      let b : ℂ := cutoffInteractionForm g L hL P (coreEnergyLift P u) (coreEnergyLift P u)
      have hl : ‖b‖ ≤ theta/2*N + A*U := lyCutoff_low_core g L hL P u theta ht
      have hh : ‖a-b‖ ≤ theta/2*D + B*V := lyCutoff_high_young_core g L Λ hL hLΛ P u theta ht
      have htriangle : X ≤ ‖b‖+‖a-b‖ :=
        (congrArg (fun z : ℂ => ‖z‖) (show a = b+(a-b) by abel)).trans_le (norm_add_le b (a-b))
      calc
        X ≤ (theta/2*N + A*U) + (theta/2*D + B*V) := htriangle.trans (add_le_add hl hh)
        _ = _ := by ring
    · have hΛL : Λ ≤ L := (lt_of_not_ge hLΛ).le
      have hl := lyCutoff_low_core g Λ hΛ P u theta ht
      have hcoef : lyAbsorptionConstant*g^2*Λ/theta ≤ A := by
        have hm := mul_le_mul_of_nonneg_left hΛL
          (show 0 ≤ lyAbsorptionConstant*g^2/theta by positivity)
        dsimp only [A]
        convert hm using 1 <;> ring
      have hmass := mul_le_mul_of_nonneg_right hcoef hU
      have hl' : X ≤ theta/2*N + A*U := hl.trans (add_le_add (le_refl _) hmass)
      have hpad : 0 ≤ theta/2*D + B*V := add_nonneg (mul_nonneg (by positivity) hD) (mul_nonneg hBnonneg hVnonneg)
      linarith
  have hBN := mul_le_mul_of_nonneg_right hB hN
  have hDD := mul_le_mul_of_nonneg_right (show theta/2 ≤ theta by linarith) hD
  have hRU := mul_le_mul_of_nonneg_right hR hU
  rw [hV] at hraw
  change X ≤ theta * freeEnergy P (u : GW.Fock.Carrier) + R*U
  rw [← hE]
  nlinarith

theorem liebYamazaki_cutoff_core_small (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space)
    (u : boundedMomentumCore) (theta : ℝ) (ht : 0 < theta) (hg : |g| ≤ theta) :
    ‖cutoffInteractionForm g Λ hΛ P (coreEnergyLift P u) (coreEnergyLift P u)‖ ≤
      theta * freeEnergy P (u : GW.Fock.Carrier) +
        (2*lyRemainderConstant*g^2/theta) * ‖(u : GW.Fock.Carrier)‖^2 := by
  have hg2 : g^2 ≤ theta^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg g) ht.le).mpr hg
  have hfrac : g^4/theta^3 ≤ g^2/theta := by
    apply (div_le_iff₀ (pow_pos ht 3)).mpr
    calc
      g^4 = g^2*g^2 := by ring
      _ ≤ g^2*theta^2 := mul_le_mul_of_nonneg_left hg2 (sq_nonneg g)
      _ = (g^2/theta)*theta^3 := by field_simp [ne_of_gt ht] <;> ring
  have hrem : lyRemainderConstant*(g^2/theta+g^4/theta^3) ≤ 2*lyRemainderConstant*g^2/theta := by
    calc
      _ ≤ lyRemainderConstant*(g^2/theta+g^2/theta) :=
        mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hfrac) lyRemainderConstant_pos.le
      _ = _ := by ring
  apply (liebYamazaki_cutoff_core g Λ hΛ P u theta ht).trans
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hrem (sq_nonneg _))

end Froehlich
