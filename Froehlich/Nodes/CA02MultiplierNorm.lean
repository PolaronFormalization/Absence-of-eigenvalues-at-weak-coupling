import Froehlich.Nodes.FC01Multipliers

set_option autoImplicit false

/-! Native Lp and lp monotonicity turn uniform pointwise multiplier
remainders into bounds on the actual canonical Fock operators. No second
Fock carrier or multiplier construction is introduced. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Froehlich

theorem fockOperator_norm_le_of_ae_sector_norm
    (T : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ (u : GW.Fock.Carrier) (n : ℕ), ∀ᵐ K ∂GW.Fock.sectorMeasure n,
      ‖physicalSector n ((T u) n) K‖ ≤ C*‖physicalSector n (u n) K‖) : ‖T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound T hC
  intro u
  have hsector : ∀ n, ‖(T u) n‖ ≤ C*‖u n‖ := by
    intro n
    have hs : ‖physicalSector n ((T u) n)‖ ≤ C*‖physicalSector n (u n)‖ :=
      MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul (hT u n)
    simpa only [LinearIsometry.norm_map] using hs
  have hp : ‖T u‖ ≤ ‖(C : ℂ) • u‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro n
    change ‖(T u) n‖ ≤ ‖(C : ℂ) • u n‖
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC]
    exact hsector n
  simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC] using hp

theorem fockOperator_norm_le_of_ae_multiplier
    (T : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier)
    (m : ∀ n, GW.Fock.Coordinates n → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n K, ‖m n K‖ ≤ C)
    (hT : ∀ (u : GW.Fock.Carrier) (n : ℕ),
      (fun K => m n K • physicalSector n (u n) K) =ᵐ[GW.Fock.sectorMeasure n]
        physicalSector n ((T u) n)) : ‖T‖ ≤ C := by
  apply fockOperator_norm_le_of_ae_sector_norm T C hC
  intro u n
  filter_upwards [hT u n] with K hK
  rw [← hK,norm_smul]
  exact mul_le_mul_of_nonneg_right (hbound n K) (norm_nonneg _)

end Froehlich
