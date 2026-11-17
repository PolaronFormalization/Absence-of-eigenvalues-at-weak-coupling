import Froehlich.Nodes.CA02MultiplierNorm

set_option autoImplicit false

/-! The same native Lp/lp estimate in actual isometric coordinates.
This applies to canonical high-sector inclusions and fixed weighted
coordinate isometries without introducing another physical carrier. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Froehlich

theorem fock_norm_le_mul_norm_of_ae_sector_norm
    (u v : GW.Fock.Carrier) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, ∀ᵐ K ∂GW.Fock.sectorMeasure n,
      ‖physicalSector n (v n) K‖ ≤ C*‖physicalSector n (u n) K‖) : ‖v‖ ≤ C*‖u‖ := by
  have hsector : ∀ n, ‖v n‖ ≤ C*‖u n‖ := by
    intro n
    have hs : ‖physicalSector n (v n)‖ ≤ C*‖physicalSector n (u n)‖ :=
      MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul (h n)
    simpa only [LinearIsometry.norm_map] using hs
  have hp : ‖v‖ ≤ ‖(C : ℂ) • u‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro n
    change ‖v n‖ ≤ ‖(C : ℂ) • u n‖
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC]
    exact hsector n
  simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC] using hp

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem operator_norm_le_of_ae_fock_coordinates
    (eU : U →ₗᵢ[ℂ] GW.Fock.Carrier) (eV : V →ₗᵢ[ℂ] GW.Fock.Carrier)
    (T : U →L[ℂ] V) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ u : U, ∀ n : ℕ, ∀ᵐ K ∂GW.Fock.sectorMeasure n,
      ‖physicalSector n (eV (T u) n) K‖ ≤ C*‖physicalSector n (eU u n) K‖) : ‖T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound T hC
  intro u
  have h := fock_norm_le_mul_norm_of_ae_sector_norm (eU u) (eV (T u)) C hC (hT u)
  simpa only [LinearIsometry.norm_map] using h

theorem operator_norm_le_of_ae_multiplier_coordinates
    (eU : U →ₗᵢ[ℂ] GW.Fock.Carrier) (eV : V →ₗᵢ[ℂ] GW.Fock.Carrier)
    (T : U →L[ℂ] V) (m : ∀ n, GW.Fock.Coordinates n → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n K, ‖m n K‖ ≤ C)
    (hT : ∀ (u : U) (n : ℕ),
      (fun K => m n K • physicalSector n (eU u n) K) =ᵐ[GW.Fock.sectorMeasure n]
        physicalSector n (eV (T u) n)) : ‖T‖ ≤ C := by
  apply operator_norm_le_of_ae_fock_coordinates eU eV T C hC
  intro u n
  filter_upwards [hT u n] with K hK
  rw [← hK,norm_smul]
  exact mul_le_mul_of_nonneg_right (hbound n K) (norm_nonneg _)

end Froehlich
