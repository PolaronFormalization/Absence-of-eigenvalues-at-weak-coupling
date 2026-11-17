import Froehlich.Nodes.FB01Kinetic

/-! Actual shifted momentum domains and actions on the full energy space. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

def energyKineticSymbol (P : GW.Space) (a : Fin 3) (n : ℕ) (K : GW.Fock.Coordinates n) : ℝ :=
  totalMomentum n K a - P a

def energyKineticRatio (P : GW.Space) (a : Fin 3) (n : ℕ) (K : GW.Fock.Coordinates n) : ℝ :=
  energyKineticSymbol P a n K / energyWeight P n K

theorem energyKineticSymbol_measurable (P : GW.Space) (a : Fin 3) (n : ℕ) :
    Measurable (energyKineticSymbol P a n) :=
  ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) a).measurable.comp
    (totalMomentum_measurable n)).sub measurable_const

theorem energyKineticRatio_measurable (P : GW.Space) (a : Fin 3) (n : ℕ) :
    Measurable (energyKineticRatio P a n) :=
  (energyKineticSymbol_measurable P a n).div (energyWeight_measurable P n)

theorem energyKineticSymbol_le_weight (P : GW.Space) (a : Fin 3) (n : ℕ)
    (K : GW.Fock.Coordinates n) : |energyKineticSymbol P a n K| ≤ energyWeight P n K := by
  have hc : |totalMomentum n K a-P a| ≤ ‖totalMomentum n K-P‖ := by
    simpa only [PiLp.sub_apply,Real.norm_eq_abs] using PiLp.norm_apply_le (totalMomentum n K-P) a
  have hw : ‖totalMomentum n K-P‖ ≤ energyWeight P n K := by
    apply (sq_le_sq₀ (norm_nonneg _) (zero_le_one.trans (energyWeight_ge_one P n K))).mp
    rw [energyWeight_sq]
    unfold freeSymbol
    linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  exact hc.trans hw

theorem energyKineticRatio_bound (P : GW.Space) (a : Fin 3) (n : ℕ)
    (K : GW.Fock.Coordinates n) : |energyKineticRatio P a n K| ≤ 1 := by
  rw [energyKineticRatio,abs_div,abs_of_nonneg (zero_le_one.trans (energyWeight_ge_one P n K))]
  exact (div_le_one (zero_lt_one.trans_le (energyWeight_ge_one P n K))).mpr
    (energyKineticSymbol_le_weight P a n K)

theorem energyKineticRatio_permutation (P : GW.Space) (a : Fin 3) (n : ℕ)
    (τ : Equiv.Perm (Fin n)) (K : GW.Fock.Coordinates n) :
    energyKineticRatio P a n (fun i => K (τ i)) = energyKineticRatio P a n K := by
  simp only [energyKineticRatio,energyKineticSymbol,totalMomentum_permutation,energyWeight_permutation]

theorem energyKineticRatio_zero (P : GW.Space) (a : Fin 3) (K : GW.Fock.Coordinates 0) :
    energyKineticRatio P a 0 K = -P a / Real.sqrt (1+‖P‖^2) := by
  rw [energyKineticRatio,energyKineticSymbol,energyWeight_zero]
  simp [totalMomentum]

def energyKineticSector (P : GW.Space) (a : Fin 3) :
    ∀ n, GW.Fock.Sector n →L[ℂ] GW.Fock.Sector n
  | 0 => (energyKineticRatio P a 0 0 : ℂ) • ContinuousLinearMap.id ℂ ℂ
  | n+1 => boundedSymmetricMultiplier (n+1) (fun K => (energyKineticRatio P a (n+1) K : ℂ))
      (Complex.continuous_ofReal.measurable.comp (energyKineticRatio_measurable P a (n+1)))
      (C := (1 : ℝ)) (fun K => by
        simpa only [Complex.norm_real,Real.norm_eq_abs] using energyKineticRatio_bound P a (n+1) K)
      (fun τ K => congrArg (fun x : ℝ => (x : ℂ)) (energyKineticRatio_permutation P a (n+1) τ K))

theorem energyKineticSector_norm (P : GW.Space) (a : Fin 3) (n : ℕ) : ‖energyKineticSector P a n‖ ≤ 1 := by
  cases n with
  | zero =>
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖(energyKineticRatio P a 0 0 : ℂ) • z‖ ≤ 1 * ‖z‖
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (energyKineticRatio_bound P a 0 0) (norm_nonneg z)
  | succ n =>
    exact boundedSymmetricMultiplier_norm (n+1) _
      (Complex.continuous_ofReal.measurable.comp (energyKineticRatio_measurable P a (n+1))) zero_le_one
      (fun K => by simpa only [Function.comp_apply,Complex.norm_real,Real.norm_eq_abs] using energyKineticRatio_bound P a (n+1) K)
      (fun τ K => congrArg (fun x : ℝ => (x : ℂ)) (energyKineticRatio_permutation P a (n+1) τ K))

theorem energyKineticSector_ae (P : GW.Space) (a : Fin 3) (n : ℕ) (u : GW.Fock.Sector n) :
    (fun K => (energyKineticRatio P a n K : ℂ) • physicalSector n u K) =ᵐ[GW.Fock.sectorMeasure n]
      physicalSector n (energyKineticSector P a n u) := by
  cases n with
  | zero =>
    filter_upwards [GW.Fock.vacuumAdapter_ae u,GW.Fock.vacuumAdapter_ae (energyKineticSector P a 0 u)]
      with K hu hv
    change (energyKineticRatio P a 0 K : ℂ) • GW.Fock.vacuumAdapterIsometry u K =
      GW.Fock.vacuumAdapterIsometry (energyKineticSector P a 0 u) K
    rw [hu,hv,show K = 0 from Subsingleton.elim _ _]
    rfl
  | succ n =>
    exact boundedSymmetricMultiplier_ae (n+1) _
      (Complex.continuous_ofReal.measurable.comp (energyKineticRatio_measurable P a (n+1)))
      (C := (1 : ℝ))
      (fun K => by simpa only [Function.comp_apply,Complex.norm_real,Real.norm_eq_abs] using energyKineticRatio_bound P a (n+1) K)
      (fun τ K => congrArg (fun x : ℝ => (x : ℂ)) (energyKineticRatio_permutation P a (n+1) τ K)) u

end Froehlich
