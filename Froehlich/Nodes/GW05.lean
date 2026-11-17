import Froehlich.Nodes.GW04
import GW.Model.ModelFrohlichEstimates

/-! GW05: signed coupling on the retained coefficient, with the same closed UV balls. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Froehlich

def couplingSign (g : ℝ) : ℝ := if 0 ≤ g then 1 else -1

theorem couplingSign_abs (g : ℝ) : |couplingSign g| = 1 := by
  by_cases hg : 0 ≤ g <;> simp [couplingSign, hg]

theorem couplingSign_mul_abs (g : ℝ) : couplingSign g * |g| = g := by
  by_cases hg : 0 ≤ g
  · simp [couplingSign, hg, abs_of_nonneg hg]
  · simp [couplingSign, hg, abs_of_neg (lt_of_not_ge hg)]

theorem couplingSign_complex_norm (g : ℝ) : ‖(couplingSign g : ℂ)‖ = 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, couplingSign_abs]

def fiberFormFactor (g : ℝ) (k : GW.Space) : ℝ := g / ‖k‖

theorem fiberFormFactor_zero (g : ℝ) : fiberFormFactor g 0 = 0 := by
  simp [fiberFormFactor]

theorem fiberFormFactor_zero_coupling (k : GW.Space) : fiberFormFactor 0 k = 0 := by
  simp [fiberFormFactor]

theorem fiberFormFactor_measurable (g : ℝ) : Measurable (fiberFormFactor g) := by
  unfold fiberFormFactor
  fun_prop

theorem fiberFormFactor_even (g : ℝ) (k : GW.Space) :
    fiberFormFactor g (-k) = fiberFormFactor g k := by simp [fiberFormFactor]

/-- Exact everywhere, including the origin and zero coupling. -/
theorem fiberFormFactor_eq_signed_gw (g : ℝ) (k : GW.Space) :
    fiberFormFactor g k = couplingSign g * GW.Model.v (g^2) k := by
  unfold fiberFormFactor GW.Model.v
  rw [Real.sqrt_sq_eq_abs, ← mul_div_assoc, couplingSign_mul_abs]

def cutoffFormFactor (g Λ : ℝ) (k : GW.Space) : ℝ :=
  if ‖k‖ ≤ Λ then fiberFormFactor g k else 0

theorem cutoffFormFactor_eq_signed_gw (g Λ : ℝ) (k : GW.Space) :
    cutoffFormFactor g Λ k = couplingSign g * GW.Model.cutoff (g^2) Λ k := by
  unfold cutoffFormFactor GW.Model.cutoff
  by_cases hk : ‖k‖ ≤ Λ
  · simp only [if_pos hk]
    exact fiberFormFactor_eq_signed_gw g k
  · simp only [if_neg hk, mul_zero]

theorem cutoffFormFactor_zero (g Λ : ℝ) : cutoffFormFactor g Λ 0 = 0 := by
  simp [cutoffFormFactor, fiberFormFactor_zero]

theorem cutoffFormFactor_zero_coupling (Λ : ℝ) (k : GW.Space) :
    cutoffFormFactor 0 Λ k = 0 := by simp [cutoffFormFactor, fiberFormFactor_zero_coupling]

/-- The source cutoff class is exactly the signed retained closed-ball cutoff class. -/
def cutoffFormFactorL2 (g Λ : ℝ) (hΛ : 0 < Λ) : GW.OnePhonon :=
  (couplingSign g : ℂ) • GW.Model.cutoffL2 (g^2) Λ (sq_nonneg g) hΛ

theorem cutoffFormFactorL2_ae (g Λ : ℝ) (hΛ : 0 < Λ) :
    cutoffFormFactorL2 g Λ hΛ =ᵐ[(volume : Measure GW.Space)]
      (fun k => (cutoffFormFactor g Λ k : ℂ)) := by
  filter_upwards [Lp.coeFn_smul (couplingSign g : ℂ)
    (GW.Model.cutoffL2 (g^2) Λ (sq_nonneg g) hΛ),
    GW.Model.cutoffL2_ae (g^2) Λ (sq_nonneg g) hΛ] with k hs hg
  change ((couplingSign g : ℂ) • GW.Model.cutoffL2 (g^2) Λ (sq_nonneg g) hΛ) k =
    (cutoffFormFactor g Λ k : ℂ)
  rw [hs, Pi.smul_apply, hg]
  change (couplingSign g : ℂ) * (GW.Model.cutoff (g^2) Λ k : ℂ) = (cutoffFormFactor g Λ k : ℂ)
  rw [← Complex.ofReal_mul, ← cutoffFormFactor_eq_signed_gw]

theorem cutoffFormFactor_memLp (g Λ : ℝ) (hΛ : 0 < Λ) :
    MemLp (fun k => (cutoffFormFactor g Λ k : ℂ)) 2 (volume : Measure GW.Space) :=
  (Lp.memLp (cutoffFormFactorL2 g Λ hΛ)).ae_eq (cutoffFormFactorL2_ae g Λ hΛ)

theorem cutoffFormFactorL2_norm_sq (g Λ : ℝ) (hΛ : 0 < Λ) :
    ‖cutoffFormFactorL2 g Λ hΛ‖ ^ 2 ≤ 7 * GW.Model.unitBallVolume * g^2 * Λ := by
  change ‖(couplingSign g : ℂ) • GW.Model.cutoffL2 (g^2) Λ (sq_nonneg g) hΛ‖ ^ 2 ≤ _
  rw [norm_smul, mul_pow, couplingSign_complex_norm, one_pow, one_mul]
  exact GW.Model.cutoffL2_norm_sq (g^2) Λ (sq_nonneg g) hΛ

theorem ordinaryKernel_smul (c : ℂ) (f : GW.OnePhonon) :
    GW.Fock.ordinaryKernel (c • f) = c • GW.Fock.ordinaryKernel f := by
  apply ContinuousLinearMap.ext
  intro z
  change z • (c • f) = c • (z • f)
  exact smul_comm z c f

theorem kernelCreationRaw_smul (c : ℂ) (F : GW.Fock.BosonKernel ℂ) (n : ℕ)
    (u : GW.Fock.KernelSector ℂ n) :
    GW.Fock.kernelCreationRaw (c • F) n u = c • GW.Fock.kernelCreationRaw F n u := by
  change (GW.Fock.kernelSplit (E := ℂ) n).symm
    (GW.Fock.amplify (GW.Fock.sectorMeasure n) (c • F) u) =
      c • (GW.Fock.kernelSplit (E := ℂ) n).symm
        (GW.Fock.amplify (GW.Fock.sectorMeasure n) F u)
  have hs : GW.Fock.amplify (GW.Fock.sectorMeasure n) (c • F) =
      c • GW.Fock.amplify (GW.Fock.sectorMeasure n) F :=
    (GW.Fock.amplificationLinear (GW.Fock.sectorMeasure n)).map_smul c F
  rw [hs]
  change (GW.Fock.kernelSplit (E := ℂ) n).symm
    (c • GW.Fock.amplify (GW.Fock.sectorMeasure n) F u) = _
  exact map_smul _ c _

theorem kernelCreation_smul (c : ℂ) (F : GW.Fock.BosonKernel ℂ) (n : ℕ)
    (u : GW.Fock.kernelFixed (E := ℂ) n) :
    GW.Fock.kernelCreation (c • F) n u = c • GW.Fock.kernelCreation F n u := by
  apply Subtype.ext
  change (GW.Fock.kernelCreation (c • F) n u : GW.Fock.KernelSector ℂ (n+1)) =
    c • (GW.Fock.kernelCreation F n u : GW.Fock.KernelSector ℂ (n+1))
  rw [GW.Fock.kernelCreation_value, GW.Fock.kernelCreation_value, kernelCreationRaw_smul, map_smul]
  exact smul_comm (Real.sqrt (n+1 : ℕ) : ℂ) c _

theorem ordinarySectorCreation_smul (c : ℂ) (f : GW.OnePhonon) (n : ℕ)
    (u : GW.Fock.Sector n) :
    GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel (c • f)) n u =
      c • GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n u := by
  change (GW.Fock.ordinarySectorKernel (n+1)).symm
    (GW.Fock.kernelCreation (GW.Fock.ordinaryKernel (c • f)) n (GW.Fock.ordinarySectorKernel n u)) =
      c • (GW.Fock.ordinarySectorKernel (n+1)).symm
        (GW.Fock.kernelCreation (GW.Fock.ordinaryKernel f) n (GW.Fock.ordinarySectorKernel n u))
  rw [ordinaryKernel_smul, kernelCreation_smul, map_smul]

theorem creationRestriction_smul_kernel (c : ℂ) (f : GW.OnePhonon) (x : NumberFormSpace) :
    creationRestriction (c • f) x = c • creationRestriction f x := by
  apply lp.ext
  funext n
  change GW.Fock.ordinaryCreation (c • f)
    (GW.Fock.ordinaryCreationRootInput (c • f) (numberFormRootInput x)) n =
      c • GW.Fock.ordinaryCreation f
        (GW.Fock.ordinaryCreationRootInput f (numberFormRootInput x)) n
  cases n with
  | zero => rw [GW.Fock.ordinaryCreation_zero, GW.Fock.ordinaryCreation_zero, smul_zero]
  | succ n =>
    rw [GW.Fock.ordinaryCreation_succ, GW.Fock.ordinaryCreation_succ]
    exact ordinarySectorCreation_smul c f n (numberFormEmbedding x n)

/-- The annihilation restriction is conjugate-linear in its smearing function. -/
theorem annihilationRestriction_smul_kernel (c : ℂ) (f : GW.OnePhonon) (x : NumberFormSpace) :
    annihilationRestriction (c • f) x = (starRingEnd ℂ) c • annihilationRestriction f x := by
  rw [annihilationRestriction_integral, annihilationRestriction_integral]
  calc
    _ = ∫ k, (starRingEnd ℂ) c • ((starRingEnd ℂ) (f k) • annihilationField x k) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c f] with k hk
      simp only [Pi.smul_apply] at hk
      rw [hk]
      change (starRingEnd ℂ) (c * f k) • annihilationField x k =
        (starRingEnd ℂ) c • ((starRingEnd ℂ) (f k) • annihilationField x k)
      rw [map_mul, smul_smul]
    _ = _ := integral_smul _ _

theorem fieldRestriction_real_smul_kernel (r : ℝ) (f : GW.OnePhonon) (x : NumberFormSpace) :
    fieldRestriction ((r : ℂ) • f) x = (r : ℂ) • fieldRestriction f x := by
  change annihilationRestriction ((r : ℂ) • f) x + creationRestriction ((r : ℂ) • f) x =
    (r : ℂ) • (annihilationRestriction f x + creationRestriction f x)
  rw [annihilationRestriction_smul_kernel, creationRestriction_smul_kernel]
  have hs : (starRingEnd ℂ) (r : ℂ) = (r : ℂ) := by
    exact Complex.conj_ofReal r
  rw [hs, smul_add]

theorem ordinaryField_real_smul_kernel (r : ℝ) (f : GW.OnePhonon) (x : NumberFormSpace) :
    GW.Fock.ordinaryField ((r : ℂ) • f) (numberFormRootInput x) =
      (r : ℂ) • GW.Fock.ordinaryField f (numberFormRootInput x) := by
  calc
    _ = fieldRestriction ((r : ℂ) • f) x := (fieldRestriction_eq_ordinaryField _ x).symm
    _ = (r : ℂ) • fieldRestriction f x := fieldRestriction_real_smul_kernel r f x
    _ = _ := congrArg ((r : ℂ) • ·) (fieldRestriction_eq_ordinaryField f x)

theorem cutoffField_eq_signed_gw (g Λ : ℝ) (hΛ : 0 < Λ) (x : NumberFormSpace) :
    GW.Fock.ordinaryField (cutoffFormFactorL2 g Λ hΛ) (numberFormRootInput x) =
      (couplingSign g : ℂ) • GW.Fock.ordinaryField
        (GW.Model.cutoffL2 (g^2) Λ (sq_nonneg g) hΛ) (numberFormRootInput x) :=
  ordinaryField_real_smul_kernel (couplingSign g)
    (GW.Model.cutoffL2 (g^2) Λ (sq_nonneg g) hΛ) x

end Froehlich
