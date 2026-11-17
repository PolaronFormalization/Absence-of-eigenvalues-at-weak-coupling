import Froehlich.Nodes.OP01KernelSymbols
import Froehlich.Nodes.OP00

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

theorem kernelDensityMajorant_square (P q : GW.Space) :
    (kernelDensityMajorant P q)^2 = (omega q)^2*muDensity P q := by
  rw [kernelDensityMajorant,mul_pow,wDensity_sq]

theorem kernelDensityMajorant_memLp (P : GW.Space) (hP : ‖P‖ ≤ 1/4) :
    MemLp (kernelDensityMajorant P) 2 volume := by
  obtain ⟨CI,hCI,hB⟩ := omega_moments_uniform
  apply (memLp_two_iff_integrable_sq (kernelDensityMajorant_measurable P).aestronglyMeasurable).mpr
  have heq : (fun q => (kernelDensityMajorant P q)^2) =
      (fun q => (omega q)^2*muDensity P q) := funext (kernelDensityMajorant_square P)
  rw [heq]
  exact (hB P hP).1.1

theorem kernelDensityMajorant_squaredNorm_uniform : ∃ CI : ℝ, 0 < CI ∧
    ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
      ‖(kernelDensityMajorant_memLp P hP).toLp (kernelDensityMajorant P)‖^2 ≤ CI := by
  obtain ⟨CI,hCI,hB⟩ := omega_moments_uniform
  refine ⟨CI,hCI,?_⟩
  intro P hP
  rw [GW.Analysis.l2_norm_sq (𝕜 := ℝ)]
  calc
    _ = ∫ q : GW.Space,(omega q)^2*muDensity P q := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp (kernelDensityMajorant_memLp P hP)] with q hq
      rw [hq,Real.norm_eq_abs,abs_of_nonneg (kernelDensityMajorant_nonnegative P q),kernelDensityMajorant_square]
    _ ≤ CI := (hB P hP).1.2

/-- The source coefficient is dominated by the same actual L2 majorant;
no unweighted w_P or v_g vector is needed at P=0. -/
theorem kernelSourceCoefficient_majorant : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P q : GW.Space), ‖P‖ ≤ 1/4 →
      ‖kernelSourceCoefficient e he g hg hs P q‖ ≤ C * |g| * kernelDensityMajorant P q := by
  obtain ⟨C,hC,hB⟩ := kernelPsi_uniform_bound
  refine ⟨(5/4 : ℝ)*C,by positivity,?_⟩
  intro e he g hg hs P q hP
  have hsum : omega q+‖P‖ ≤ (5/4 : ℝ) := by linarith [omega_le_one q]
  have hgw : 0 ≤ |g| * wDensity P q := mul_nonneg (abs_nonneg g) (wDensity_nonneg P q)
  simp only [kernelSourceCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (wDensity_nonneg P q)]
  calc
    _ ≤ |g| * wDensity P q*(C*omega q*(omega q+‖P‖)) :=
      mul_le_mul_of_nonneg_left (hB e he g hg hs P q hP) hgw
    _ ≤ |g| * wDensity P q*(C*omega q*(5/4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum
        (mul_nonneg hC.le (omega_nonneg q))) hgw
    _ = _ := by unfold kernelDensityMajorant; ring

end Froehlich
