import Froehlich.Nodes.OP01KernelConstruction

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

/-- The literal physical coefficient; its weighted vanishing controls P=0. -/
def weightedHilbertCoefficient (g : ℝ) (P : GW.Space) (eta : GW.Space → ℝ)
    (q : GW.Space) : ℂ := (g : ℂ)*(wDensity P q : ℂ)*(eta q : ℂ)

theorem weightedHilbertCoefficient_memLp (g : ℝ) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)
    (eta : GW.Space → ℝ) (hEta : AEStronglyMeasurable eta volume) (M : ℝ)
    (hBound : ∀ᵐ q ∂volume, |eta q| ≤ M*omega q) :
    MemLp (weightedHilbertCoefficient g P eta) 2 volume := by
  have hw : AEStronglyMeasurable (fun q : GW.Space => (wDensity P q : ℂ)) volume :=
    (Complex.continuous_ofReal.measurable.comp (wDensity_measurable P)).aestronglyMeasurable
  have he : AEStronglyMeasurable (fun q : GW.Space => (eta q : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hEta
  have hm : AEStronglyMeasurable (weightedHilbertCoefficient g P eta) volume := by
    simpa only [weightedHilbertCoefficient,Pi.mul_def] using! (hw.const_mul (g : ℂ)).mul he
  apply ((kernelDensityMajorant_memLp P hP).const_mul (|g| * M)).mono' hm
  filter_upwards [hBound] with q hq
  simp only [weightedHilbertCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (wDensity_nonneg P q)]
  calc
    _ ≤ |g| * wDensity P q*(M*omega q) :=
      mul_le_mul_of_nonneg_left hq (mul_nonneg (abs_nonneg g) (wDensity_nonneg P q))
    _ = _ := by rw [kernelDensityMajorant]; ring

/-- Actual native complex L2 vector, never an unweighted singular source. -/
def weightedHilbertVector (g : ℝ) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)
    (eta : GW.Space → ℝ) (hEta : AEStronglyMeasurable eta volume) (M : ℝ)
    (hBound : ∀ᵐ q ∂volume, |eta q| ≤ M*omega q) : GW.OnePhonon :=
  (weightedHilbertCoefficient_memLp g P hP eta hEta M hBound).toLp
    (weightedHilbertCoefficient g P eta)

theorem weightedHilbertVector_ae (g : ℝ) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)
    (eta : GW.Space → ℝ) (hEta : AEStronglyMeasurable eta volume) (M : ℝ)
    (hBound : ∀ᵐ q ∂volume, |eta q| ≤ M*omega q) :
    weightedHilbertVector g P hP eta hEta M hBound =ᵐ[volume]
      weightedHilbertCoefficient g P eta := MemLp.coeFn_toLp _

end Froehlich
