import Froehlich.Nodes.SE03AnnularTest
import Froehlich.Nodes.OP02SourcePairings

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

/-- The annular radial test turns the source dual into the literal infrared row. -/
theorem se03AnnularTest_source (g M : ℝ) (hM : 1 ≤ M) (z : GW.OnePhonon)
    (hz : ∀ᵐ q ∂volume, q ∉ se03Annulus M → z q = 0) :
    Integrable (fun q : GW.Space => (starRingEnd ℂ) (z q)*((g/‖q‖^2 : ℝ) : ℂ)) volume ∧
    (starRingEnd ℂ) (translatedLinearSource g 0 (se03AnnularTest M hM z)) =
      ∫ q : GW.Space,(starRingEnd ℂ) (z q)*((g/‖q‖^2 : ℝ) : ℂ) := by
  let f := se03AnnularTest M hM z
  have hsource := translatedLinearSource_star_integral g 0 f
  have hr := oneParticleRadialMap_ae f
  have heq := se03AnnularTest_radial M hM z hz
  have hi : (fun q : GW.Space => (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q)*
      (fiberFormFactor g (q+0) : ℂ)) =ᵐ[volume]
      (fun q : GW.Space => (starRingEnd ℂ) (z q)*((g/‖q‖^2 : ℝ) : ℂ)) := by
    filter_upwards [hr,(volume : Measure GW.Space).ae_ne 0] with q hr hq
    rw [heq] at hr
    rw [hr]
    have hn : (‖q‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hq)
    simp only [add_zero,fiberFormFactor,Complex.ofReal_div,Complex.ofReal_pow,map_mul,
      Complex.conj_ofReal]
    field_simp [hn]
    <;> ring
  exact ⟨hsource.1.congr hi,hsource.2.trans (integral_congr_ae hi)⟩

/-- The second annular source term is the actual Hilbert pairing with b. -/
theorem se03AnnularTest_kernelSource (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (M : ℝ) (hM : 1 ≤ M) (z : GW.OnePhonon)
    (hz : ∀ᵐ q ∂volume, q ∉ se03Annulus M → z q = 0) :
    Integrable (fun q : GW.Space =>
      (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 (se03AnnularTest M hM z) q)*
        (fiberFormFactor g (q+0) : ℂ)*(kernelPsi e he g hg hs 0 q : ℂ)) volume ∧
    ⟪z,thresholdKernelSourceVector e he g hg hs 0 (by simp)⟫_ℂ =
      ∫ q : GW.Space,(starRingEnd ℂ) (oneParticleEnergyEmbedding 0 (se03AnnularTest M hM z) q)*
        (fiberFormFactor g (q+0) : ℂ)*(kernelPsi e he g hg hs 0 q : ℂ) := by
  have h := radial_inner_kernelSource_integral e he g hg hs 0 (by simp) (se03AnnularTest M hM z)
  rw [se03AnnularTest_radial M hM z hz] at h
  exact h

end Froehlich
