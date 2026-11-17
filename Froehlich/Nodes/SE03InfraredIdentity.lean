import Froehlich.Nodes.SE03WeakCancellation
import Froehlich.Nodes.SE03AnnularInfrared
import Froehlich.Nodes.SE03AnnularSeparation

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace Classical
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)

def se03InfraredDifference : GW.OnePhonon :=
  ((1+e : ℝ) : ℂ) • thresholdKernelSourceVector e he g hg hs 0 (by simp)-
    thresholdBoundedOperator e he g hg hs CD hCD hquad 0 (by simp)
      (oneParticleRadialMap (groundSourceOneEnergy e he g hg hs))

def se03InfraredCoefficient : ℂ :=
  ⟪thresholdKernelSourceVector e he g hg hs 0 (by simp),
    oneParticleRadialMap (groundSourceOneEnergy e he g hg hs)⟫_ℂ-
      ((1+e : ℝ) : ℂ)*(kernelConstant e he g hg hs 0 : ℂ)

variable (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8)
    (hanchor : auxiliarySelfEnergy e 0 he g hg hs = e)

include hquarter heLower hquadratic hanchor in
theorem se03_infrared_identity_on_annulus (M : ℝ) (hM : 1 ≤ M) :
    ∀ᵐ q ∂volume, q ∈ se03Annulus M →
      se03InfraredDifference e he g hg hs CD hCD hquad q =
        ((g/‖q‖^2 : ℝ) : ℂ)*se03InfraredCoefficient e he g hg hs := by
  let d := se03InfraredDifference e he g hg hs CD hCD hquad
  let a := se03InfraredCoefficient e he g hg hs
  let t := se03AnnularInfraredVector g M hM
  have htest (z : GW.OnePhonon) (hz : ∀ᵐ q ∂volume, q ∉ se03Annulus M → z q = 0) :
      ⟪z,d⟫_ℂ = ⟪z,t⟫_ℂ*a := by
    have ht : ⟪z,t⟫_ℂ = ∫ q : GW.Space,(starRingEnd ℂ) (z q)*((g/‖q‖^2 : ℝ) : ℂ) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [se03AnnularInfraredVector_ae g M hM,hz] with q ht hz
      rw [RCLike.inner_apply',ht]
      by_cases hq : q ∈ se03Annulus M
      · rw [se03AnnularInfraredRow,Set.indicator_of_mem hq]
      · rw [se03AnnularInfraredRow,Set.indicator_of_notMem hq,hz hq]
        simp only [map_zero,zero_mul]
    rw [ht]
    exact se03_annular_weak_cancellation e he g hg hs CD hCD hquad
      hquarter heLower hquadratic hanchor M hM z hz
  have hsep := se03_annular_separation M d t a htest
  filter_upwards [hsep,se03AnnularInfraredVector_ae g M hM] with q hsep ht hq
  have h := hsep hq
  rw [ht,se03AnnularInfraredRow,Set.indicator_of_mem hq] at h
  exact h.trans (mul_comm _ _)

include hquarter heLower hquadratic hanchor in
/-- Countably many annuli patch the source identity outside the null singleton. -/
theorem se03_infrared_identity :
    ∀ᵐ q ∂volume, se03InfraredDifference e he g hg hs CD hCD hquad q =
      ((g/‖q‖^2 : ℝ) : ℂ)*se03InfraredCoefficient e he g hg hs := by
  have hall : ∀ n : ℕ, ∀ᵐ q ∂volume, q ∈ se03Annulus ((n : ℝ)+1) →
      se03InfraredDifference e he g hg hs CD hCD hquad q =
        ((g/‖q‖^2 : ℝ) : ℂ)*se03InfraredCoefficient e he g hg hs := by
    intro n
    exact se03_infrared_identity_on_annulus e he g hg hs CD hCD hquad
      hquarter heLower hquadratic hanchor ((n : ℝ)+1) (by have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  filter_upwards [ae_all_iff.mpr hall,(volume : Measure GW.Space).ae_ne 0] with q hq hq0
  obtain ⟨n,hn⟩ := exists_nat_ge (max ‖q‖ ‖q‖⁻¹)
  have hnorm : ‖q‖ ≤ (n : ℝ)+1 := (le_max_left _ _).trans (hn.trans (by linarith))
  have hinv : ‖q‖⁻¹ ≤ (n : ℝ)+1 := (le_max_right _ _).trans (hn.trans (by linarith))
  have hMp : 0 < (n : ℝ)+1 := by positivity
  have hpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  exact hq n ⟨(inv_le_comm₀ hMp hpos).mpr hinv,hnorm⟩

end Froehlich
