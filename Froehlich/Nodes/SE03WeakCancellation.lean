import Froehlich.Nodes.SE03ThresholdSource
import Froehlich.Nodes.SE03SourceCollection
import Froehlich.Nodes.SE03AnnularPairing
import Froehlich.Nodes.OP03
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8)
    (hanchor : auxiliarySelfEnergy e 0 he g hg hs = e)

include hquarter heLower hquadratic hanchor in
/-- Equality of the source and direct mixed decompositions, before any infrared division. -/
theorem se03_weak_cancellation (w : OneParticleEnergySpace 0) :
    ⟪oneParticleRadialMap w,
      ((1+e : ℝ) : ℂ) • thresholdKernelSourceVector e he g hg hs 0 (by simp)-
        thresholdBoundedOperator e he g hg hs CD hCD hquad 0 (by simp)
          (oneParticleRadialMap (groundSourceOneEnergy e he g hg hs))⟫_ℂ =
      (starRingEnd ℂ) (translatedLinearSource g 0 w)*
        (⟪thresholdKernelSourceVector e he g hg hs 0 (by simp),
          oneParticleRadialMap (groundSourceOneEnergy e he g hg hs)⟫_ℂ-
            ((1+e : ℝ) : ℂ)*(kernelConstant e he g hg hs 0 : ℂ)) := by
  let f0 := groundSourceOneEnergy e he g hg hs
  let b := thresholdKernelSourceVector e he g hg hs 0 (by simp)
  let B := thresholdBoundedOperator e he g hg hs CD hCD hquad 0 (by simp)
  let u := oneParticleRadialMap f0
  let z := oneParticleRadialMap w
  let L := (starRingEnd ℂ) (translatedLinearSource g 0 w)
  let c : ℂ := (kernelConstant e he g hg hs 0 : ℂ)
  have hO := (se03_threshold_source_pairing e he g hg hs hquarter heLower hquadratic hanchor w).trans
    (se03_right_source_collected e he g hg hs w)
  have hP := translatedThresholdForm_polarized e he g hg hs CD hCD hquad
    hquarter heLower hquadratic 0 (by simp) w f0
  have hell := se03_ground_source_linear_pairing_of_anchor e he g hg hs hanchor
  have hsum : ⟪z,B u⟫_ℂ+c*L*(-(e : ℂ))+L*⟪b,u⟫_ℂ+⟪z,b⟫_ℂ*(-(e : ℂ)) = c*L+⟪z,b⟫_ℂ := by
    have h := hP.symm.trans hO
    rw [hell] at h
    exact h
  change ⟪z,((1+e : ℝ) : ℂ) • b-B u⟫_ℂ = L*(⟪b,u⟫_ℂ-((1+e : ℝ) : ℂ)*c)
  rw [inner_sub_right,inner_smul_right]
  simp only [Complex.ofReal_add,Complex.ofReal_one]
  linear_combination -hsum

include hquarter heLower hquadratic hanchor in
/-- Annular tests yield the literal infrared distributional equality. -/
theorem se03_annular_weak_cancellation (M : ℝ) (hM : 1 ≤ M) (z : GW.OnePhonon)
    (hz : ∀ᵐ q ∂volume, q ∉ se03Annulus M → z q = 0) :
    ⟪z,((1+e : ℝ) : ℂ) • thresholdKernelSourceVector e he g hg hs 0 (by simp)-
      thresholdBoundedOperator e he g hg hs CD hCD hquad 0 (by simp)
        (oneParticleRadialMap (groundSourceOneEnergy e he g hg hs))⟫_ℂ =
      (∫ q : GW.Space,(starRingEnd ℂ) (z q)*((g/‖q‖^2 : ℝ) : ℂ))*
        (⟪thresholdKernelSourceVector e he g hg hs 0 (by simp),
          oneParticleRadialMap (groundSourceOneEnergy e he g hg hs)⟫_ℂ-
          ((1+e : ℝ) : ℂ)*(kernelConstant e he g hg hs 0 : ℂ)) := by
  have h := se03_weak_cancellation e he g hg hs CD hCD hquad hquarter heLower hquadratic hanchor
    (se03AnnularTest M hM z)
  rw [se03AnnularTest_radial M hM z hz,(se03AnnularTest_source g M hM z hz).2] at h
  exact h

end Froehlich
