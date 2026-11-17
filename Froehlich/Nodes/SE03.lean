import Froehlich.Nodes.SE03Saturation
import Froehlich.Nodes.RS01
import Froehlich.Nodes.PT03FormCorrectionGround

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

/-- Literal unnormalized zero-momentum inverse response; no normalization by c0. -/
def SE03FixedReference (CD e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2) : Prop :=
  ⟪thresholdKernelSourceVector e he g hg hs 0 (by simp),
    thresholdBoundedInverse e he g hg hs CD hCD hquad 0 (by simp)
      (thresholdKernelSourceVector e he g hg hs 0 (by simp))⟫_ℂ =
    (kernelConstant e he g hg hs 0 : ℂ)

/-- A single preliminary cutoff works for every sufficiently small nonzero signed coupling. -/
theorem finalSE03 : ∃ CD s : ℝ, 0 < CD ∧ 0 < s ∧
    ∀ g : ℝ, g ≠ 0 → |g| < s →
      ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
      ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
      ∃ hCD : 0 ≤ CD,
      ∃ hquad : ∀ q : GW.Space,
        |auxiliarySelfEnergy (groundEnergy (fiberHamiltonian g 0)) q he g hg hs-
          groundEnergy (fiberHamiltonian g 0)| ≤ CD*g^2*‖q‖^2,
      SE03FixedReference CD (groundEnergy (fiberHamiltonian g 0)) he g hg hs hCD hquad := by
  obtain ⟨CD,C,sO,hCD,hC,hsO,hO⟩ := op01_ground_smallness
  obtain ⟨sT,hsT,hT⟩ := pt03_ground_reference_smallness
  obtain ⟨sA,hsA,hA⟩ := auxiliarySelfEnergy_zero_groundEnergy
  refine ⟨CD,min sO (min sT sA),hCD,lt_min hsO (lt_min hsT hsA),?_⟩
  intro g hg0 hgs
  have hgO : |g| < sO := hgs.trans_le (min_le_left _ _)
  have hgT : |g| < sT := hgs.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hgA : |g| < sA := hgs.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨he,hg,haux,hCD0,hquad,hControl,_⟩ := hO g hgO
  obtain ⟨_he,_hg,_haux,hquarter,heLower,hquadratic⟩ := hT g hgT
  obtain ⟨_heA,_hgA,_hauxA,hanchor⟩ := hA g hgA
  refine ⟨he,hg,haux,hCD0,hquad,?_⟩
  exact se03_saturation _ he g hg haux CD hCD0 hquad hquarter heLower hquadratic
    hanchor (hControl 0 (by simp)).2 hg0

end Froehlich
