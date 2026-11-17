import Froehlich.Nodes.PO02Square
import Froehlich.Nodes.PT03FormCorrectionGround

set_option autoImplicit false
noncomputable section
namespace Froehlich

/-- Zero-momentum positivity on the complete actual one-particle form domain. -/
theorem finalPO02 : ∃ s : ℝ, 0 < s ∧
    ∀ g : ℝ, g ≠ 0 → |g| < s →
      ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
      ∃ hquarter : |g| ≤ 1/4,
      ∃ heLower : -sectorEnergyConstant*|g|^2 ≤ groundEnergy (fiberHamiltonian g 0),
      ∃ hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8,
      ∀ f : OneParticleEnergySpace 0,
        0 ≤ (translatedThresholdForm (groundEnergy (fiberHamiltonian g 0)) he g
          hquarter heLower hquadratic 0 (by simp) f f).re := by
  obtain ⟨CD,sS,hCD,hsS,hS⟩ := finalSE03
  obtain ⟨sT,hsT,hT⟩ := pt03_ground_reference_smallness
  obtain ⟨CK,hCK,hDist⟩ := thresholdBoundedOperator_distance_uniform
  obtain ⟨a,ha,haC⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1/2) (CD+CK)
  refine ⟨min sS (min sT a),lt_min hsS (lt_min hsT ha),?_⟩
  intro g hg0 hgs
  have hgS : |g| < sS := hgs.trans_le (min_le_left _ _)
  have hgT : |g| < sT := hgs.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hga : |g| < a := hgs.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨he,hg,haux,hCD0,hquad,hSat⟩ := hS g hg0 hgS
  obtain ⟨_he,_hg,_haux,hquarter,heLower,hquadratic⟩ := hT g hgT
  have hsq : g^2 ≤ |g| := by nlinarith [abs_nonneg g,sq_abs g]
  have hTiny : (CD+CK)*g^2 ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hsq (add_pos hCD hCK).le).trans
      ((mul_le_mul_of_nonneg_left hga.le (add_pos hCD hCK).le).trans haC.le)
  have hN := (hDist _ he g hg haux CD hCD0 hquad 0 (by simp)).trans hTiny
  refine ⟨he,hquarter,heLower,hquadratic,?_⟩
  intro f
  exact translatedThresholdForm_zero_nonnegative _ he g hg haux CD hCD0 hquad
    hquarter heLower hquadratic hN hSat f

end Froehlich
