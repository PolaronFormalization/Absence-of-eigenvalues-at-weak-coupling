import Froehlich.Nodes.OP01BoundedOperator
import Froehlich.Nodes.RS03

set_option autoImplicit false
noncomputable section
namespace Froehlich

/-- The quadratic multiplier estimate is constructed from the actual RS03
ground anchor. No cutoff energy or caller-supplied smallness estimate is used. -/
theorem op01_ground_smallness : ∃ CD C s : ℝ, 0 < CD ∧ 0 < C ∧ 0 < s ∧
    ∀ g : ℝ, |g| < s →
      ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
      ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
      ∃ hCD : 0 ≤ CD,
      ∃ hquad : ∀ q : GW.Space,
        |auxiliarySelfEnergy (groundEnergy (fiberHamiltonian g 0)) q he g hg hs-groundEnergy (fiberHamiltonian g 0)| ≤
          CD*g^2*‖q‖^2,
      (∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
        ‖thresholdBoundedOperator (groundEnergy (fiberHamiltonian g 0)) he g hg hs CD hCD hquad P hP-1‖ ≤ C*g^2 ∧
        ‖thresholdBoundedOperator (groundEnergy (fiberHamiltonian g 0)) he g hg hs CD hCD hquad P hP-1‖ ≤ 1/2) ∧
      ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier (groundEnergy (fiberHamiltonian g 0)) he g hg hs q := by
  obtain ⟨CD,sR,hCD,hsR,hR⟩ := finalRS03
  obtain ⟨CK,hCK,hDist⟩ := thresholdBoundedOperator_distance_uniform
  let C := CD+CK
  have hC : 0 < C := add_pos hCD hCK
  obtain ⟨a,ha,haC⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1/4) C
  let s := min sR a
  have hs : 0 < s := lt_min hsR ha
  refine ⟨CD,C,s,hCD,hC,hs,?_⟩
  intro g hgs
  have hgR : |g| < sR := hgs.trans_le (min_le_left _ _)
  have hga : |g| < a := hgs.trans_le (min_le_right _ _)
  obtain ⟨he,hg,haux,hQ⟩ := hR g hgR
  rcases hQ with ⟨_,_,_,_,_,_,hquad⟩
  have hsq : g^2 ≤ |g| := by nlinarith [abs_nonneg g,sq_abs g]
  have hlin : C*|g| < 1/4 := (mul_le_mul_of_nonneg_left hga.le hC.le).trans_lt haC
  have hsmall : C*g^2 ≤ 1/4 := (mul_le_mul_of_nonneg_left hsq hC.le).trans hlin.le
  have hCDsmall : CD*g^2 ≤ 1/4 :=
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCK.le) (sq_nonneg g)).trans hsmall
  refine ⟨he,hg,haux,hCD.le,hquad,?_,?_⟩
  · intro P hP
    have hD := hDist _ he g hg haux CD hCD.le hquad P hP
    exact ⟨hD,hD.trans (hsmall.trans (by norm_num))⟩
  · intro q
    exact thresholdDiagonalMultiplier_lower _ he g hg haux CD hCD.le hquad hCDsmall q

end Froehlich
