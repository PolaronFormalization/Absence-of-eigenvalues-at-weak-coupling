import Froehlich.Nodes.RS03

set_option autoImplicit false

/-! The diagonal multiplier from OP01. Its value at zero is prescribed as
one; no continuous extension at zero is asserted or needed. -/
noncomputable section
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

def thresholdDiagonalMultiplier (q : GW.Space) : ℝ :=
  if q = 0 then 1 else 1 + (auxiliarySelfEnergy e q he g hg hs-e)/‖q‖^2

theorem thresholdDiagonalMultiplier_zero :
    thresholdDiagonalMultiplier e he g hg hs 0 = 1 := by
  simp [thresholdDiagonalMultiplier]

theorem thresholdDiagonalMultiplier_measurable :
    Measurable (thresholdDiagonalMultiplier e he g hg hs) := by
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (measurable_const.add (((auxiliarySelfEnergy_contDiff g e he hg hs).continuous.measurable.sub
      measurable_const).div (measurable_norm.pow_const 2)))

theorem thresholdDiagonalMultiplier_even :
    Function.Even (thresholdDiagonalMultiplier e he g hg hs) := by
  intro q
  simp only [thresholdDiagonalMultiplier,neg_eq_zero,norm_neg,
    auxiliarySelfEnergy_even e q he g hg hs]

theorem thresholdDiagonalMultiplier_sub_one_bound (C : ℝ) (hC : 0 ≤ C)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ C*g^2*‖q‖^2)
    (q : GW.Space) :
    |thresholdDiagonalMultiplier e he g hg hs q-1| ≤ C*g^2 := by
  by_cases hq : q = 0
  · simp only [hq,thresholdDiagonalMultiplier_zero,sub_self,abs_zero]
    positivity
  · have hpos : 0 < ‖q‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hq)
    rw [thresholdDiagonalMultiplier,ite_eq_right hq,add_sub_cancel_left,abs_div,
      abs_of_pos hpos]
    exact (div_le_iff₀ hpos).mpr (hquad q)

theorem thresholdDiagonalMultiplier_lower (C : ℝ) (hC : 0 ≤ C)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ C*g^2*‖q‖^2)
    (hsmall : C*g^2 ≤ 1/4) (q : GW.Space) :
    3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q := by
  have h := (abs_le.mp (thresholdDiagonalMultiplier_sub_one_bound e he g hg hs C hC hquad q)).1
  linarith

theorem thresholdDiagonalMultiplier_uniform : ∃ C s : ℝ, 0 < C ∧ 0 < s ∧
    ∀ g : ℝ, |g| < s →
      ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
      ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
        ∀ q : GW.Space,
          |thresholdDiagonalMultiplier (groundEnergy (fiberHamiltonian g 0)) he g hg hs q-1| ≤ C*g^2 := by
  obtain ⟨C,s,hC,hs,hRS⟩ := finalRS03
  refine ⟨C,s,hC,hs,?_⟩
  intro g hgs
  obtain ⟨he,hg,hsmall,hQ⟩ := hRS g hgs
  rcases hQ with ⟨_,_,_,_,_,_,hquad⟩
  exact ⟨he,hg,hsmall,thresholdDiagonalMultiplier_sub_one_bound _ he g hg hsmall C hC.le hquad⟩

end Froehlich
