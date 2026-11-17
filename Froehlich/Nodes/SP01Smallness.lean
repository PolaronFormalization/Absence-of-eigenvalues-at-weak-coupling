import Froehlich.Nodes.SP01Root
import Froehlich.Nodes.FB03

/-! A single preliminary coupling cutoff, chosen before g and P, gives
all the numerical hypotheses used by the source vacuum-root construction. -/
noncomputable section
namespace Froehlich

theorem vacuumRoot_uniform_smallness : ∃ s : ℝ, 0 < s ∧ ∀ g : ℝ, |g| < s →
    |g| ≤ 1/4 ∧ (1/2 : ℝ) < nonvacuumThreshold g ∧ sectorEnergyConstant*|g|^2 < 1/4 := by
  obtain ⟨a,ha,haC⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1/4) sectorLinearConstant
  obtain ⟨b,hb,hbC⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1/4) sectorEnergyConstant
  let s := min (1/4 : ℝ) (min a b)
  have hs : 0 < s := lt_min (by norm_num) (lt_min ha hb)
  refine ⟨s,hs,?_⟩
  intro g hg
  have hquarter : |g| < 1/4 := hg.trans_le (min_le_left _ _)
  have hga : |g| < a := hg.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hgb : |g| < b := hg.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hCL : 0 ≤ sectorLinearConstant := by
    unfold sectorLinearConstant
    linarith [lySmallConstant_pos]
  have hCE : 0 ≤ sectorEnergyConstant := sectorEnergyConstant_pos.le
  have hlin : sectorLinearConstant*|g| < 1/4 :=
    (mul_le_mul_of_nonneg_left hga.le hCL).trans_lt haC
  have he : sectorEnergyConstant*|g| < 1/4 :=
    (mul_le_mul_of_nonneg_left hgb.le hCE).trans_lt hbC
  have hsq : |g|^2 ≤ |g| := by nlinarith [abs_nonneg g]
  refine ⟨hquarter.le,?_,(mul_le_mul_of_nonneg_left hsq hCE).trans_lt he⟩
  unfold nonvacuumThreshold
  linarith

end Froehlich
