import Froehlich.Nodes.RS01

/-! One preliminary cutoff, before signed g and every P, supplies all
actual ground-energy and numerical guards of the threshold form. -/
noncomputable section
namespace Froehlich

theorem pt03_ground_reference_smallness : ∃ s : ℝ, 0 < s ∧ ∀ g : ℝ, |g| < s →
    groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0 ∧
    |g| ≤ 1 ∧ auxiliaryResolventConstant * |g| ≤ 1/2 ∧ |g| ≤ 1/4 ∧
    -sectorEnergyConstant * |g|^2 ≤ groundEnergy (fiberHamiltonian g 0) ∧
    sectorQuadraticConstant * |g|^2 ≤ 1/8 := by
  obtain ⟨sA,hsA,hA⟩ := auxiliarySelfEnergy_zero_groundEnergy
  obtain ⟨sSP,hsSP,hSP⟩ := finalSP01
  obtain ⟨a,ha,haC⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1/8) sectorQuadraticConstant
  let s := min sA (min sSP a)
  have hs : 0 < s := lt_min hsA (lt_min hsSP ha)
  refine ⟨s,hs,?_⟩
  intro g hg
  have hgA : |g| < sA := hg.trans_le (min_le_left _ _)
  have hgSP : |g| < sSP := hg.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hga : |g| < a := hg.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨he,hg1,haux,_hSelf⟩ := hA g hgA
  obtain ⟨hquarter,_hthr,_hleft,_hup,hlower,_hrest⟩ := hSP g hgSP 0 (by simp)
  have hC : 0 ≤ sectorQuadraticConstant := by
    unfold sectorQuadraticConstant
    exact mul_nonneg (by norm_num) lySmallConstant_pos.le
  have hsq : |g|^2 ≤ |g| := by
    have h1 : |g| ≤ 1 := hquarter.trans (by norm_num)
    nlinarith [abs_nonneg g]
  have hlin : sectorQuadraticConstant * |g| < 1/8 :=
    (mul_le_mul_of_nonneg_left hga.le hC).trans_lt haC
  have hlower' : -sectorEnergyConstant * |g|^2 ≤ groundEnergy (fiberHamiltonian g 0) := by
    simpa only [neg_mul] using hlower
  exact ⟨he,hg1,haux,hquarter,hlower',(mul_le_mul_of_nonneg_left hsq hC).trans hlin.le⟩

end Froehlich
