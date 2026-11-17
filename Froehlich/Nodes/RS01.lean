import Froehlich.Nodes.RS01Anchors
import Froehlich.Nodes.SP01

/-!
RS01 / lem:resolvents. The fixed constant is 3*Cphi, before g,p,e.
The weighted source objects, zero extensions Z,Y,X, true original-domain
inverse, and X=X^(0) identification are constructed in the imported files.
The final ground anchor uses the actual groundEnergy and one preliminary
cutoff, rather than selecting a new reference energy.
-/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem finalRS01_uniform : 0 < auxiliaryResolventConstant ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (p : GW.Space) (n : ℕ) (hn : n ≤ 2)
      (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2),
      ‖auxiliaryInteractionOperator g n e p he.2‖ ≤ auxiliaryResolventConstant * |g| ∧
      ‖auxiliaryPhysicalFreeInverse n e p he.2‖ ≤ 1 ∧
      ‖auxiliaryNormalizedInverse g n e p he.2 hg hsmall‖ ≤ 2 ∧
      ‖auxiliaryResolvent n e p he g hg hsmall‖ ≤ 2 ∧
      (∀ f : HighSectorSpace n, 0 ≤ (⟪f,auxiliaryResolvent n e p he g hg hsmall f⟫_ℂ).re) ∧
      GW.Operators.IsResolvent (compressedHamiltonian g (-p) n none) ((e-1+(n : ℝ) : ℝ) : ℂ)
        (auxiliaryResolvent n e p he g hg hsmall) := by
  refine ⟨auxiliaryResolventConstant_pos,?_⟩
  intro e he p n hn g hg hsmall
  exact ⟨auxiliaryInteractionOperator_norm_le g n e p he.2 hg,
    auxiliaryPhysicalFreeInverse_norm_le n e p he.2,
    auxiliaryNormalizedInverse_norm_le g n e p he.2 hg hsmall,
    auxiliaryResolvent_norm_le n e p he g hg hsmall,
    auxiliaryResolvent_nonnegative n e p he g hg hsmall,
    auxiliaryResolvent_isResolvent n e p hn he g hg hsmall⟩

theorem auxiliarySelfEnergy_zero_groundEnergy : ∃ s : ℝ, 0 < s ∧ ∀ g : ℝ, |g| < s →
    ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
    ∃ hg : |g| ≤ 1, ∃ hsmall : auxiliaryResolventConstant * |g| ≤ 1/2,
      auxiliarySelfEnergy (groundEnergy (fiberHamiltonian g 0)) 0 he g hg hsmall =
        groundEnergy (fiberHamiltonian g 0) := by
  obtain ⟨sSP,hsSP,hSP⟩ := finalSP01
  obtain ⟨sNum,hsNum,hNum⟩ := vacuumRoot_uniform_smallness
  obtain ⟨a,ha,haC⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1/2) auxiliaryResolventConstant
  let s := min sSP (min sNum a)
  have hs : 0 < s := lt_min hsSP (lt_min hsNum ha)
  refine ⟨s,hs,?_⟩
  intro g hg
  have hgSP : |g| < sSP := hg.trans_le (min_le_left _ _)
  have hgNum : |g| < sNum := hg.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hga : |g| < a := hg.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hgc,hthr,hleft,hup,hlower,hroot,hrest⟩ := hSP g hgSP 0 (by simp)
  obtain ⟨hgcNum,hL,hquad⟩ := hNum g hgNum
  have he0 : groundEnergy (fiberHamiltonian g 0) ≤ 0 := by
    simpa only [norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hup
  have heI : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0 := by
    exact ⟨by linarith,he0⟩
  have hg1 : |g| ≤ 1 := hgc.trans (by norm_num)
  have hM : auxiliaryResolventConstant * |g| ≤ 1/2 :=
    ((mul_le_mul_of_nonneg_left hga.le auxiliaryResolventConstant_pos.le).trans_lt haC).le
  refine ⟨heI,hg1,hM,?_⟩
  exact auxiliarySelfEnergy_zero_of_vacuum_root (groundEnergy (fiberHamiltonian g 0)) heI g hgc hM hthr hroot

end Froehlich
