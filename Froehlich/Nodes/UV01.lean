import Froehlich.Nodes.UV01UniformInverse
import Froehlich.Nodes.UV01Annihilation
import Froehlich.Nodes.UV01Fields
import Froehlich.Nodes.UV01CorrectionError
import Froehlich.Nodes.RS01

/-! UV01 / lem:fixedcutoff, source1605–1647. All cutoffs use the same e.
The source solutions and corrections are continuous energy-dual solutions;
annihilation convergence is in L² and not at individual momenta. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace Froehlich

 def UV01FixedReference (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2) : Prop :=
  (∀ (n : ℕ) (hn : n ≤ 2) (p : GW.Space) (Λ : GW.Operators.PositiveCutoff),
    ‖cutoffAuxiliaryResolvent n e p he Λ g hg hsmall‖ ≤ 2 ∧
    ‖cutoffAuxiliaryExtendedResolvent n e p he Λ g hg hsmall‖ ≤ 2 ∧
    GW.Operators.IsResolvent (compressedHamiltonian g (-p) n (some Λ)) ((e-1+(n : ℝ) : ℝ) : ℂ)
      (cutoffAuxiliaryResolvent n e p he Λ g hg hsmall)) ∧
  (∀ (n : ℕ) (hn : n ≤ 2) (p0 : GW.Space) (K : Set GW.Space), Bornology.IsBounded K →
    TendstoUniformlyOn
      (fun Λ : GW.Operators.PositiveCutoff => fun p : GW.Space => cutoffCommonEnergyInverse n e p0 p hn he g hg hsmall Λ)
      (fun p : GW.Space => singularCommonEnergyInverse n e p0 p hn he g hg hsmall) atTop K) ∧
  (∀ (p0 : GW.Space) (K : Set GW.Space), Bornology.IsBounded K →
    TendstoUniformlyOn
      (fun Λ : GW.Operators.PositiveCutoff => fun p : GW.Space =>
        highEnergyCoordinateChange (-p0) (-p) 1 (cutoffGroundSourceEnergy e p he g hg hsmall Λ))
      (fun p : GW.Space => highEnergyCoordinateChange (-p0) (-p) 1 (auxiliaryGroundSourceEnergy e p he g hg hsmall)) atTop K) ∧
  (∀ (p0 : GW.Space) (K : Set GW.Space), Bornology.IsBounded K →
    TendstoUniformlyOn
      (fun Λ : GW.Operators.PositiveCutoff => fun p : GW.Space => commonEnergyAnnihilation p0 1
        (highEnergyCoordinateChange (-p0) (-p) 1 (cutoffGroundSourceEnergy e p he g hg hsmall Λ)))
      (fun p : GW.Space => commonEnergyAnnihilation p0 1
        (highEnergyCoordinateChange (-p0) (-p) 1 (auxiliaryGroundSourceEnergy e p he g hg hsmall))) atTop K) ∧
  (∀ (P : GW.Space) (Λ : GW.Operators.PositiveCutoff), 1 ≤ Λ.val →
    ‖cutoffTwoSectorCoupling g P Λ-twoSectorCoupling g P‖ ≤ Real.sqrt 2*lyHighConstant*|g|/Real.sqrt Λ.val) ∧
  (∀ (P : GW.Space) (Λ : GW.Operators.PositiveCutoff), 1 ≤ Λ.val →
    ‖cutoffEnergySchurCorrection e P he g hg hsmall Λ-singularEnergySchurCorrection e P he g hg hsmall‖ ≤
      (12*(Real.sqrt 2*phiMixedConstant*|g|)*(Real.sqrt 2*lyHighConstant*|g|) +
        36*(Real.sqrt 2*phiMixedConstant*|g|)^2*lyHighConstant*|g|)/Real.sqrt Λ.val)

theorem finalUV01_fixed_reference (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2) :
    UV01FixedReference e he g hg hsmall := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro n hn p Λ
    exact ⟨cutoffAuxiliaryResolvent_norm_le n e p he Λ g hg hsmall,
      cutoffAuxiliaryExtendedResolvent_norm_le n e p he Λ g hg hsmall,
      cutoffAuxiliaryResolvent_isResolvent n e p hn he Λ g hg hsmall⟩
  · intro n hn p0 K hK
    exact cutoffCommonEnergyInverse_uniform_on_bounded n e p0 hn he g hg hsmall K hK
  · intro p0 K hK
    simpa only [←cutoffCommonGroundSourceSolution_eq,←singularCommonGroundSourceSolution_eq] using
      cutoffCommonSourceSolution_uniform_on_bounded 1 e p0 (by norm_num) he g hg hsmall K hK
  · intro p0 K hK
    simpa only [←cutoffCommonGroundSourceSolution_eq,←singularCommonGroundSourceSolution_eq] using
      cutoffCommonAnnihilation_uniform_on_bounded 1 e p0 (by norm_num) he g hg hsmall K hK
  · intro P Λ hΛ
    exact cutoffTwoSectorCoupling_error g P Λ hΛ
  · intro P Λ hΛ
    exact cutoffEnergySchurCorrection_error e P he g hg hsmall Λ hΛ

theorem finalUV01 : ∃ s : ℝ, 0 < s ∧ ∀ g : ℝ, |g| < s →
    ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
    ∃ hg : |g| ≤ 1, ∃ hsmall : auxiliaryResolventConstant*|g| ≤ 1/2,
      UV01FixedReference (groundEnergy (fiberHamiltonian g 0)) he g hg hsmall := by
  obtain ⟨s,hs,hground⟩ := auxiliarySelfEnergy_zero_groundEnergy
  refine ⟨s,hs,?_⟩
  intro g hg
  obtain ⟨he,hg1,hsmall,_⟩ := hground g hg
  exact ⟨he,hg1,hsmall,finalUV01_fixed_reference _ he g hg1 hsmall⟩

end Froehlich
