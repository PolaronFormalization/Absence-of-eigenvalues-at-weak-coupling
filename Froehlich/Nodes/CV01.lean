import Froehlich.Nodes.CV01FormConvergence
import Froehlich.Nodes.CV01PhysicalInverse
import Froehlich.Nodes.CV01InversePairs
import Froehlich.Nodes.CV01SchurCorrections

/-! CV01 / lem:cutoffledger, source1645–1677. Every limit is on a fixed
coordinate Hilbert carrier, at the same energy e. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace Froehlich
variable (e : ℝ) (P0 : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2)

theorem commonSchurCorrection_uniform_on_bounded (K : Set GW.Space) (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn
      (fun Λ : GW.Operators.PositiveCutoff => fun P : GW.Space => cutoffCommonSchurCorrection e P0 P he g hg hsmall Λ)
      (fun P : GW.Space => singularCommonSchurCorrection e P0 P he g hg hsmall) atTop K := by
  obtain ⟨R,hR,hsub⟩ := hK.subset_closedBall_lt 0 P0
  apply (commonSchurCorrection_uniform_on_ball e P0 he g hg hsmall R hR.le).mono
  intro P hP
  change ‖P-P0‖ ≤ R
  simpa only [Metric.mem_closedBall,dist_eq_norm] using hsub hP

def CV01FixedReference : Prop :=
  (∀ (n : ℕ) (hn : n ≤ 2) (p0 : GW.Space) (K : Set GW.Space), Bornology.IsBounded K →
    TendstoUniformlyOn
      (fun Λ : GW.Operators.PositiveCutoff => fun p : GW.Space => cutoffCommonFormOperator n e p0 p hn he g Λ)
      (fun p : GW.Space => singularCommonFormOperator n e p0 p hn he g) atTop K ∧
    TendstoUniformlyOn
      (fun Λ : GW.Operators.PositiveCutoff => fun p : GW.Space => cutoffCommonEnergyInverse n e p0 p hn he g hg hsmall Λ)
      (fun p : GW.Space => singularCommonEnergyInverse n e p0 p hn he g hg hsmall) atTop K ∧
    TendstoUniformlyOn
      (fun Λ : GW.Operators.PositiveCutoff => fun p : GW.Space => cutoffAuxiliaryResolvent n e p he Λ g hg hsmall)
      (fun p : GW.Space => auxiliaryResolvent n e p he g hg hsmall) atTop K) ∧
  (∀ (n : ℕ) (hn : n ≤ 2) (p0 p : GW.Space) (Λ : GW.Operators.PositiveCutoff),
    (cutoffCommonEnergyInverse n e p0 p hn he g hg hsmall Λ*cutoffCommonFormOperator n e p0 p hn he g Λ=1 ∧
      cutoffCommonFormOperator n e p0 p hn he g Λ*cutoffCommonEnergyInverse n e p0 p hn he g hg hsmall Λ=1) ∧
    (singularCommonEnergyInverse n e p0 p hn he g hg hsmall*singularCommonFormOperator n e p0 p hn he g=1 ∧
      singularCommonFormOperator n e p0 p hn he g*singularCommonEnergyInverse n e p0 p hn he g hg hsmall=1)) ∧
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
  (∀ (P0 : GW.Space) (K : Set GW.Space), Bornology.IsBounded K →
    TendstoUniformlyOn
      (fun Λ : GW.Operators.PositiveCutoff => fun P : GW.Space => cutoffCommonSchurCorrection e P0 P he g hg hsmall Λ)
      (fun P : GW.Space => singularCommonSchurCorrection e P0 P he g hg hsmall) atTop K)

theorem finalCV01_fixed_reference : CV01FixedReference e he g hg hsmall := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro n hn p0 K hK
    exact ⟨commonFormOperator_uniform_on n e p0 hn he g K,
      cutoffCommonEnergyInverse_uniform_on_bounded n e p0 hn he g hg hsmall K hK,
      cutoffAuxiliaryResolvent_uniform_on_bounded n e p0 hn he g hg hsmall K hK⟩
  · intro n hn p0 p Λ
    exact ⟨cutoffCommonFormOperator_inverse_pair n e p0 p hn he g hg hsmall Λ,
      singularCommonFormOperator_inverse_pair n e p0 p hn he g hg hsmall⟩
  · intro p0 K hK
    simpa only [←cutoffCommonGroundSourceSolution_eq,←singularCommonGroundSourceSolution_eq] using
      cutoffCommonSourceSolution_uniform_on_bounded 1 e p0 (by norm_num) he g hg hsmall K hK
  · intro p0 K hK
    simpa only [←cutoffCommonGroundSourceSolution_eq,←singularCommonGroundSourceSolution_eq] using
      cutoffCommonAnnihilation_uniform_on_bounded 1 e p0 (by norm_num) he g hg hsmall K hK
  · intro P0 K hK
    exact commonSchurCorrection_uniform_on_bounded e P0 he g hg hsmall K hK

theorem finalCV01 : ∃ s : ℝ, 0 < s ∧ ∀ g : ℝ, |g| < s →
    ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
    ∃ hg : |g| ≤ 1, ∃ hsmall : auxiliaryResolventConstant*|g| ≤ 1/2,
      CV01FixedReference (groundEnergy (fiberHamiltonian g 0)) he g hg hsmall := by
  obtain ⟨s,hs,hground⟩ := auxiliarySelfEnergy_zero_groundEnergy
  refine ⟨s,hs,?_⟩
  intro g hg
  obtain ⟨he,hg1,hsmall,_⟩ := hground g hg
  exact ⟨he,hg1,hsmall,finalCV01_fixed_reference _ he g hg1 hsmall⟩

end Froehlich
