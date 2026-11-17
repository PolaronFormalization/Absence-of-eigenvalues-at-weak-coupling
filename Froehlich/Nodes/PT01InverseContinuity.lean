import Froehlich.Nodes.PT01FormContinuity
import Froehlich.Nodes.CV01InversePairs
import Froehlich.Nodes.CV01PhysicalInverse
import Froehlich.Nodes.CA01Inverse

set_option autoImplicit false

/-! Actual cutoff inverses vary continuously in operator norm: both inverse
identities identify them with native inversion of the actual fixed form. -/
noncomputable section
namespace Froehlich

theorem cutoffCommonEnergyInverse_continuous (n : ℕ) (e : ℝ) (p0 : GW.Space)
    (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (Λ : GW.Operators.PositiveCutoff) :
    Continuous (fun p : GW.Space => cutoffCommonEnergyInverse n e p0 p hn he g hg hs Λ) := by
  let T := fun p : GW.Space => cutoffCommonFormOperator n e p0 p hn he g Λ
  let Q := fun p : GW.Space => cutoffCommonEnergyInverse n e p0 p hn he g hg hs Λ
  have heq : Q = fun p => Ring.inverse (T p) := by
    funext p
    have hp := cutoffCommonFormOperator_inverse_pair n e p0 p hn he g hg hs Λ
    exact (actualInverse_ringInverse (T p) (Q p) hp.2 hp.1).symm
  change Continuous Q
  rw [heq]
  apply continuous_iff_continuousAt.mpr
  intro p
  have hp := cutoffCommonFormOperator_inverse_pair n e p0 p hn he g hg hs Λ
  have hi : ContinuousAt
      (Ring.inverse : (HighEnergySpace (-p0) n →L[ℂ] HighEnergySpace (-p0) n) →
        (HighEnergySpace (-p0) n →L[ℂ] HighEnergySpace (-p0) n)) (T p) :=
    NormedRing.inverse_continuousAt (actualInverseUnit (T p) (Q p) hp.2 hp.1)
  have hT : ContinuousAt T p :=
    (cutoffCommonFormOperator_continuous n e p0 hn he g Λ).continuousAt
  exact hi.comp hT

theorem cutoffAuxiliaryResolvent_continuous (n : ℕ) (e : ℝ)
    (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (Λ : GW.Operators.PositiveCutoff) :
    Continuous (fun p : GW.Space => cutoffAuxiliaryResolvent n e p he Λ g hg hs) := by
  have h := (fixedPhysicalInverseMap (highEnergyEmbedding (-(0 : GW.Space)) n)).continuous.comp
    (cutoffCommonEnergyInverse_continuous n e 0 hn he g hg hs Λ)
  simpa only [Function.comp_def,cutoffCommonEnergyInverse_physical] using h

end Froehlich
