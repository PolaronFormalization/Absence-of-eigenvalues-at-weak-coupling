import Froehlich.Nodes.CV01PhysicalInverse
import Froehlich.Nodes.RS01PhysicalResolvent

/-! PT01's left cutoff limit for a regular physical source, using the
actual energy-dual load j†F. This is not the singular form-source h_p. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

def ptRegularCutoffEnergyVector (F : HighSectorSpace n) (Lambda : GW.Operators.PositiveCutoff) :
    HighEnergySpace (-p) n :=
  cutoffCommonEnergyInverse n e p p hn he g hg hs Lambda ((highEnergyEmbedding (-p) n).adjoint F)

def ptRegularSingularEnergyVector (F : HighSectorSpace n) : HighEnergySpace (-p) n :=
  singularCommonEnergyInverse n e p p hn he g hg hs ((highEnergyEmbedding (-p) n).adjoint F)

theorem ptRegularCutoffEnergyVector_physical (F : HighSectorSpace n) (Lambda : GW.Operators.PositiveCutoff) :
    highEnergyEmbedding (-p) n (ptRegularCutoffEnergyVector n e p hn he g hg hs F Lambda)=
      cutoffAuxiliaryResolvent n e p he Lambda g hg hs F := by
  have h := congrArg (fun T : HighSectorSpace n →L[ℂ] HighSectorSpace n => T F)
    (cutoffCommonEnergyInverse_physical n e p p hn he g hg hs Lambda)
  exact h

theorem ptRegularSingularEnergyVector_physical (F : HighSectorSpace n) :
    highEnergyEmbedding (-p) n (ptRegularSingularEnergyVector n e p hn he g hg hs F)=
      auxiliaryResolvent n e p he g hg hs F := by
  have h := congrArg (fun T : HighSectorSpace n →L[ℂ] HighSectorSpace n => T F)
    (singularCommonEnergyInverse_physical n e p p hn he g hg hs)
  exact h

theorem ptRegularSingularEnergyVector_eq_solution (F : HighSectorSpace n) :
    ptRegularSingularEnergyVector n e p hn he g hg hs F=auxiliaryPhysicalEnergySolution n e p hn he g hg hs F := by
  apply highEnergyEmbedding_injective (-p) n
  rw [ptRegularSingularEnergyVector_physical,auxiliaryResolvent_solution_embedding]

theorem ptRegularCutoffEnergyVector_tendsto (F : HighSectorSpace n) :
    Tendsto (ptRegularCutoffEnergyVector n e p hn he g hg hs F) atTop
      (𝓝 (ptRegularSingularEnergyVector n e p hn he g hg hs F)) := by
  have hQ := (cutoffCommonEnergyInverse_uniform_on_bounded n e p hn he g hg hs ({p} : Set GW.Space)
    (isCompact_singleton : IsCompact ({p} : Set GW.Space)).isBounded).tendsto_at (Set.mem_singleton p)
  exact ((ContinuousLinearMap.apply ℂ (HighEnergySpace (-p) n)
    ((highEnergyEmbedding (-p) n).adjoint F)).continuous.tendsto
      (singularCommonEnergyInverse n e p p hn he g hg hs)).comp hQ

end Froehlich
