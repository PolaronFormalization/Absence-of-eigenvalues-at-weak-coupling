import Froehlich.Nodes.PT01CoreLeftLimitEnergy
import Froehlich.Nodes.PT01CutoffGraph
import Froehlich.Nodes.FC02

/-! The regular-source left side passes to the cutoff limit in the actual
number-form and L² field norms. No free operator-graph convergence occurs. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

def ptRegularCutoffNumberVector (F : HighSectorSpace n) (Lambda : GW.Operators.PositiveCutoff) : NumberFormSpace :=
  energyNumberCoordinates (-p) (ptRegularCutoffEnergyVector n e p hn he g hg hs F Lambda : EnergySpace (-p))

def ptRegularSingularNumberVector (F : HighSectorSpace n) : NumberFormSpace :=
  energyNumberCoordinates (-p) (auxiliaryPhysicalEnergySolution n e p hn he g hg hs F : EnergySpace (-p))

theorem ptRegularCutoffNumberVector_physical (F : HighSectorSpace n) (Lambda : GW.Operators.PositiveCutoff) :
    numberFormEmbedding (ptRegularCutoffNumberVector n e p hn he g hg hs F Lambda)=
      (cutoffAuxiliaryResolvent n e p he Lambda g hg hs F : GW.Fock.Carrier) := by
  rw [ptRegularCutoffNumberVector,energyNumberCoordinates_intertwines]
  have h := congrArg (fun v : HighSectorSpace n => (v : GW.Fock.Carrier))
    (ptRegularCutoffEnergyVector_physical n e p hn he g hg hs F Lambda)
  rw [highEnergyEmbedding_apply] at h
  exact h

theorem ptRegularSingularNumberVector_physical (F : HighSectorSpace n) :
    numberFormEmbedding (ptRegularSingularNumberVector n e p hn he g hg hs F)=
      (auxiliaryResolvent n e p he g hg hs F : GW.Fock.Carrier) := by
  rw [ptRegularSingularNumberVector,energyNumberCoordinates_intertwines]
  have h := congrArg (fun v : HighSectorSpace n => (v : GW.Fock.Carrier))
    (auxiliaryResolvent_solution_embedding n e p hn he g hg hs F)
  rw [highEnergyEmbedding_apply] at h
  exact h

theorem ptRegularCutoffNumberVector_eq_graph (F : HighSectorSpace n) (Lambda : GW.Operators.PositiveCutoff) :
    ptRegularCutoffNumberVector n e p hn he g hg hs F Lambda=
      freeGraphNumberCoordinates (-p) (cutoffAuxiliaryGraphCoordinate n e p hn he Lambda g hg hs F) := by
  apply numberFormEmbedding_injective
  rw [ptRegularCutoffNumberVector_physical,freeGraphNumberCoordinates_embedding,cutoffAuxiliaryGraphCoordinate_physical]

theorem ptRegularCutoffNumberVector_tendsto (F : HighSectorSpace n) :
    Tendsto (ptRegularCutoffNumberVector n e p hn he g hg hs F) atTop
      (𝓝 (ptRegularSingularNumberVector n e p hn he g hg hs F)) := by
  let N : HighEnergySpace (-p) n →L[ℂ] NumberFormSpace :=
    (energyNumberCoordinates (-p)).comp (HighEnergySpace (-p) n).subtypeL
  have h := (N.continuous.tendsto (ptRegularSingularEnergyVector n e p hn he g hg hs F)).comp
    (ptRegularCutoffEnergyVector_tendsto n e p hn he g hg hs F)
  have hN : N (ptRegularSingularEnergyVector n e p hn he g hg hs F)=
      ptRegularSingularNumberVector n e p hn he g hg hs F := by
    rw [ptRegularSingularEnergyVector_eq_solution]
    rfl
  change Tendsto (fun Lambda : GW.Operators.PositiveCutoff => ptRegularCutoffNumberVector n e p hn he g hg hs F Lambda)
    atTop (𝓝 (N (ptRegularSingularEnergyVector n e p hn he g hg hs F))) at h
  rw [hN] at h
  exact h

theorem regularCutoff_annihilation_global_tendsto (F : HighSectorSpace n) :
    Tendsto (fun Lambda : GW.Operators.PositiveCutoff => annihilationField
      (freeGraphNumberCoordinates (-p) (cutoffAuxiliaryGraphCoordinate n e p hn he Lambda g hg hs F))) atTop
      (𝓝 (annihilationField (ptRegularSingularNumberVector n e p hn he g hg hs F))) := by
  have h := (annihilationField.continuous.tendsto (ptRegularSingularNumberVector n e p hn he g hg hs F)).comp
    (ptRegularCutoffNumberVector_tendsto n e p hn he g hg hs F)
  simpa only [Function.comp_def,ptRegularCutoffNumberVector_eq_graph] using h

theorem regularCutoff_annihilation_local_tendsto (F : HighSectorSpace n) (K : Set GW.Space) :
    Tendsto (fun Lambda : GW.Operators.PositiveCutoff =>
      LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K
        (annihilationField (freeGraphNumberCoordinates (-p)
          (cutoffAuxiliaryGraphCoordinate n e p hn he Lambda g hg hs F)))) atTop
      (𝓝 (LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K
        (annihilationField (ptRegularSingularNumberVector n e p hn he g hg hs F)))) :=
  ((LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K).continuous.tendsto _).comp
    (regularCutoff_annihilation_global_tendsto n e p hn he g hg hs F)

end Froehlich
