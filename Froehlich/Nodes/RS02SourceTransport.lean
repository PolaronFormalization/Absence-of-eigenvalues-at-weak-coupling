import Froehlich.Nodes.RS02NormalizedSource

/-! The singular source is invariant under actual momentum graph-coordinate
changes. This is an equality of continuous energy-dual loads. -/
noncomputable section
namespace Froehlich

theorem fiberSourceLoad_coordinateChange (g : ℝ) (P Q : GW.Space) (u : EnergySpace Q) :
    fiberSourceLoad g P (energyCoordinateChange P Q u) = fiberSourceLoad g Q u := by
  rw [fiberSourceLoad_integral,fiberSourceLoad_integral,energyCoordinateChange_intertwines]

theorem fiberSourceLoad_comp_coordinateChange (g : ℝ) (P Q : GW.Space) :
    (fiberSourceLoad g P).comp (energyCoordinateChange P Q) = fiberSourceLoad g Q := by
  apply ContinuousLinearMap.ext
  intro u
  exact fiberSourceLoad_coordinateChange g P Q u

end Froehlich
