import Froehlich.Nodes.KE01ResolventSymmetry
import Froehlich.Nodes.PT03KernelDefinitions

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

include hn in
theorem auxiliaryResolvent_conjugation (f : HighSectorSpace n) :
    fockConjugation (auxiliaryResolvent n e p he g hg hs f : GW.Fock.Carrier) =
      (auxiliaryResolvent n e p he g hg hs (highSectorConjugation n f) : GW.Fock.Carrier) := by
  have h := congrArg (fun u : HighEnergySpace (-p) n =>
    energyEmbedding (-p) (u : EnergySpace (-p)))
    (auxiliaryPhysicalEnergySolution_conjugation n e p hn he g hg hs f)
  change energyEmbedding (-p) (energyConjugation (-p)
    (auxiliaryPhysicalEnergySolution n e p hn he g hg hs f : EnergySpace (-p))) = _ at h
  rw [energyConjugation_intertwines] at h
  have hi (u : HighSectorSpace n) :
      energyEmbedding (-p) (auxiliaryPhysicalEnergySolution n e p hn he g hg hs u : EnergySpace (-p)) =
        (auxiliaryResolvent n e p he g hg hs u : GW.Fock.Carrier) :=
    congrArg (fun v : HighSectorSpace n => (v : GW.Fock.Carrier))
      (auxiliaryResolvent_solution_embedding n e p hn he g hg hs u)
  rw [hi f,hi (highSectorConjugation n f)] at h
  exact h

include hn in
theorem auxiliaryExtendedResolvent_conjugation (f : GW.Fock.Carrier) :
    fockConjugation (auxiliaryExtendedResolvent n e p he g hg hs f) =
      auxiliaryExtendedResolvent n e p he g hg hs (fockConjugation f) := by
  have hp : highSectorConjugation n (highSectorProject n f) =
      highSectorProject n (fockConjugation f) := by
    apply Subtype.ext
    exact fockConjugation_highProjection n f
  change fockConjugation (auxiliaryResolvent n e p he g hg hs (highSectorProject n f) : GW.Fock.Carrier) = _
  rw [auxiliaryResolvent_conjugation n e p hn he g hg hs,hp]
  rfl

end Froehlich
