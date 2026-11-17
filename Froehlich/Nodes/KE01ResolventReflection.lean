import Froehlich.Nodes.KE01ResolventSymmetry

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem auxiliaryPhysicalEnergySolution_reflection (f : HighSectorSpace n) :
    highEnergyReflection (-p) n (auxiliaryPhysicalEnergySolution n e p hn he g hg hs f) =
      auxiliaryPhysicalEnergySolution n e (-p) hn he g hg hs (highSectorReflection n f) := by
  apply ke01_shiftedWeak_unique n e (-p) hn he g hg hs
  intro w
  have hr := compressedWeak_reflection g (e-1+(n : ℝ)) (-p) n none
    (auxiliaryPhysicalLoad n p f) (auxiliaryPhysicalEnergySolution n e p hn he g hg hs f)
    (ke01_physicalEnergySolution_shiftedWeak n e p hn he g hg hs f)
  rw [hr w,ke01_physicalEnergySolution_shiftedWeak n e (-p) hn he g hg hs]
  change ⟪energyEmbedding (-p) ((energyReflection (-p)).symm (w : EnergySpace (-(-p)))),
    (f : GW.Fock.Carrier)⟫_ℂ =
      ⟪energyEmbedding (-(-p)) (w : EnergySpace (-(-p))),fockReflection (f : GW.Fock.Carrier)⟫_ℂ
  rw [energyReflection_symm_intertwines,fockReflection_inner_flip]

include hn in
theorem auxiliaryResolvent_reflection (f : HighSectorSpace n) :
    fockReflection (auxiliaryResolvent n e p he g hg hs f : GW.Fock.Carrier) =
      (auxiliaryResolvent n e (-p) he g hg hs (highSectorReflection n f) : GW.Fock.Carrier) := by
  have h := congrArg (fun u : HighEnergySpace (-(-p)) n =>
    energyEmbedding (-(-p)) (u : EnergySpace (-(-p))))
    (auxiliaryPhysicalEnergySolution_reflection n e p hn he g hg hs f)
  change energyEmbedding (-(-p)) (energyReflection (-p)
    (auxiliaryPhysicalEnergySolution n e p hn he g hg hs f : EnergySpace (-p))) = _ at h
  rw [energyReflection_intertwines] at h
  have hi (t : GW.Space) (u : HighSectorSpace n) :
      energyEmbedding (-t) (auxiliaryPhysicalEnergySolution n e t hn he g hg hs u : EnergySpace (-t)) =
        (auxiliaryResolvent n e t he g hg hs u : GW.Fock.Carrier) :=
    congrArg (fun v : HighSectorSpace n => (v : GW.Fock.Carrier))
      (auxiliaryResolvent_solution_embedding n e t hn he g hg hs u)
  rw [hi p f,hi (-p) (highSectorReflection n f)] at h
  exact h

include hn in
theorem auxiliaryExtendedResolvent_reflection (f : GW.Fock.Carrier) :
    fockReflection (auxiliaryExtendedResolvent n e p he g hg hs f) =
      auxiliaryExtendedResolvent n e (-p) he g hg hs (fockReflection f) := by
  have hp : highSectorReflection n (highSectorProject n f) = highSectorProject n (fockReflection f) := by
    apply Subtype.ext
    exact fockReflection_highProjection n f
  change fockReflection (auxiliaryResolvent n e p he g hg hs (highSectorProject n f) : GW.Fock.Carrier) = _
  rw [auxiliaryResolvent_reflection n e p hn he g hg hs,hp]
  rfl

end Froehlich
