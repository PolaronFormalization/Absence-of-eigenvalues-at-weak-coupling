import Froehlich.Nodes.RS03StaticReflection
import Froehlich.Nodes.SY01CompressedForms

set_option autoImplicit false

/-! KE01 begins with symmetries of the actual singular source solution.
Uniqueness is on the complete original high-energy domain. -/
noncomputable section
namespace Froehlich

variable (e : ℝ) (p : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

theorem auxiliaryGroundSourceEnergy_conjugation :
    highEnergyConjugation (-p) 1 (auxiliaryGroundSourceEnergy e p he g hg hs) =
      auxiliaryGroundSourceEnergy e p he g hg hs := by
  apply rs03GroundSourceEnergy_unique e p he g hg hs
  have hx (w : HighEnergySpace (-p) 1) :
      (compressedFiberFormData g (-p) 1 none).form w (auxiliaryGroundSourceEnergy e p he g hg hs)-
        (e : ℂ)*inner ℂ (highEnergyEmbedding (-p) 1 w)
          (highEnergyEmbedding (-p) 1 (auxiliaryGroundSourceEnergy e p he g hg hs)) =
        highFiberSourceLoad g (-p) 1 w := auxiliaryGroundSourceEnergy_weak e p he g hg hs w
  have hc := compressedWeak_conjugation g e (-p) 1 none (highFiberSourceLoad g (-p) 1)
    (auxiliaryGroundSourceEnergy e p he g hg hs) hx
  intro w
  exact (hc w).trans (highFiberSourceLoad_conjugation g (-p) 1 w)

theorem auxiliaryGroundSourceVector_conjugation :
    fockConjugation (auxiliaryGroundSourceVector e p he g hg hs) =
      auxiliaryGroundSourceVector e p he g hg hs := by
  have h := congrArg (fun u : HighEnergySpace (-p) 1 => energyEmbedding (-p) (u : EnergySpace (-p)))
    (auxiliaryGroundSourceEnergy_conjugation e p he g hg hs)
  change energyEmbedding (-p) (energyConjugation (-p)
    (auxiliaryGroundSourceEnergy e p he g hg hs : EnergySpace (-p))) = _ at h
  rw [energyConjugation_intertwines] at h
  exact h

theorem auxiliaryGroundSourceVector_reflection :
    fockReflection (auxiliaryGroundSourceVector e p he g hg hs) =
      auxiliaryGroundSourceVector e (-p) he g hg hs := by
  have h := congrArg (fun u : HighEnergySpace (-(-p)) 1 =>
      energyEmbedding (-(-p)) (u : EnergySpace (-(-p))))
    (auxiliaryGroundSourceEnergy_reflection e p he g hg hs)
  change energyEmbedding (-(-p)) (energyReflection (-p)
    (auxiliaryGroundSourceEnergy e p he g hg hs : EnergySpace (-p))) = _ at h
  rw [energyReflection_intertwines] at h
  exact h

end Froehlich
