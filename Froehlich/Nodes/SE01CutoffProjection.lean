import Froehlich.Nodes.SE01SourceProjection
import Froehlich.Nodes.PT03KernelDefinitions

/-! Actual cutoff h₀,Λ and its one/high projections, at the SAME fixed e.
No assertion that e is a cutoff eigenvalue is made or needed. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

def cutoffGroundSourceZeroEnergy (Λ : GW.Operators.PositiveCutoff) : HighEnergySpace 0 1 :=
  highEnergyCoordinateChange 0 (-(0 : GW.Space)) 1 (cutoffGroundSourceEnergy e 0 he g hg hs Λ)

def cutoffGroundSourceOneEnergy (Λ : GW.Operators.PositiveCutoff) : OneParticleEnergySpace 0 :=
  oneParticleEnergyProjection 0 (cutoffGroundSourceZeroEnergy e he g hg hs Λ : EnergySpace 0)

def cutoffGroundSourceHighEnergy (Λ : GW.Operators.PositiveCutoff) : HighEnergySpace 0 2 :=
  highEnergyProject 0 2 (cutoffGroundSourceZeroEnergy e he g hg hs Λ : EnergySpace 0)

theorem cutoffGroundSourceZeroEnergy_val (Λ : GW.Operators.PositiveCutoff) :
    (cutoffGroundSourceZeroEnergy e he g hg hs Λ : EnergySpace 0) =
      (cutoffGroundSourceEnergy e 0 he g hg hs Λ : EnergySpace (-(0 : GW.Space))) := by
  have h := congrArg (fun u : HighSectorSpace 1 => (u : GW.Fock.Carrier))
    (highEnergyCoordinateChange_physical 0 (-(0 : GW.Space)) 1 (cutoffGroundSourceEnergy e 0 he g hg hs Λ))
  change energyEmbedding 0 (cutoffGroundSourceZeroEnergy e he g hg hs Λ : EnergySpace 0) =
    energyEmbedding (-(0 : GW.Space))
      (cutoffGroundSourceEnergy e 0 he g hg hs Λ : EnergySpace (-(0 : GW.Space))) at h
  rw [neg_zero] at h
  exact energyEmbedding_injective 0 h

theorem cutoffGroundSourceZeroEnergy_physical (Λ : GW.Operators.PositiveCutoff) :
    energyEmbedding 0 (cutoffGroundSourceZeroEnergy e he g hg hs Λ : EnergySpace 0) =
      cutoffThresholdSourceVector e he g hg hs Λ 0 := by
  exact congrArg (fun u : HighSectorSpace 1 => (u : GW.Fock.Carrier))
    (highEnergyCoordinateChange_physical 0 (-(0 : GW.Space)) 1 (cutoffGroundSourceEnergy e 0 he g hg hs Λ))

theorem cutoffGroundSourceOneEnergy_physical (Λ : GW.Operators.PositiveCutoff) :
    oneParticleEnergyEmbedding 0 (cutoffGroundSourceOneEnergy e he g hg hs Λ) =
      oneParticleExtraction (cutoffThresholdSourceVector e he g hg hs Λ 0) := by
  rw [cutoffGroundSourceOneEnergy,oneParticleEnergyProjection_intertwines,cutoffGroundSourceZeroEnergy_physical]

theorem cutoffGroundSourceHighEnergy_physical (Λ : GW.Operators.PositiveCutoff) :
    energyEmbedding 0 (cutoffGroundSourceHighEnergy e he g hg hs Λ : EnergySpace 0) =
      highSectorProjection 2 (cutoffThresholdSourceVector e he g hg hs Λ 0) := by
  change energyEmbedding 0 (energyHighProjection 0 2 (cutoffGroundSourceZeroEnergy e he g hg hs Λ : EnergySpace 0)) = _
  rw [energyHighProjection_intertwines,cutoffGroundSourceZeroEnergy_physical]

theorem cutoffGroundSource_one_high_decomposition (Λ : GW.Operators.PositiveCutoff) :
    onePhononEnergyLift 0 (cutoffGroundSourceOneEnergy e he g hg hs Λ) +
      (cutoffGroundSourceHighEnergy e he g hg hs Λ : EnergySpace 0) =
      (cutoffGroundSourceZeroEnergy e he g hg hs Λ : EnergySpace 0) := by
  have h := energy_vacuum_one_high_decomposition 0
    (cutoffGroundSourceZeroEnergy e he g hg hs Λ : EnergySpace 0)
  rw [vacuumCoefficient_highEnergy,zero_smul,zero_add] at h
  exact h

theorem cutoffGroundSourceZeroEnergy_weak (Λ : GW.Operators.PositiveCutoff) (w : HighEnergySpace 0 1) :
    (fiberFormData g 0 (some Λ)).form (w : EnergySpace 0) (cutoffGroundSourceZeroEnergy e he g hg hs Λ : EnergySpace 0) -
      (e : ℂ)*⟪energyEmbedding 0 (w : EnergySpace 0),
        energyEmbedding 0 (cutoffGroundSourceZeroEnergy e he g hg hs Λ : EnergySpace 0)⟫_ℂ =
      cutoffHighFiberSourceLoad g 0 1 Λ.val w := by
  have hw := congrArg (fun u : HighSectorSpace 1 => (u : GW.Fock.Carrier))
    (highEnergyCoordinateChange_physical (-(0 : GW.Space)) 0 1 w)
  change energyEmbedding (-(0 : GW.Space))
    (highEnergyCoordinateChange (-(0 : GW.Space)) 0 1 w : EnergySpace (-(0 : GW.Space))) =
      energyEmbedding 0 (w : EnergySpace 0) at hw
  rw [neg_zero] at hw
  have hwv := energyEmbedding_injective 0 hw
  have h := cutoffGroundSourceEnergy_weak e 0 he g hg hs Λ
    (highEnergyCoordinateChange (-(0 : GW.Space)) 0 1 w)
  change (fiberFormData g (-(0 : GW.Space)) (some Λ)).form
      (highEnergyCoordinateChange (-(0 : GW.Space)) 0 1 w : EnergySpace (-(0 : GW.Space)))
      (cutoffGroundSourceEnergy e 0 he g hg hs Λ : EnergySpace (-(0 : GW.Space))) -
    (e : ℂ)*⟪energyEmbedding (-(0 : GW.Space))
      (highEnergyCoordinateChange (-(0 : GW.Space)) 0 1 w : EnergySpace (-(0 : GW.Space))),
      energyEmbedding (-(0 : GW.Space))
        (cutoffGroundSourceEnergy e 0 he g hg hs Λ : EnergySpace (-(0 : GW.Space)))⟫_ℂ =
    cutoffFiberSourceLoad g (-(0 : GW.Space)) Λ.val
      (highEnergyCoordinateChange (-(0 : GW.Space)) 0 1 w : EnergySpace (-(0 : GW.Space))) at h
  rw [neg_zero] at h
  rw [hwv,←cutoffGroundSourceZeroEnergy_val] at h
  exact h

end Froehlich
