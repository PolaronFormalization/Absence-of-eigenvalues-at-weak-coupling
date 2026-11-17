import Froehlich.Nodes.PT02SourceField
import Froehlich.Nodes.SP03OneParticleColumns
import Froehlich.Nodes.SP01EnergySplit

/-! The literal zero-momentum source and its one/high energy projections.
Only the canonical graph coordinate change is used to pass from -0 to 0. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

private theorem zeroHighEnergyChange_val (n : ℕ) (u : HighEnergySpace 0 n) :
    (highEnergyCoordinateChange (-(0 : GW.Space)) 0 n u : EnergySpace (-(0 : GW.Space))) =
      (u : EnergySpace 0) := by
  have h := congrArg (fun v : HighSectorSpace n => (v : GW.Fock.Carrier))
    (highEnergyCoordinateChange_physical (-(0 : GW.Space)) 0 n u)
  change energyEmbedding (-(0 : GW.Space))
    (highEnergyCoordinateChange (-(0 : GW.Space)) 0 n u : EnergySpace (-(0 : GW.Space))) =
      energyEmbedding 0 (u : EnergySpace 0) at h
  rw [neg_zero] at h
  exact energyEmbedding_injective 0 h

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

def groundSourceZeroEnergy : HighEnergySpace 0 1 :=
  highEnergyCoordinateChange 0 (-(0 : GW.Space)) 1 (auxiliaryGroundSourceEnergy e 0 he g hg hs)

def groundSourceOneEnergy : OneParticleEnergySpace 0 :=
  oneParticleEnergyProjection 0 (groundSourceZeroEnergy e he g hg hs : EnergySpace 0)

def groundSourceHighEnergy : HighEnergySpace 0 2 :=
  highEnergyProject 0 2 (groundSourceZeroEnergy e he g hg hs : EnergySpace 0)

theorem groundSourceZeroEnergy_val :
    (groundSourceZeroEnergy e he g hg hs : EnergySpace 0) =
      (auxiliaryGroundSourceEnergy e 0 he g hg hs : EnergySpace (-(0 : GW.Space))) := by
  have h := congrArg (fun v : HighSectorSpace 1 => (v : GW.Fock.Carrier))
    (highEnergyCoordinateChange_physical 0 (-(0 : GW.Space)) 1
      (auxiliaryGroundSourceEnergy e 0 he g hg hs))
  change energyEmbedding 0 (groundSourceZeroEnergy e he g hg hs : EnergySpace 0) =
    energyEmbedding (-(0 : GW.Space))
      (auxiliaryGroundSourceEnergy e 0 he g hg hs : EnergySpace (-(0 : GW.Space))) at h
  rw [neg_zero] at h
  exact energyEmbedding_injective 0 h

theorem groundSourceZeroEnergy_physical :
    energyEmbedding 0 (groundSourceZeroEnergy e he g hg hs : EnergySpace 0) =
      auxiliaryGroundSourceVector e 0 he g hg hs := by
  have h := congrArg (fun u : HighSectorSpace 1 => (u : GW.Fock.Carrier))
    (highEnergyCoordinateChange_physical 0 (-(0 : GW.Space)) 1
      (auxiliaryGroundSourceEnergy e 0 he g hg hs))
  exact h

theorem groundSourceOneEnergy_physical :
    oneParticleEnergyEmbedding 0 (groundSourceOneEnergy e he g hg hs) =
      oneParticleExtraction (auxiliaryGroundSourceVector e 0 he g hg hs) := by
  rw [groundSourceOneEnergy,oneParticleEnergyProjection_intertwines,groundSourceZeroEnergy_physical]

theorem groundSourceHighEnergy_physical :
    energyEmbedding 0 (groundSourceHighEnergy e he g hg hs : EnergySpace 0) =
      highSectorProjection 2 (auxiliaryGroundSourceVector e 0 he g hg hs) := by
  change energyEmbedding 0 (energyHighProjection 0 2 (groundSourceZeroEnergy e he g hg hs : EnergySpace 0)) = _
  rw [energyHighProjection_intertwines,groundSourceZeroEnergy_physical]

theorem groundSource_one_high_decomposition :
    onePhononEnergyLift 0 (groundSourceOneEnergy e he g hg hs) +
      (groundSourceHighEnergy e he g hg hs : EnergySpace 0) =
      (groundSourceZeroEnergy e he g hg hs : EnergySpace 0) := by
  have h := energy_vacuum_one_high_decomposition 0
    (groundSourceZeroEnergy e he g hg hs : EnergySpace 0)
  rw [vacuumCoefficient_highEnergy,zero_smul,zero_add] at h
  exact h

theorem groundSourceZeroEnergy_weak (w : HighEnergySpace 0 1) :
    (fiberFormData g 0 none).form (w : EnergySpace 0) (groundSourceZeroEnergy e he g hg hs : EnergySpace 0) -
      (e : ℂ)*⟪energyEmbedding 0 (w : EnergySpace 0),
        energyEmbedding 0 (groundSourceZeroEnergy e he g hg hs : EnergySpace 0)⟫_ℂ =
      highFiberSourceLoad g 0 1 w := by
  have h := auxiliaryGroundSourceEnergy_weak e 0 he g hg hs
    (highEnergyCoordinateChange (-(0 : GW.Space)) 0 1 w)
  change (fiberFormData g (-(0 : GW.Space)) none).form
      (highEnergyCoordinateChange (-(0 : GW.Space)) 0 1 w : EnergySpace (-(0 : GW.Space)))
      (auxiliaryGroundSourceEnergy e 0 he g hg hs : EnergySpace (-(0 : GW.Space))) -
    (e : ℂ)*⟪energyEmbedding (-(0 : GW.Space))
      (highEnergyCoordinateChange (-(0 : GW.Space)) 0 1 w : EnergySpace (-(0 : GW.Space))),
      energyEmbedding (-(0 : GW.Space))
        (auxiliaryGroundSourceEnergy e 0 he g hg hs : EnergySpace (-(0 : GW.Space)))⟫_ℂ =
    fiberSourceLoad g (-(0 : GW.Space))
      (highEnergyCoordinateChange (-(0 : GW.Space)) 0 1 w : EnergySpace (-(0 : GW.Space))) at h
  rw [zeroHighEnergyChange_val,←groundSourceZeroEnergy_val,neg_zero] at h
  exact h

end Froehlich
