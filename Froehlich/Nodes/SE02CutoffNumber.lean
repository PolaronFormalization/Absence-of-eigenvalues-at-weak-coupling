import Froehlich.Nodes.SE01
import Froehlich.Nodes.KA01NumberPairing

/-! Genuine number-domain representatives of the fixed cutoff source and
its high component. The annihilation split is an equality of L² fields,
not a parameter-dependent scalar test assertion. -/
noncomputable section
open MeasureTheory
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

def se02CutoffHighNumber (Λ : GW.Operators.PositiveCutoff) : NumberFormSpace :=
  energyNumberCoordinates 0 (cutoffGroundSourceHighEnergy e he g hg hs Λ : EnergySpace 0)

theorem se02CutoffSourceNumber_physical (Λ : GW.Operators.PositiveCutoff) :
    numberFormEmbedding (cutoffGroundSourceNumber e 0 he g hg hs Λ) =
      cutoffThresholdSourceVector e he g hg hs Λ 0 :=
  energyNumberCoordinates_intertwines (-(0 : GW.Space)) _

theorem se02CutoffHighNumber_physical (Λ : GW.Operators.PositiveCutoff) :
    numberFormEmbedding (se02CutoffHighNumber e he g hg hs Λ) =
      energyEmbedding 0 (cutoffGroundSourceHighEnergy e he g hg hs Λ : EnergySpace 0) :=
  energyNumberCoordinates_intertwines 0 _

theorem se02CutoffHighNumber_high (Λ : GW.Operators.PositiveCutoff) :
    numberFormEmbedding (se02CutoffHighNumber e he g hg hs Λ) ∈ HighSectorSpace 2 := by
  rw [se02CutoffHighNumber_physical]
  exact (highEnergyEmbedding 0 2 (cutoffGroundSourceHighEnergy e he g hg hs Λ)).property

theorem se02CutoffSourceNumber_decomposition (Λ : GW.Operators.PositiveCutoff) :
    cutoffGroundSourceNumber e 0 he g hg hs Λ =
      numberOneParticleLift (oneParticleEnergyEmbedding 0 (cutoffGroundSourceOneEnergy e he g hg hs Λ)) +
        se02CutoffHighNumber e he g hg hs Λ := by
  apply numberFormEmbedding_injective
  rw [map_add,numberFormEmbedding_oneParticleLift,se02CutoffHighNumber_physical,
    se02CutoffSourceNumber_physical]
  have h := congrArg (energyEmbedding 0) (cutoffGroundSource_one_high_decomposition e he g hg hs Λ)
  rw [map_add,onePhononEnergyLift_physical,cutoffGroundSourceZeroEnergy_physical] at h
  exact h.symm

theorem se02CutoffSource_annihilation_split (Λ : GW.Operators.PositiveCutoff) :
    ∀ᵐ k ∂volume, annihilationField (cutoffGroundSourceNumber e 0 he g hg hs Λ) k =
      oneParticleEnergyEmbedding 0 (cutoffGroundSourceOneEnergy e he g hg hs Λ) k • GW.Fock.vacuum +
        annihilationField (se02CutoffHighNumber e he g hg hs Λ) k := by
  have h := congrArg annihilationField (se02CutoffSourceNumber_decomposition e he g hg hs Λ)
  rw [map_add] at h
  filter_upwards [Lp.coeFn_add
    (annihilationField (numberOneParticleLift (oneParticleEnergyEmbedding 0 (cutoffGroundSourceOneEnergy e he g hg hs Λ))))
    (annihilationField (se02CutoffHighNumber e he g hg hs Λ)),
    coreAnnihilationField_oneParticle (oneParticleEnergyEmbedding 0 (cutoffGroundSourceOneEnergy e he g hg hs Λ))]
    with k hadd hone
  rw [h,hadd]
  simp only [Pi.add_apply]
  rw [hone]

theorem se02CutoffHigh_annihilation_high (Λ : GW.Operators.PositiveCutoff) :
    ∀ᵐ k ∂volume, annihilationField (se02CutoffHighNumber e he g hg hs Λ) k ∈ HighSectorSpace 1 :=
  annihilationField_mem_high_of_number_high 1 (se02CutoffHighNumber e he g hg hs Λ)
    (se02CutoffHighNumber_high e he g hg hs Λ)

end Froehlich
