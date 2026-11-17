import Froehlich.Nodes.UV01SourceAnchors
import Froehlich.Nodes.UV01PhysicalResolvent
import Froehlich.Nodes.FB02VacuumColumn
import Froehlich.Nodes.FC02

/-! PT02 starts with the genuine cutoff one-particle vector. The singular
form factor is never used as a physical one-particle Hilbert vector. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def cutoffOneParticleSource (g : ℝ) (Λ : GW.Operators.PositiveCutoff) : HighSectorSpace 1 :=
  ⟨oneParticleInclusion (cutoffFormFactorL2 g Λ.val Λ.property), by
    apply (highSector_mem_iff 1 _).mpr
    apply lp.ext
    funext m
    rw [highSectorProjection_apply]
    by_cases hm : 1 ≤ m
    · rw [if_pos hm]
    · rw [if_neg hm,oneParticleInclusion_apply,
        lp.single_apply_ne 2 1 (oneParticleCoordinate (cutoffFormFactorL2 g Λ.val Λ.property))
          (by omega : m ≠ 1)]⟩

theorem cutoffOneParticleSource_number (g : ℝ) (Λ : GW.Operators.PositiveCutoff) :
    numberFormEmbedding (numberOneParticleLift (cutoffFormFactorL2 g Λ.val Λ.property)) =
      (cutoffOneParticleSource g Λ : GW.Fock.Carrier) :=
  numberFormEmbedding_oneParticleLift _

theorem cutoffOneParticleSource_load (g : ℝ) (Λ : GW.Operators.PositiveCutoff)
    (p : GW.Space) (w : HighEnergySpace (-p) 1) :
    cutoffHighFiberSourceLoad g (-p) 1 Λ.val w =
      ⟪highEnergyEmbedding (-p) 1 w,cutoffOneParticleSource g Λ⟫_ℂ := by
  change cutoffFiberSourceLoad g (-p) Λ.val (w : EnergySpace (-p)) = _
  rw [cutoffFiberSourceLoad_eq_inner]
  have h := congrArg (starRingEnd ℂ)
    (oneParticleInclusion_pairing (cutoffFormFactorL2 g Λ.val Λ.property)
      (energyEmbedding (-p) (w : EnergySpace (-p))))
  change ⟪oneParticleExtraction (energyEmbedding (-p) (w : EnergySpace (-p))),
      cutoffFormFactorL2 g Λ.val Λ.property⟫_ℂ =
    ⟪energyEmbedding (-p) (w : EnergySpace (-p)),
      oneParticleInclusion (cutoffFormFactorL2 g Λ.val Λ.property)⟫_ℂ
  simpa only [Complex.star_def,inner_conj_symm] using! h.symm

theorem cutoffOneParticleSource_loadRiesz (g : ℝ) (Λ : GW.Operators.PositiveCutoff)
    (p : GW.Space) :
    loadRiesz (cutoffHighFiberSourceLoad g (-p) 1 Λ.val) =
      (highEnergyEmbedding (-p) 1).adjoint (cutoffOneParticleSource g Λ) := by
  apply Eq.symm
  apply loadRiesz_unique
  intro w
  rw [cutoffOneParticleSource_load]
  exact ((highEnergyEmbedding (-p) 1).adjoint_inner_right w (cutoffOneParticleSource g Λ)).symm

variable (e : ℝ) (p : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem cutoffGroundSourceEnergy_eq_physicalLoad (Λ : GW.Operators.PositiveCutoff) :
    cutoffGroundSourceEnergy e p he g hg hs Λ =
      cutoffAuxiliaryEnergyInverse 1 e p (by norm_num) he g hg hs Λ
        ((highEnergyEmbedding (-p) 1).adjoint (cutoffOneParticleSource g Λ)) := by
  rw [←cutoffOneParticleSource_loadRiesz,cutoffAuxiliaryEnergyInverse_load]
  rfl

theorem cutoffGroundSourceEnergy_physical (Λ : GW.Operators.PositiveCutoff) :
    highEnergyEmbedding (-p) 1 (cutoffGroundSourceEnergy e p he g hg hs Λ) =
      cutoffAuxiliaryResolvent 1 e p he Λ g hg hs (cutoffOneParticleSource g Λ) := by
  rw [cutoffGroundSourceEnergy_eq_physicalLoad]
  have h := congrArg (fun T : HighSectorSpace 1 →L[ℂ] HighSectorSpace 1 =>
      T (cutoffOneParticleSource g Λ))
    (cutoffCompressedEnergyInverse_physical 1 e p (by norm_num) he Λ g hg hs)
  exact h

end Froehlich
