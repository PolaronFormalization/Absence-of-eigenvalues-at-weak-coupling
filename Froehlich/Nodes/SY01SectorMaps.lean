import Froehlich.Nodes.SY01NumberMaps
import Froehlich.Nodes.GW06Sectors

/-! Sector compatibility of the actual physical and energy symmetries. -/
noncomputable section
namespace Froehlich

theorem sectorConjugation_zero (n : ℕ) : sectorConjugation n 0 = 0 := by
  simpa only [zero_smul, map_zero] using sectorConjugation_smul n (0 : ℂ) (0 : GW.Fock.Sector n)

theorem fockConjugation_highProjection (m : ℕ) (u : GW.Fock.Carrier) :
    fockConjugation (highSectorProjection m u) = highSectorProjection m (fockConjugation u) := by
  apply lp.ext
  funext n
  by_cases hn : m ≤ n <;>
    simp [highSectorProjection_apply, hn, fockConjugation, sectorConjugation_zero]

theorem fockReflection_highProjection (m : ℕ) (u : GW.Fock.Carrier) :
    fockReflection (highSectorProjection m u) = highSectorProjection m (fockReflection u) := by
  apply lp.ext
  funext n
  by_cases hn : m ≤ n <;>
    simp [highSectorProjection_apply, hn, fockReflection, GW.Spaces.diagonalMap_apply]

theorem energyConjugation_highProjection (P : GW.Space) (m : ℕ) (u : EnergySpace P) :
    energyConjugation P (energyHighProjection P m u) = energyHighProjection P m (energyConjugation P u) := by
  apply energyEmbedding_injective P
  rw [energyConjugation_intertwines,energyHighProjection_intertwines,
    energyHighProjection_intertwines,energyConjugation_intertwines,fockConjugation_highProjection]

theorem energyReflection_highProjection (P : GW.Space) (m : ℕ) (u : EnergySpace P) :
    energyReflection P (energyHighProjection P m u) = energyHighProjection (-P) m (energyReflection P u) := by
  apply energyEmbedding_injective (-P)
  rw [energyReflection_intertwines,energyHighProjection_intertwines,
    energyHighProjection_intertwines,energyReflection_intertwines,fockReflection_highProjection]

theorem highSector_conjugation_mem (n : ℕ) (u : HighSectorSpace n) : fockConjugation u ∈ HighSectorSpace n := by
  apply (highSector_mem_iff n _).mpr
  have hu : highSectorProjection n (u : GW.Fock.Carrier) = (u : GW.Fock.Carrier) :=
    (highSector_mem_iff n (u : GW.Fock.Carrier)).mp u.property
  rw [← fockConjugation_highProjection,hu]

theorem highSector_reflection_mem (n : ℕ) (u : HighSectorSpace n) : fockReflection u ∈ HighSectorSpace n := by
  apply (highSector_mem_iff n _).mpr
  have hu : highSectorProjection n (u : GW.Fock.Carrier) = (u : GW.Fock.Carrier) :=
    (highSector_mem_iff n (u : GW.Fock.Carrier)).mp u.property
  rw [← fockReflection_highProjection,hu]

theorem highEnergy_conjugation_mem (P : GW.Space) (n : ℕ) (u : HighEnergySpace P n) :
    energyConjugation P u ∈ HighEnergySpace P n := by
  apply (highEnergy_mem_iff P n _).mpr
  have hu : energyHighProjection P n (u : EnergySpace P) = (u : EnergySpace P) :=
    (highEnergy_mem_iff P n (u : EnergySpace P)).mp u.property
  rw [← energyConjugation_highProjection,hu]

theorem highEnergy_reflection_mem (P : GW.Space) (n : ℕ) (u : HighEnergySpace P n) :
    energyReflection P u ∈ HighEnergySpace (-P) n := by
  apply (highEnergy_mem_iff (-P) n _).mpr
  have hu : energyHighProjection P n (u : EnergySpace P) = (u : EnergySpace P) :=
    (highEnergy_mem_iff P n (u : EnergySpace P)).mp u.property
  rw [← energyReflection_highProjection,hu]

def highEnergyConjugation (P : GW.Space) (n : ℕ) (u : HighEnergySpace P n) : HighEnergySpace P n :=
  ⟨energyConjugation P u,highEnergy_conjugation_mem P n u⟩

def highEnergyReflection (P : GW.Space) (n : ℕ) (u : HighEnergySpace P n) : HighEnergySpace (-P) n :=
  ⟨energyReflection P u,highEnergy_reflection_mem P n u⟩

def highSectorConjugation (n : ℕ) (u : HighSectorSpace n) : HighSectorSpace n :=
  ⟨fockConjugation u,highSector_conjugation_mem n u⟩

def highSectorReflection (n : ℕ) (u : HighSectorSpace n) : HighSectorSpace n :=
  ⟨fockReflection u,highSector_reflection_mem n u⟩

end Froehlich
