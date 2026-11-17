import Froehlich.Nodes.GW06

/-! Actual closed particle-sector subspaces, using native closed kernels. -/
noncomputable section
namespace Froehlich

abbrev HighSectorSpace (n : ℕ) :=
  (ContinuousLinearMap.id ℂ GW.Fock.Carrier - highSectorProjection n).ker

abbrev HighEnergySpace (P : GW.Space) (n : ℕ) :=
  (ContinuousLinearMap.id ℂ (EnergySpace P) - energyHighProjection P n).ker

theorem highSector_mem_iff (n : ℕ) (u : GW.Fock.Carrier) :
    u ∈ HighSectorSpace n ↔ highSectorProjection n u = u := by
  change u - highSectorProjection n u = 0 ↔ highSectorProjection n u = u
  exact sub_eq_zero.trans eq_comm

theorem highEnergy_mem_iff (P : GW.Space) (n : ℕ) (u : EnergySpace P) :
    u ∈ HighEnergySpace P n ↔ energyHighProjection P n u = u := by
  change u - energyHighProjection P n u = 0 ↔ energyHighProjection P n u = u
  exact sub_eq_zero.trans eq_comm

theorem energyHighProjection_idempotent_apply (P : GW.Space) (n : ℕ) (u : EnergySpace P) :
    energyHighProjection P n (energyHighProjection P n u) = energyHighProjection P n u := by
  apply energyEmbedding_injective P
  rw [energyHighProjection_intertwines, energyHighProjection_intertwines]
  exact congrArg (fun f : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier => f (energyEmbedding P u))
    (highSectorProjection_idempotent n)

def highSectorProject (n : ℕ) : GW.Fock.Carrier →L[ℂ] HighSectorSpace n :=
  (highSectorProjection n).codRestrict _ (fun u => (highSector_mem_iff n _).mpr
    (congrArg (fun f : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier => f u)
      (highSectorProjection_idempotent n)))

def highEnergyProject (P : GW.Space) (n : ℕ) : EnergySpace P →L[ℂ] HighEnergySpace P n :=
  (energyHighProjection P n).codRestrict _ (fun u => (highEnergy_mem_iff P n _).mpr
    (energyHighProjection_idempotent_apply P n u))

theorem highSectorProject_surjective (n : ℕ) : Function.Surjective (highSectorProject n) := by
  intro u
  refine ⟨(u : GW.Fock.Carrier), ?_⟩
  apply Subtype.ext
  exact (highSector_mem_iff n u).mp u.property

def highEnergyEmbedding (P : GW.Space) (n : ℕ) : HighEnergySpace P n →L[ℂ] HighSectorSpace n :=
  ((energyEmbedding P).comp (HighEnergySpace P n).subtypeL).codRestrict _ (by
    intro u
    apply (highSector_mem_iff n _).mpr
    change highSectorProjection n (energyEmbedding P u) = energyEmbedding P u
    rw [← energyHighProjection_intertwines, (highEnergy_mem_iff P n u).mp u.property])

theorem highEnergyEmbedding_apply (P : GW.Space) (n : ℕ) (u : HighEnergySpace P n) :
    (highEnergyEmbedding P n u : GW.Fock.Carrier) = energyEmbedding P u := rfl

end Froehlich
