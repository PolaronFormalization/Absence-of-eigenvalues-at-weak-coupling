import Froehlich.Nodes.RS01WeightedSpace

/-! Exact supported multiplier formulas and invisibility of every
below-cutoff weight value on the actual auxiliary high energy space. -/
noncomputable section
open MeasureTheory Filter
namespace Froehlich

theorem auxiliaryEnergyCoordinates_val (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (u : AuxiliaryEnergySpace n e p he) :
    (auxiliaryEnergyCoordinates n e p he u : GW.Fock.Carrier) =
      auxiliaryWeightedCoordinates n e p he (u : AuxiliaryFullEnergy n e p he) := rfl

theorem auxiliaryEnergyEmbedding_val (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (u : AuxiliaryEnergySpace n e p he) :
    (auxiliaryEnergyEmbedding n e p he u : GW.Fock.Carrier) =
      auxiliaryFullEmbedding n e p he (u : AuxiliaryFullEnergy n e p he) := rfl

theorem auxiliaryCoordinates_below (n m : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (u : AuxiliaryEnergySpace n e p he) (hmn : m < n) :
    auxiliaryWeightedCoordinates n e p he (u : AuxiliaryFullEnergy n e p he) m = 0 := by
  have h := (highSector_mem_iff n (auxiliaryEnergyCoordinates n e p he u)).mp
    (auxiliaryEnergyCoordinates n e p he u).property
  rw [auxiliaryEnergyCoordinates_val] at h
  have hm := congrArg (fun v : GW.Fock.Carrier => v m) h
  rw [highSectorProjection_apply,if_neg (Nat.not_le.mpr hmn)] at hm
  exact hm.symm

theorem auxiliaryPhysical_below (n m : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (u : AuxiliaryEnergySpace n e p he) (hmn : m < n) :
    auxiliaryFullEmbedding n e p he (u : AuxiliaryFullEnergy n e p he) m = 0 := by
  have h := (highSector_mem_iff n (auxiliaryEnergyEmbedding n e p he u)).mp
    (auxiliaryEnergyEmbedding n e p he u).property
  rw [auxiliaryEnergyEmbedding_val] at h
  have hm := congrArg (fun v : GW.Fock.Carrier => v m) h
  rw [highSectorProjection_apply,if_neg (Nat.not_le.mpr hmn)] at hm
  exact hm.symm

theorem auxiliaryWeightedCoordinates_physical (n m : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (u : AuxiliaryEnergySpace n e p he) :
    (fun K => (auxiliaryWeight n e p m K : ℂ) * physicalSector m
      (auxiliaryFullEmbedding n e p he (u : AuxiliaryFullEnergy n e p he) m) K) =ᵐ[GW.Fock.sectorMeasure m]
      physicalSector m (auxiliaryWeightedCoordinates n e p he (u : AuxiliaryFullEnergy n e p he) m) := by
  have h := fockWeightedCoordinates_physical (auxiliaryWeight n e p)
    (auxiliaryWeight_measurable n e p) (fun m K => auxiliaryWeight_ge_one n m e p he K)
    (fun m tau K => auxiliaryWeight_permutation n m e p tau K)
    (u : AuxiliaryFullEnergy n e p he) m
  have hi := fockWeightedInclusion_apply (auxiliaryWeight n e p)
    (auxiliaryWeight_measurable n e p) (fun m K => auxiliaryWeight_ge_one n m e p he K)
    (fun m tau K => auxiliaryWeight_permutation n m e p tau K)
    (u : AuxiliaryFullEnergy n e p he)
  change auxiliaryFullEmbedding n e p he (u : AuxiliaryFullEnergy n e p he) = _ at hi
  rw [hi]
  exact h

theorem auxiliaryLiteralWeight_physical (n m : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (u : AuxiliaryEnergySpace n e p he) (hnm : n ≤ m) :
    (fun K => (Real.sqrt (freeSymbol (-p) m K + 1 - (n : ℝ) - e) : ℂ) * physicalSector m
      (auxiliaryFullEmbedding n e p he (u : AuxiliaryFullEnergy n e p he) m) K) =ᵐ[GW.Fock.sectorMeasure m]
      physicalSector m (auxiliaryWeightedCoordinates n e p he (u : AuxiliaryFullEnergy n e p he) m) := by
  simpa only [auxiliaryWeight_of_ge n m e p hnm] using
    auxiliaryWeightedCoordinates_physical n m e p he u

/-- An arbitrary multiplier on a discarded sector acts as zero. Hence the
extension value one below n has no mathematical effect on this space. -/
theorem auxiliaryBelow_multiplier_zero (n m : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (u : AuxiliaryEnergySpace n e p he) (hmn : m < n) (b : GW.Fock.Coordinates m → ℂ) :
    (fun K => b K * physicalSector m
      (auxiliaryFullEmbedding n e p he (u : AuxiliaryFullEnergy n e p he) m) K) =ᵐ[GW.Fock.sectorMeasure m]
      (fun _ => (0 : ℂ)) := by
  rw [auxiliaryPhysical_below n m e p he u hmn,map_zero]
  filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := GW.Fock.sectorMeasure m)] with K hK
  simp only [hK,Pi.zero_apply,mul_zero]

end Froehlich
