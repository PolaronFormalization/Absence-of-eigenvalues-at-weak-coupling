import Froehlich.Nodes.CA02FixedEnergyCoordinates

set_option autoImplicit false

/-! Every fixed-energy jet is the same physical multiplier as its physical
jet. In particular the weighted C3 family at order zero is the source G. -/
noncomputable section
open MeasureTheory Filter
namespace Froehlich

theorem auxiliaryFixedEnergyWeightJet_physical (is : List (Fin 3)) (n : ℕ) (e : ℝ)
    (p0 p : GW.Space) (he : e ≤ 0) :
    (auxiliaryEnergyEmbedding n e p0 he).comp (auxiliaryFixedEnergyWeightJet is n e p0 p he) =
      auxiliaryPhysicalWeightJet is n e p he := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply lp.ext
  funext m
  apply (physicalSector m).injective
  apply Lp.ext
  let u := auxiliaryFixedEnergyWeightJet is n e p0 p he f
  have hw := auxiliaryWeightedCoordinates_physical n m e p0 he u
  have hc := auxiliaryFixedEnergyJetCoordinates_ae is n m e p0 p he f
  have hg := auxiliaryPhysicalWeightJet_ae is n m e p he f
  change (fun K => ((auxiliaryWeight n e p0 m K * auxiliaryInverseWeightJet is n e p m K : ℝ) : ℂ) •
      physicalSector m ((f : GW.Fock.Carrier) m) K) =ᵐ[GW.Fock.sectorMeasure m]
    physicalSector m (auxiliaryWeightedCoordinates n e p0 he (u : AuxiliaryFullEnergy n e p0 he) m) at hc
  filter_upwards [hw,hc,hg] with K hwK hcK hgK
  have hW : (auxiliaryWeight n e p0 m K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (zero_lt_one.trans_le (auxiliaryWeight_ge_one n m e p0 he K)))
  apply mul_left_cancel₀ hW
  change (auxiliaryWeight n e p0 m K : ℂ)*
      physicalSector m (auxiliaryFullEmbedding n e p0 he (u : AuxiliaryFullEnergy n e p0 he) m) K = _
  rw [hwK,← hcK,← hgK]
  simp only [Complex.ofReal_mul,smul_eq_mul]
  ring

theorem auxiliaryFixedEnergyWeightJet_zero_physical (n : ℕ) (e : ℝ)
    (p0 p : GW.Space) (he : e ≤ 0) :
    (auxiliaryEnergyEmbedding n e p0 he).comp (auxiliaryFixedEnergyWeightJet [] n e p0 p he) =
      auxiliaryPhysicalFreeInverse n e p he :=
  auxiliaryFixedEnergyWeightJet_physical [] n e p0 p he

end Froehlich
