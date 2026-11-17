import Froehlich.Nodes.RS01Sandwich
import Froehlich.Nodes.FD02MultiplierSymmetry

/-! The physical G is the literal reciprocal-weight multiplier. Its
selfadjointness makes G M⁻¹ G the source formula, without replacing G by G†. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

theorem auxiliaryPhysicalFreeInverse_ae (n m : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (f : HighSectorSpace n) :
    (fun K => (((auxiliaryWeight n e p m K)⁻¹ : ℝ) : ℂ) • physicalSector m ((f : GW.Fock.Carrier) m) K)
      =ᵐ[GW.Fock.sectorMeasure m]
      physicalSector m ((auxiliaryPhysicalFreeInverse n e p he f : GW.Fock.Carrier) m) := by
  let u := auxiliaryFreeInverseEnergy n e p he f
  have hu := auxiliaryWeightedCoordinates_physical n m e p he u
  have hc : auxiliaryWeightedCoordinates n e p he (u : AuxiliaryFullEnergy n e p he) = (f : GW.Fock.Carrier) := by
    have h := congrArg (fun z : HighSectorSpace n => (z : GW.Fock.Carrier))
      ((auxiliaryEnergyCoordinates n e p he).apply_symm_apply f)
    rw [auxiliaryEnergyCoordinates_val] at h
    exact h
  have hg : auxiliaryFullEmbedding n e p he (u : AuxiliaryFullEnergy n e p he) =
      (auxiliaryPhysicalFreeInverse n e p he f : GW.Fock.Carrier) := rfl
  rw [hc,hg] at hu
  filter_upwards [hu] with K hK
  let z : ℂ := physicalSector m ((auxiliaryPhysicalFreeInverse n e p he f : GW.Fock.Carrier) m) K
  let v : ℂ := physicalSector m ((f : GW.Fock.Carrier) m) K
  have hEq : (auxiliaryWeight n e p m K : ℂ)*z = v := hK
  change (((auxiliaryWeight n e p m K)⁻¹ : ℝ) : ℂ)*v = z
  have hW : (auxiliaryWeight n e p m K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (zero_lt_one.trans_le (auxiliaryWeight_ge_one n m e p he K)))
  rw [Complex.ofReal_inv,← hEq]
  field_simp [hW]

theorem auxiliaryPhysicalFreeInverse_graph (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (f : HighSectorSpace n) :
    ((f : GW.Fock.Carrier),(auxiliaryPhysicalFreeInverse n e p he f : GW.Fock.Carrier)) ∈
      (fockRealMultiplier (fun m K => (auxiliaryWeight n e p m K)⁻¹)).graph :=
  (fockRealMultiplier_graph_ae_iff _ _ _).mpr (fun m => auxiliaryPhysicalFreeInverse_ae n m e p he f)

theorem auxiliaryPhysicalFreeInverse_norm_le (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    ‖auxiliaryPhysicalFreeInverse n e p he‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  have h := fockWeightedInclusion_norm_le (auxiliaryWeight n e p) (auxiliaryWeight_measurable n e p)
    (fun m K => auxiliaryWeight_ge_one n m e p he K)
    (fun m tau K => auxiliaryWeight_permutation n m e p tau K)
    (auxiliaryFreeInverseEnergy n e p he f : AuxiliaryFullEnergy n e p he)
  change ‖(auxiliaryPhysicalFreeInverse n e p he f : GW.Fock.Carrier)‖ ≤ _ at h
  change ‖(auxiliaryPhysicalFreeInverse n e p he f : GW.Fock.Carrier)‖ ≤ 1*‖f‖
  rw [one_mul]
  exact h.trans_eq ((auxiliaryFreeInverseEnergy n e p he).norm_map f)

theorem auxiliaryPhysicalFreeInverse_selfadjoint (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    (auxiliaryPhysicalFreeInverse n e p he).adjoint = auxiliaryPhysicalFreeInverse n e p he := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f h
  let A := fockRealMultiplier (fun m K => (auxiliaryWeight n e p m K)⁻¹)
  obtain ⟨af,haf⟩ := A.mem_graph_iff'.mp (auxiliaryPhysicalFreeInverse_graph n e p he f)
  obtain ⟨ah,hah⟩ := A.mem_graph_iff'.mp (auxiliaryPhysicalFreeInverse_graph n e p he h)
  have hs := fockRealMultiplier_symmetric (fun m K => (auxiliaryWeight n e p m K)⁻¹) af ah
  have haf1 : (af : GW.Fock.Carrier) = (f : GW.Fock.Carrier) := congrArg Prod.fst haf
  have haf2 : A af = (auxiliaryPhysicalFreeInverse n e p he f : GW.Fock.Carrier) := congrArg Prod.snd haf
  have hah1 : (ah : GW.Fock.Carrier) = (h : GW.Fock.Carrier) := congrArg Prod.fst hah
  have hah2 : A ah = (auxiliaryPhysicalFreeInverse n e p he h : GW.Fock.Carrier) := congrArg Prod.snd hah
  change ⟪A af,(ah : GW.Fock.Carrier)⟫_ℂ = ⟪(af : GW.Fock.Carrier),A ah⟫_ℂ at hs
  rw [haf2,hah1,haf1,hah2] at hs
  exact hs

end Froehlich
