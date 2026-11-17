import Froehlich.Nodes.UV01Fields

set_option autoImplicit false

/-! Self-adjointness of the actual cutoff inverses, needed in the
ordinary scalar pairing argument. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem pt03_cutoffNormalizedInverse_selfadjoint (n : ℕ) (e : ℝ) (p : GW.Space)
    (he : e ≤ 0) (Λ : GW.Operators.PositiveCutoff) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) :
    (cutoffAuxiliaryNormalizedInverse g Λ.val Λ.property n e p he hg hs).adjoint =
      cutoffAuxiliaryNormalizedInverse g Λ.val Λ.property n e p he hg hs := by
  apply inverse_selfadjoint (cutoffAuxiliaryNormalizedOperator g Λ.val Λ.property n e p he)
  · simp only [cutoffAuxiliaryNormalizedOperator,map_add,
      ContinuousLinearMap.adjoint_one,cutoffAuxiliaryInteractionOperator_selfadjoint]
  · exact cutoffAuxiliaryNormalizedInverse_left g Λ.val Λ.property n e p he hg hs
  · exact cutoffAuxiliaryNormalizedInverse_right g Λ.val Λ.property n e p he hg hs

theorem pt03_cutoffResolvent_selfadjoint (n : ℕ) (e : ℝ) (p : GW.Space)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (Λ : GW.Operators.PositiveCutoff)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) :
    (cutoffAuxiliaryResolvent n e p he Λ g hg hs).adjoint =
      cutoffAuxiliaryResolvent n e p he Λ g hg hs := by
  simp only [cutoffAuxiliaryResolvent,ContinuousLinearMap.adjoint_comp,
    auxiliaryPhysicalFreeInverse_selfadjoint,pt03_cutoffNormalizedInverse_selfadjoint,
    ContinuousLinearMap.comp_assoc]

theorem pt03_cutoffExtendedResolvent_pairing (n : ℕ) (e : ℝ) (p : GW.Space)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (Λ : GW.Operators.PositiveCutoff)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (u v : GW.Fock.Carrier) :
    ⟪u,cutoffAuxiliaryExtendedResolvent n e p he Λ g hg hs v⟫_ℂ =
      ⟪cutoffAuxiliaryExtendedResolvent n e p he Λ g hg hs u,v⟫_ℂ := by
  let R := cutoffAuxiliaryResolvent n e p he Λ g hg hs
  have hleft (a : GW.Fock.Carrier) (b : HighSectorSpace n) :
      ⟪a,(b : GW.Fock.Carrier)⟫_ℂ = ⟪highSectorProject n a,b⟫_ℂ := by
    change ⟪a,(b : GW.Fock.Carrier)⟫_ℂ = ⟪highSectorProjection n a,(b : GW.Fock.Carrier)⟫_ℂ
    rw [highSectorProjection_pairing,(highSector_mem_iff n b).mp b.property]
  have hright (a : HighSectorSpace n) (b : GW.Fock.Carrier) :
      ⟪(a : GW.Fock.Carrier),b⟫_ℂ = ⟪a,highSectorProject n b⟫_ℂ := by
    change ⟪(a : GW.Fock.Carrier),b⟫_ℂ = ⟪(a : GW.Fock.Carrier),highSectorProjection n b⟫_ℂ
    rw [←highSectorProjection_pairing,(highSector_mem_iff n a).mp a.property]
  change ⟪u,(R (highSectorProject n v) : GW.Fock.Carrier)⟫_ℂ =
    ⟪(R (highSectorProject n u) : GW.Fock.Carrier),v⟫_ℂ
  rw [hleft,hright]
  have h := R.adjoint_inner_right (highSectorProject n u) (highSectorProject n v)
  rw [show R.adjoint = R from pt03_cutoffResolvent_selfadjoint n e p he Λ g hg hs] at h
  exact h

end Froehlich
