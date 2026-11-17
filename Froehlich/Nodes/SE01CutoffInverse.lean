import Froehlich.Nodes.SE01CutoffSectorEquations
import Froehlich.Nodes.PT03FormCorrectionPhysical

/-! The cutoff high weak inverse applied at the same fixed e. The extra
identity is physical mass j†j; the source coupling stays in the energy dual. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

private def se01CutoffHighOperator (e : ℝ) (P : GW.Space)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (Λ : GW.Operators.PositiveCutoff) :
    HighEnergySpace P 2 →L[ℂ] HighEnergySpace P 2 := by
  simpa only [neg_neg] using! cutoffCompressedEnergyOperator 2 e (-P) (by norm_num) he Λ g

private theorem se01CutoffHighOperator_spec (e : ℝ) (P : GW.Space)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (Λ : GW.Operators.PositiveCutoff)
    (w u : HighEnergySpace P 2) :
    ⟪w,se01CutoffHighOperator e P he g Λ u⟫_ℂ =
      (fiberFormData g P (some Λ)).form (w : EnergySpace P) (u : EnergySpace P) -
      ((e+1 : ℝ) : ℂ)*⟪highEnergyEmbedding P 2 w,highEnergyEmbedding P 2 u⟫_ℂ := by
  have hspec := cutoffCompressedEnergyOperator_spec 2 e (-P) (by norm_num) he Λ g
  change ∀ w u : HighEnergySpace (-(-P)) 2,
    ⟪w,cutoffCompressedEnergyOperator 2 e (-P) (by norm_num) he Λ g u⟫_ℂ =
    (fiberFormData g (-(-P)) (some Λ)).form (w : EnergySpace (-(-P))) (u : EnergySpace (-(-P))) -
    ((e-1+(2 : ℝ) : ℝ) : ℂ)*⟪highEnergyEmbedding (-(-P)) 2 w,highEnergyEmbedding (-(-P)) 2 u⟫_ℂ at hspec
  rw [neg_neg] at hspec
  have h := hspec w u
  rw [show e-1+(2 : ℝ)=e+1 by ring] at h
  simpa only [se01CutoffHighOperator] using h

private theorem se01CutoffHighInverse_left (e : ℝ) (P : GW.Space)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant * |g| ≤ 1/2) (Λ : GW.Operators.PositiveCutoff)
    (u : HighEnergySpace P 2) :
    cutoffTwoSectorReferenceInverse e P he g hg hs Λ (se01CutoffHighOperator e P he g Λ u) = u := by
  have hleft := cutoffCompressedEnergyInverse_left 2 e (-P) (by norm_num) he Λ g hg hs
  have hpoint : ∀ v : HighEnergySpace (-(-P)) 2,
      cutoffAuxiliaryEnergyInverse 2 e (-P) (by norm_num) he g hg hs Λ
        (cutoffCompressedEnergyOperator 2 e (-P) (by norm_num) he Λ g v) = v := by
    intro v
    have h := congrArg (fun A : HighEnergySpace (-(-P)) 2 →L[ℂ] HighEnergySpace (-(-P)) 2 => A v) hleft
    exact (mul_apply_eq_comp
      (cutoffAuxiliaryEnergyInverse 2 e (-P) (by norm_num) he g hg hs Λ)
      (cutoffCompressedEnergyOperator 2 e (-P) (by norm_num) he Λ g) v).symm.trans
      (h.trans (one_apply_eq_self
        (F := HighEnergySpace (-(-P)) 2 →L[ℂ] HighEnergySpace (-(-P)) 2) v))
  rw [neg_neg] at hpoint
  have h := hpoint u
  simpa only [cutoffTwoSectorReferenceInverse,se01CutoffHighOperator] using h

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

def cutoffGroundSourceCouplingResponseEnergy (Λ : GW.Operators.PositiveCutoff) : HighEnergySpace 0 2 :=
  cutoffTwoSectorReferenceInverse e 0 he g hg hs Λ
    (cutoffTwoSectorCoupling g 0 Λ (cutoffGroundSourceOneEnergy e he g hg hs Λ))

theorem cutoffGroundSource_high_shifted_equation (Λ : GW.Operators.PositiveCutoff) :
    se01CutoffHighOperator e 0 he g Λ (cutoffGroundSourceHighEnergy e he g hg hs Λ) +
      (highEnergyEmbedding 0 2).adjoint
        (highEnergyEmbedding 0 2 (cutoffGroundSourceHighEnergy e he g hg hs Λ)) =
      -(cutoffTwoSectorCoupling g 0 Λ (cutoffGroundSourceOneEnergy e he g hg hs Λ)) := by
  apply ext_inner_left ℂ
  intro w
  rw [inner_add_right,inner_neg_right,se01CutoffHighOperator_spec,
    (highEnergyEmbedding 0 2).adjoint_inner_right]
  have h := cutoffGroundSource_high_equation_test e he g hg hs Λ w
  change (fiberFormData g 0 (some Λ)).form (w : EnergySpace 0)
      (cutoffGroundSourceHighEnergy e he g hg hs Λ : EnergySpace 0) -
    (e : ℂ)*⟪highEnergyEmbedding 0 2 w,
      highEnergyEmbedding 0 2 (cutoffGroundSourceHighEnergy e he g hg hs Λ)⟫_ℂ = _ at h
  push_cast
  linear_combination h

theorem cutoffGroundSource_high_inverse_energy (Λ : GW.Operators.PositiveCutoff) :
    cutoffTwoSectorReferenceInverse e 0 he g hg hs Λ
      ((highEnergyEmbedding 0 2).adjoint (highEnergyEmbedding 0 2 (cutoffGroundSourceHighEnergy e he g hg hs Λ))) =
      -(cutoffGroundSourceHighEnergy e he g hg hs Λ) - cutoffGroundSourceCouplingResponseEnergy e he g hg hs Λ := by
  have h := congrArg (cutoffTwoSectorReferenceInverse e 0 he g hg hs Λ)
    (cutoffGroundSource_high_shifted_equation e he g hg hs Λ)
  rw [map_add,map_neg,se01CutoffHighInverse_left] at h
  apply eq_sub_iff_add_eq.mpr
  apply eq_neg_iff_add_eq_zero.mpr
  exact ((add_comm _ _).trans (add_assoc _ _ _).symm).trans (eq_neg_iff_add_eq_zero.mp h)

theorem cutoffGroundSource_high_inverse_physical (Λ : GW.Operators.PositiveCutoff) :
    cutoffAuxiliaryX e he Λ g hg hs 0
      (energyEmbedding 0 (cutoffGroundSourceHighEnergy e he g hg hs Λ : EnergySpace 0)) =
      -(energyEmbedding 0 (cutoffGroundSourceHighEnergy e he g hg hs Λ : EnergySpace 0)) -
        energyEmbedding 0 (cutoffGroundSourceCouplingResponseEnergy e he g hg hs Λ : EnergySpace 0) := by
  have h := congrArg (highEnergyEmbedding 0 2) (cutoffGroundSource_high_inverse_energy e he g hg hs Λ)
  rw [map_sub,map_neg] at h
  have hp := congrArg (fun R : HighSectorSpace 2 →L[ℂ] HighSectorSpace 2 =>
    R (highEnergyEmbedding 0 2 (cutoffGroundSourceHighEnergy e he g hg hs Λ)))
    (cutoffTwoSectorReferenceInverse_physical e 0 he g hg hs Λ)
  change highEnergyEmbedding 0 2 (cutoffTwoSectorReferenceInverse e 0 he g hg hs Λ
    ((highEnergyEmbedding 0 2).adjoint (highEnergyEmbedding 0 2 (cutoffGroundSourceHighEnergy e he g hg hs Λ)))) =
      cutoffAuxiliaryResolvent 2 e (-(0 : GW.Space)) he Λ g hg hs
        (highEnergyEmbedding 0 2 (cutoffGroundSourceHighEnergy e he g hg hs Λ)) at hp
  rw [hp] at h
  have hv := congrArg (fun u : HighSectorSpace 2 => (u : GW.Fock.Carrier)) h
  exact (cutoffAuxiliaryExtendedResolvent_on_high 2 e (-(0 : GW.Space)) he Λ g hg hs
    (highEnergyEmbedding 0 2 (cutoffGroundSourceHighEnergy e he g hg hs Λ))).trans hv

end Froehlich
