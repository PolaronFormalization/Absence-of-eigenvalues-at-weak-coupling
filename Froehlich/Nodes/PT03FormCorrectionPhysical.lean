import Froehlich.Nodes.PT03FormCutoffCoupling
import Froehlich.Nodes.UV01CorrectionConvergence
import Froehlich.Nodes.UV01Fields

/-! The literal cutoff Schur correction is the physical creation/inverse
pairing. All maps are the retained original-energy and Fock maps. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

private theorem adjoint_triple_pairing {E H V : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (j : E →L[ℂ] H) (Q : E →L[ℂ] E) (B : V →L[ℂ] E)
    (f h : V) (x y : H) (hf : B f = j.adjoint x) (hh : B h = j.adjoint y) :
    ⟪f,(B.adjoint.comp (Q.comp B)) h⟫_ℂ =
      ⟪x,(j.comp (Q.comp j.adjoint)) y⟫_ℂ := by
  change ⟪f,B.adjoint (Q (B h))⟫_ℂ = ⟪x,j (Q (j.adjoint y))⟫_ℂ
  rw [B.adjoint_inner_right,hf,hh,j.adjoint_inner_left]

variable (e : ℝ) (P : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem cutoffTwoSectorReferenceInverse_physical (Λ : GW.Operators.PositiveCutoff) :
    (highEnergyEmbedding P 2).comp
      ((cutoffTwoSectorReferenceInverse e P he g hg hs Λ).comp (highEnergyEmbedding P 2).adjoint) =
      cutoffAuxiliaryResolvent 2 e (-P) he Λ g hg hs := by
  have h := cutoffCompressedEnergyInverse_physical 2 e (-P) (by norm_num) he Λ g hg hs
  change (highEnergyEmbedding (-(-P)) 2).comp
    ((cutoffAuxiliaryEnergyInverse 2 e (-P) (by norm_num) he g hg hs Λ).comp
      (highEnergyEmbedding (-(-P)) 2).adjoint) =
    cutoffAuxiliaryResolvent 2 e (-P) he Λ g hg hs at h
  rw [neg_neg] at h
  simpa only [cutoffTwoSectorReferenceInverse] using h

theorem cutoffEnergySchurCorrection_creation_pairing (Λ : GW.Operators.PositiveCutoff)
    (f h : OneParticleEnergySpace P) :
    ⟪f,cutoffEnergySchurCorrection e P he g hg hs Λ h⟫_ℂ =
      ⟪(oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) (oneParticleEnergyEmbedding P f) : GW.Fock.Carrier),
        cutoffAuxiliaryX e he Λ g hg hs P
          (oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) (oneParticleEnergyEmbedding P h) : GW.Fock.Carrier)⟫_ℂ := by
  have hp := adjoint_triple_pairing (highEnergyEmbedding P 2)
    (cutoffTwoSectorReferenceInverse e P he g hg hs Λ) (cutoffTwoSectorCoupling g P Λ) f h
    (oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) (oneParticleEnergyEmbedding P f))
    (oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) (oneParticleEnergyEmbedding P h))
    (cutoffTwoSectorCoupling_physicalLoad g P Λ f) (cutoffTwoSectorCoupling_physicalLoad g P Λ h)
  rw [cutoffTwoSectorReferenceInverse_physical] at hp
  change ⟪f,cutoffEnergySchurCorrection e P he g hg hs Λ h⟫_ℂ = _ at hp
  calc
    _ = _ := hp
    _ = _ := congrArg (fun u : GW.Fock.Carrier =>
      ⟪(oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) (oneParticleEnergyEmbedding P f) : GW.Fock.Carrier),u⟫_ℂ)
      (cutoffAuxiliaryExtendedResolvent_on_high 2 e (-P) he Λ g hg hs
        (oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) (oneParticleEnergyEmbedding P h))).symm

end Froehlich
