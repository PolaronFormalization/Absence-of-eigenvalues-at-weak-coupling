import Froehlich.Nodes.SE01SectorEquations
import Froehlich.Nodes.PT03FormCorrectionSingular

/-! Applying the true high form inverse to the source sector equation.
The coupling is an energy-dual/Riesz load; its response is never an
uncut physical creation vector. -/
noncomputable section
namespace Froehlich

private theorem se01ReferenceInverse_physical (e : ℝ) (P : GW.Space)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant * |g| ≤ 1/2) :
    (highEnergyEmbedding P 2).comp
      ((singularTwoSectorReferenceInverse e P he g hg hs).comp (highEnergyEmbedding P 2).adjoint) =
      auxiliaryResolvent 2 e (-P) he g hg hs := by
  have h := auxiliaryCompressedEnergyInverse_physical 2 e (-P) (by norm_num) he g hg hs
  change (highEnergyEmbedding (-(-P)) 2).comp
    ((auxiliaryCompressedEnergyInverse 2 e (-P) (by norm_num) he g hg hs).comp
      (highEnergyEmbedding (-(-P)) 2).adjoint) = auxiliaryResolvent 2 e (-P) he g hg hs at h
  rw [neg_neg] at h
  simpa only [singularTwoSectorReferenceInverse] using h

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

def groundSourceCouplingResponseEnergy : HighEnergySpace 0 2 :=
  singularTwoSectorReferenceInverse e 0 he g hg hs
    (twoSectorCoupling g 0 (groundSourceOneEnergy e he g hg hs))

variable (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant * |g|^2 ≤ e)
  (hquadratic : sectorQuadraticConstant * |g|^2 ≤ 1/8)

include hquarter heLower hquadratic in
theorem groundSource_high_inverse_energy :
    singularTwoSectorReferenceInverse e 0 he g hg hs
      ((highEnergyEmbedding 0 2).adjoint (highEnergyEmbedding 0 2 (groundSourceHighEnergy e he g hg hs))) =
      -(groundSourceHighEnergy e he g hg hs) - groundSourceCouplingResponseEnergy e he g hg hs := by
  have hleft : singularTwoSectorReferenceInverse e 0 he g hg hs
      (twoSectorOperator g 0 (e+1) (groundSourceHighEnergy e he g hg hs)) = groundSourceHighEnergy e he g hg hs := by
    rw [singularTwoSectorReferenceInverse_eq_threshold e 0 he g hg hs hquarter heLower hquadratic]
    simpa only [sub_zero] using twoSectorEnergyInverse_left_apply g e 0 0 hquarter heLower he.2
      (by norm_num) hquadratic (groundSourceHighEnergy e he g hg hs)
  have h := congrArg (singularTwoSectorReferenceInverse e 0 he g hg hs)
    (groundSource_high_shifted_equation e he g hg hs)
  rw [map_add,map_neg,hleft] at h
  apply eq_sub_iff_add_eq.mpr
  apply eq_neg_iff_add_eq_zero.mpr
  exact ((add_comm _ _).trans (add_assoc _ _ _).symm).trans (eq_neg_iff_add_eq_zero.mp h)

include hquarter heLower hquadratic in
theorem groundSource_high_inverse_physical :
    auxiliaryX e he g hg hs 0 (energyEmbedding 0 (groundSourceHighEnergy e he g hg hs : EnergySpace 0)) =
      -(energyEmbedding 0 (groundSourceHighEnergy e he g hg hs : EnergySpace 0)) -
        energyEmbedding 0 (groundSourceCouplingResponseEnergy e he g hg hs : EnergySpace 0) := by
  have h := congrArg (highEnergyEmbedding 0 2)
    (groundSource_high_inverse_energy e he g hg hs hquarter heLower hquadratic)
  rw [map_sub,map_neg] at h
  have hp := congrArg (fun R : HighSectorSpace 2 →L[ℂ] HighSectorSpace 2 =>
    R (highEnergyEmbedding 0 2 (groundSourceHighEnergy e he g hg hs)))
    (se01ReferenceInverse_physical e 0 he g hg hs)
  change highEnergyEmbedding 0 2 (singularTwoSectorReferenceInverse e 0 he g hg hs
    ((highEnergyEmbedding 0 2).adjoint (highEnergyEmbedding 0 2 (groundSourceHighEnergy e he g hg hs)))) =
      auxiliaryResolvent 2 e (-(0 : GW.Space)) he g hg hs
        (highEnergyEmbedding 0 2 (groundSourceHighEnergy e he g hg hs)) at hp
  rw [hp] at h
  have hv := congrArg (fun u : HighSectorSpace 2 => (u : GW.Fock.Carrier)) h
  exact (auxiliaryExtendedResolvent_on_high 2 e (-(0 : GW.Space)) he g hg hs
    (highEnergyEmbedding 0 2 (groundSourceHighEnergy e he g hg hs))).trans hv

end Froehlich
