import Froehlich.Nodes.GW07
import Froehlich.Nodes.GW06Action

/-! Construction-specific applications of the retained full-domain spectrum
and form-inverse interfaces to the actual canonical fiber family. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem fiber_realSpectrum_preimage (g : ℝ) (P : GW.Space) :
    realSpectrum (fiberHamiltonian g P) =
      Complex.ofReal ⁻¹' complexSpectrum (fiberHamiltonian g P) :=
  associated_realSpectrum_preimage (fiberFormData g P none)

theorem fiber_nonreal_resolvent (g : ℝ) (P : GW.Space) (z : ℂ) (hz : z.im ≠ 0) :
    z ∈ complexResolventSet (fiberHamiltonian g P) :=
  associated_nonreal_resolvent (fiberFormData g P none) z hz

theorem fiber_energyInverse_isResolvent (g : ℝ) (P : GW.Space) (lam : ℝ)
    (T R : EnergySpace P →L[ℂ] EnergySpace P)
    (hrep : ∀ w u, ⟪w,T u⟫_ℂ = freeFiberForm P w u + singularInteraction g P w u -
      (lam : ℂ)*⟪energyEmbedding P w,energyEmbedding P u⟫_ℂ)
    (hRT : R*T = 1) (hTR : T*R = 1) :
    GW.Operators.IsResolvent (fiberHamiltonian g P) (lam : ℂ)
      (physicalEnergyInverse (fiberFormData g P none) R) :=
  physicalEnergyInverse_isResolvent (fiberFormData g P none) lam T R hrep hRT hTR

theorem fiber_energyKernel_hasEigenvector (g : ℝ) (P : GW.Space) (lam : ℝ)
    (T : EnergySpace P →L[ℂ] EnergySpace P)
    (hrep : ∀ w u, ⟪w,T u⟫_ℂ = freeFiberForm P w u + singularInteraction g P w u -
      (lam : ℂ)*⟪energyEmbedding P w,energyEmbedding P u⟫_ℂ)
    (u : EnergySpace P) (hu : u ≠ 0) (hTu : T u = 0) :
    HasEigenvector (fiberHamiltonian g P) lam :=
  energyKernel_hasEigenvector (fiberFormData g P none) lam T hrep u hu hTu

end Froehlich
