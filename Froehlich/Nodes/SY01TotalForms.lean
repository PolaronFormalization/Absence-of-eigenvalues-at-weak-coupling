import Froehlich.Nodes.SY01Forms
import Froehlich.Nodes.GW06Action

/-! Symmetry of the actual full forms, including arbitrary real spectral shifts. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem energyConjugation_inner (P : GW.Space) (w u : EnergySpace P) :
    ⟪energyConjugation P w,energyConjugation P u⟫_ℂ = (starRingEnd ℂ) ⟪w,u⟫_ℂ := by
  calc
    _ = ⟪energyCoordinates P (energyConjugation P w),
        energyCoordinates P (energyConjugation P u)⟫_ℂ := ((energyCoordinates P).inner_map_map _ _).symm
    _ = (starRingEnd ℂ) ⟪energyCoordinates P w,energyCoordinates P u⟫_ℂ := by
      rw [energyConjugation_coordinates,energyConjugation_coordinates,fockConjugation_inner]
    _ = _ := by rw [LinearIsometryEquiv.inner_map_map]

theorem freeFiberForm_conjugation (P : GW.Space) (w u : EnergySpace P) :
    freeFiberForm P (energyConjugation P w) (energyConjugation P u) =
      (starRingEnd ℂ) (freeFiberForm P w u) := by
  rw [freeFiberForm_apply,freeFiberForm_apply,energyConjugation_inner,
    energyConjugation_intertwines,energyConjugation_intertwines,fockConjugation_inner,map_sub]

theorem freeFiberForm_reflection (P : GW.Space) (w u : EnergySpace P) :
    freeFiberForm (-P) (energyReflection P w) (energyReflection P u) = freeFiberForm P w u := by
  rw [freeFiberForm_apply,freeFiberForm_apply,LinearIsometryEquiv.inner_map_map,
    energyReflection_intertwines,energyReflection_intertwines]
  exact congrArg (fun z : ℂ => ⟪w,u⟫_ℂ-z) (fockReflectionEquiv.inner_map_map _ _)

theorem fiberTotalForm_conjugation (g : ℝ) (P : GW.Space) (w u : EnergySpace P) :
    (fiberFormData g P none).form (energyConjugation P w) (energyConjugation P u) =
      (starRingEnd ℂ) ((fiberFormData g P none).form w u) := by
  rw [fiberFormData_singular_apply,fiberFormData_singular_apply,freeFiberForm_conjugation,
    singularInteraction_conjugation,map_add]

theorem fiberTotalForm_reflection (g : ℝ) (P : GW.Space) (w u : EnergySpace P) :
    (fiberFormData g (-P) none).form (energyReflection P w) (energyReflection P u) =
      (fiberFormData g P none).form w u := by
  rw [fiberFormData_singular_apply,fiberFormData_singular_apply,freeFiberForm_reflection,
    singularInteraction_reflection]

theorem shiftedFiberForm_conjugation (g lam : ℝ) (P : GW.Space) (w u : EnergySpace P) :
    (fiberFormData g P none).form (energyConjugation P w) (energyConjugation P u) -
        (lam : ℂ)*⟪energyEmbedding P (energyConjugation P w),energyEmbedding P (energyConjugation P u)⟫_ℂ =
      (starRingEnd ℂ) ((fiberFormData g P none).form w u -
        (lam : ℂ)*⟪energyEmbedding P w,energyEmbedding P u⟫_ℂ) := by
  rw [fiberTotalForm_conjugation,energyConjugation_intertwines,energyConjugation_intertwines,
    fockConjugation_inner,map_sub,map_mul,Complex.conj_ofReal]

theorem shiftedFiberForm_reflection (g lam : ℝ) (P : GW.Space) (w u : EnergySpace P) :
    (fiberFormData g (-P) none).form (energyReflection P w) (energyReflection P u) -
        (lam : ℂ)*⟪energyEmbedding (-P) (energyReflection P w),energyEmbedding (-P) (energyReflection P u)⟫_ℂ =
      (fiberFormData g P none).form w u - (lam : ℂ)*⟪energyEmbedding P w,energyEmbedding P u⟫_ℂ := by
  rw [fiberTotalForm_reflection,energyReflection_intertwines,energyReflection_intertwines]
  exact congrArg (fun z : ℂ => (fiberFormData g P none).form w u - (lam : ℂ)*z)
    (fockReflectionEquiv.inner_map_map _ _)

end Froehlich
