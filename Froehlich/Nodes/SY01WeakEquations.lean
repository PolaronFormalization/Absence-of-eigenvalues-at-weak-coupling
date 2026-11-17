import Froehlich.Nodes.SY01Hamiltonian
import Froehlich.Nodes.FA02

/-! Transport of actual shifted weak equations. Coercive uniqueness below
uses the retained inverse construction, never a ground-state hypothesis. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem shiftedWeak_conjugation (g lam : ℝ) (P : GW.Space)
    (F : ConjugateLoad (EnergySpace P)) (x : EnergySpace P)
    (hx : ∀ w, (fiberFormData g P none).form w x -
      (lam : ℂ)*⟪energyEmbedding P w,energyEmbedding P x⟫_ℂ = F w) :
    ∀ w, (fiberFormData g P none).form w (energyConjugation P x) -
      (lam : ℂ)*⟪energyEmbedding P w,energyEmbedding P (energyConjugation P x)⟫_ℂ =
        (starRingEnd ℂ) (F (energyConjugation P w)) := by
  intro w
  have h := shiftedFiberForm_conjugation g lam P (energyConjugation P w) x
  rw [energyConjugation_involutive P w, hx] at h
  exact h

theorem shiftedWeak_reflection (g lam : ℝ) (P : GW.Space)
    (F : ConjugateLoad (EnergySpace P)) (x : EnergySpace P)
    (hx : ∀ w, (fiberFormData g P none).form w x -
      (lam : ℂ)*⟪energyEmbedding P w,energyEmbedding P x⟫_ℂ = F w) :
    ∀ w : EnergySpace (-P), (fiberFormData g (-P) none).form w (energyReflection P x) -
      (lam : ℂ)*⟪energyEmbedding (-P) w,energyEmbedding (-P) (energyReflection P x)⟫_ℂ =
        F ((energyReflection P).symm w) := by
  intro w
  have h := shiftedFiberForm_reflection g lam P ((energyReflection P).symm w) x
  rw [LinearIsometryEquiv.apply_symm_apply, hx] at h
  exact h

theorem coercive_weak_unique {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] (T : V →L[ℂ] V) (hT : T.adjoint = T) (alpha : ℝ) (ha : 0 < alpha)
    (hp : ∀ u, alpha*‖u‖^2 ≤ (⟪u,T u⟫_ℂ).re) (u v : V)
    (he : ∀ w, ⟪w,T u⟫_ℂ = ⟪w,T v⟫_ℂ) : u = v := by
  have hTu : T u = T v := ext_inner_left ℂ he
  calc
    u = GW.Operators.coerciveInverse T hT ha hp (T u) :=
      (GW.Operators.coerciveInverse_left T hT ha hp u).symm
    _ = GW.Operators.coerciveInverse T hT ha hp (T v) := congrArg _ hTu
    _ = v := GW.Operators.coerciveInverse_left T hT ha hp v

theorem shiftedWeak_unique (g lam : ℝ) (P : GW.Space)
    (T : EnergySpace P →L[ℂ] EnergySpace P) (hT : T.adjoint = T)
    (alpha : ℝ) (ha : 0 < alpha) (hp : ∀ u, alpha*‖u‖^2 ≤ (⟪u,T u⟫_ℂ).re)
    (hrep : ∀ w u, ⟪w,T u⟫_ℂ = (fiberFormData g P none).form w u -
      (lam : ℂ)*⟪energyEmbedding P w,energyEmbedding P u⟫_ℂ)
    (u v : EnergySpace P) (F : ConjugateLoad (EnergySpace P))
    (hu : ∀ w, (fiberFormData g P none).form w u -
      (lam : ℂ)*⟪energyEmbedding P w,energyEmbedding P u⟫_ℂ = F w)
    (hv : ∀ w, (fiberFormData g P none).form w v -
      (lam : ℂ)*⟪energyEmbedding P w,energyEmbedding P v⟫_ℂ = F w) : u = v := by
  apply coercive_weak_unique T hT alpha ha hp u v
  intro w
  rw [hrep,hrep,hu,hv]

end Froehlich
