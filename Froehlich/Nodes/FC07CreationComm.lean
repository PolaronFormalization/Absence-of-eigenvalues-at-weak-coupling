import Froehlich.Nodes.FC07Commutators

/-! The creation momentum commutator follows from actual maximal adjoints,
real momentum symmetry, and density of the same canonical core. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

def coreCreationAction (S : ℕ) (hS : 1 ≤ S) (f : GW.OnePhonon)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), (S : ℝ) < ‖k‖ → f k = 0)
    (u : boundedMomentumCore) : boundedMomentumCore :=
  ⟨creationRestriction f (coreNumberLift u),creationRestriction_preserves_core f u S hS hf⟩

theorem coreMomentum_pairing (a : Fin 3) (w u : boundedMomentumCore) :
    ⟪(coreMomentumAction a w : GW.Fock.Carrier),(u : GW.Fock.Carrier)⟫_ℂ =
      ⟪(w : GW.Fock.Carrier),(coreMomentumAction a u : GW.Fock.Carrier)⟫_ℂ :=
  fockRealMultiplier_symmetric (fun n K => totalMomentum n K a)
    (coreMomentumInput a w) (coreMomentumInput a u)

theorem core_creation_pairing (f : GW.OnePhonon) (w u : boundedMomentumCore) :
    ⟪creationRestriction f (coreNumberLift w),(u : GW.Fock.Carrier)⟫_ℂ =
      ⟪(w : GW.Fock.Carrier),annihilationRestriction f (coreNumberLift u)⟫_ℂ := by
  simpa only [coreNumberLift_embedding] using smeared_adjoint_pairing f (coreNumberLift w) (coreNumberLift u)

theorem core_annihilation_pairing (f : GW.OnePhonon) (w u : boundedMomentumCore) :
    ⟪annihilationRestriction f (coreNumberLift w),(u : GW.Fock.Carrier)⟫_ℂ =
      ⟪(w : GW.Fock.Carrier),creationRestriction f (coreNumberLift u)⟫_ℂ := by
  rw [← inner_conj_symm (annihilationRestriction f (coreNumberLift w)) (u : GW.Fock.Carrier),
    ← core_creation_pairing f u w, inner_conj_symm]

theorem creation_momentum_pairing (a : Fin 3) (S : ℕ) (hS : 1 ≤ S) (f : GW.OnePhonon)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), (S : ℝ) < ‖k‖ → f k = 0)
    (u w : boundedMomentumCore) :
    ⟪(w : GW.Fock.Carrier),
      (coreMomentumAction a (coreCreationAction S hS f hf u) : GW.Fock.Carrier)⟫_ℂ =
      ⟪(w : GW.Fock.Carrier),
        creationRestriction f (coreNumberLift (coreMomentumAction a u)) +
          creationRestriction (momentumSmearing a S f) (coreNumberLift u)⟫_ℂ := by
  have he : annihilationRestriction f (coreNumberLift (coreMomentumAction a w)) =
      (coreMomentumAction a (coreAnnihilationAction f w) : GW.Fock.Carrier) +
        annihilationRestriction (momentumSmearing a S f) (coreNumberLift w) := by
    rw [annihilation_momentum_action a S f hf w]
    abel
  calc
    _ = ⟪(coreMomentumAction a w : GW.Fock.Carrier),
        (coreCreationAction S hS f hf u : GW.Fock.Carrier)⟫_ℂ :=
      (coreMomentum_pairing a w (coreCreationAction S hS f hf u)).symm
    _ = ⟪annihilationRestriction f (coreNumberLift (coreMomentumAction a w)),
        (u : GW.Fock.Carrier)⟫_ℂ := (core_annihilation_pairing f (coreMomentumAction a w) u).symm
    _ = ⟪(coreMomentumAction a (coreAnnihilationAction f w) : GW.Fock.Carrier),
        (u : GW.Fock.Carrier)⟫_ℂ +
        ⟪annihilationRestriction (momentumSmearing a S f) (coreNumberLift w),
          (u : GW.Fock.Carrier)⟫_ℂ := by rw [he,inner_add_left]
    _ = ⟪(coreAnnihilationAction f w : GW.Fock.Carrier),
        (coreMomentumAction a u : GW.Fock.Carrier)⟫_ℂ +
        ⟪(w : GW.Fock.Carrier),creationRestriction (momentumSmearing a S f) (coreNumberLift u)⟫_ℂ := by
      rw [coreMomentum_pairing,core_annihilation_pairing]
    _ = ⟪(w : GW.Fock.Carrier),creationRestriction f (coreNumberLift (coreMomentumAction a u))⟫_ℂ +
        ⟪(w : GW.Fock.Carrier),creationRestriction (momentumSmearing a S f) (coreNumberLift u)⟫_ℂ := by
      change ⟪annihilationRestriction f (coreNumberLift w),(coreMomentumAction a u : GW.Fock.Carrier)⟫_ℂ + _ = _
      rw [core_annihilation_pairing]
    _ = _ := (inner_add_right _ _ _).symm

theorem creation_momentum_action (a : Fin 3) (S : ℕ) (hS : 1 ≤ S) (f : GW.OnePhonon)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), (S : ℝ) < ‖k‖ → f k = 0)
    (u : boundedMomentumCore) :
    (coreMomentumAction a (coreCreationAction S hS f hf u) : GW.Fock.Carrier) =
      creationRestriction f (coreNumberLift (coreMomentumAction a u)) +
        creationRestriction (momentumSmearing a S f) (coreNumberLift u) := by
  apply ext_inner_left ℂ
  intro z
  have hc : IsClosed {w : GW.Fock.Carrier |
      ⟪w,(coreMomentumAction a (coreCreationAction S hS f hf u) : GW.Fock.Carrier)⟫_ℂ =
        ⟪w,creationRestriction f (coreNumberLift (coreMomentumAction a u)) +
          creationRestriction (momentumSmearing a S f) (coreNumberLift u)⟫_ℂ} :=
    isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  apply closure_minimal (s := (boundedMomentumCore : Set GW.Fock.Carrier)) _ hc (boundedMomentumCore_dense z)
  intro w hw
  exact creation_momentum_pairing a S hS f hf u ⟨w,hw⟩

theorem creation_momentum_commutator (a : Fin 3) (S : ℕ) (hS : 1 ≤ S) (f : GW.OnePhonon)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), (S : ℝ) < ‖k‖ → f k = 0)
    (u : boundedMomentumCore) :
    (coreMomentumAction a (coreCreationAction S hS f hf u) : GW.Fock.Carrier) -
      creationRestriction f (coreNumberLift (coreMomentumAction a u)) =
        creationRestriction (momentumSmearing a S f) (coreNumberLift u) := by
  rw [creation_momentum_action a S hS f hf u]
  abel

end Froehlich
