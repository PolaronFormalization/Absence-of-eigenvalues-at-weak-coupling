import Froehlich.Nodes.FC07CreationComm
import Froehlich.Nodes.FB01Kinetic

/-! The real diagonal commutator form, before any high-cutoff estimate. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

def coreSkewField (f : GW.OnePhonon) (u : boundedMomentumCore) : GW.Fock.Carrier :=
  creationRestriction f (coreNumberLift u) - annihilationRestriction f (coreNumberLift u)

theorem coreSkewField_diagonal_real (f : GW.OnePhonon) (u : boundedMomentumCore) :
    (⟪(u : GW.Fock.Carrier),coreSkewField f u⟫_ℂ).re = 0 := by
  have h := congrArg Complex.re (core_creation_pairing f u u)
  have hs := inner_re_symm (𝕜 := ℂ) (creationRestriction f (coreNumberLift u)) (u : GW.Fock.Carrier)
  simp only [RCLike.re_eq_complex_re] at hs
  change (⟪(u : GW.Fock.Carrier),creationRestriction f (coreNumberLift u) -
    annihilationRestriction f (coreNumberLift u)⟫_ℂ).re = 0
  rw [inner_sub_right,Complex.sub_re]
  linarith

theorem coreField_diagonal_real (f : GW.OnePhonon) (u : boundedMomentumCore) :
    (⟪(u : GW.Fock.Carrier),fieldRestriction f (coreNumberLift u)⟫_ℂ).re =
      2 * (⟪(u : GW.Fock.Carrier),creationRestriction f (coreNumberLift u)⟫_ℂ).re := by
  have h := coreSkewField_diagonal_real f u
  change (⟪(u : GW.Fock.Carrier),creationRestriction f (coreNumberLift u) -
    annihilationRestriction f (coreNumberLift u)⟫_ℂ).re = 0 at h
  rw [inner_sub_right,Complex.sub_re] at h
  change (⟪(u : GW.Fock.Carrier),annihilationRestriction f (coreNumberLift u) +
    creationRestriction f (coreNumberLift u)⟫_ℂ).re = _
  rw [inner_add_right,Complex.add_re]
  linarith

theorem momentum_creation_diagonal_real (a : Fin 3) (S : ℕ) (hS : 1 ≤ S)
    (f : GW.OnePhonon)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), (S : ℝ) < ‖k‖ → f k = 0)
    (u : boundedMomentumCore) :
    (⟪(u : GW.Fock.Carrier),creationRestriction (momentumSmearing a S f) (coreNumberLift u)⟫_ℂ).re =
      (⟪(coreMomentumAction a u : GW.Fock.Carrier),coreSkewField f u⟫_ℂ).re := by
  have hc := congrArg (fun z : GW.Fock.Carrier => (⟪(u : GW.Fock.Carrier),z⟫_ℂ).re)
    (creation_momentum_action a S hS f hf u)
  have hp := congrArg Complex.re (coreMomentum_pairing a u (coreCreationAction S hS f hf u))
  have ha := congrArg Complex.re (core_annihilation_pairing f u (coreMomentumAction a u))
  have hs := inner_re_symm (𝕜 := ℂ) (annihilationRestriction f (coreNumberLift u))
    (coreMomentumAction a u : GW.Fock.Carrier)
  simp only [RCLike.re_eq_complex_re] at hs
  change (⟪(u : GW.Fock.Carrier),(coreMomentumAction a (coreCreationAction S hS f hf u) : GW.Fock.Carrier)⟫_ℂ).re =
    (⟪(u : GW.Fock.Carrier),creationRestriction f (coreNumberLift (coreMomentumAction a u)) +
      creationRestriction (momentumSmearing a S f) (coreNumberLift u)⟫_ℂ).re at hc
  rw [inner_add_right,Complex.add_re] at hc
  change (⟪(coreMomentumAction a u : GW.Fock.Carrier),creationRestriction f (coreNumberLift u)⟫_ℂ).re =
    (⟪(u : GW.Fock.Carrier),(coreMomentumAction a (coreCreationAction S hS f hf u) : GW.Fock.Carrier)⟫_ℂ).re at hp
  change _ = (⟪(coreMomentumAction a u : GW.Fock.Carrier),
    creationRestriction f (coreNumberLift u) - annihilationRestriction f (coreNumberLift u)⟫_ℂ).re
  rw [inner_sub_right,Complex.sub_re]
  linarith

theorem coreSkewField_kinetic_shift_real (P : GW.Space) (a : Fin 3)
    (f : GW.OnePhonon) (u : boundedMomentumCore) :
    (⟪coreKineticComponent P a u,coreSkewField f u⟫_ℂ).re =
      (⟪(coreMomentumAction a u : GW.Fock.Carrier),coreSkewField f u⟫_ℂ).re := by
  change (⟪(coreMomentumAction a u : GW.Fock.Carrier) - (P a : ℂ) • (u : GW.Fock.Carrier),
    coreSkewField f u⟫_ℂ).re = _
  rw [inner_sub_left,inner_smul_left]
  simp only [Complex.sub_re,Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,coreSkewField_diagonal_real,mul_zero]

theorem momentum_field_commutator_form (P : GW.Space) (a : Fin 3) (S : ℕ) (hS : 1 ≤ S)
    (f : GW.OnePhonon)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), (S : ℝ) < ‖k‖ → f k = 0)
    (u : boundedMomentumCore) :
    (⟪(u : GW.Fock.Carrier),fieldRestriction (momentumSmearing a S f) (coreNumberLift u)⟫_ℂ).re =
      2 * (⟪coreKineticComponent P a u,coreSkewField f u⟫_ℂ).re := by
  rw [coreField_diagonal_real,momentum_creation_diagonal_real a S hS f hf u,
    coreSkewField_kinetic_shift_real]

end Froehlich
