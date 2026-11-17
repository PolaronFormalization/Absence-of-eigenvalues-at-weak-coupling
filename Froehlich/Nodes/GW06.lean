import Froehlich.Nodes.FB02A

/-! The precise source coercive record, with upper constant 2+2b_g.
Only the retained GW representation constructs its associated operators. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem fiberTotalForm_upper (g : ℝ) (P : GW.Space)
    (i : Option GW.Operators.PositiveCutoff) (u : EnergySpace P) :
    (GW.Operators.uniformTotalForm (fiberUniformData g P) i u u).re +
        (lyGlobalRemainder g+1)*‖energyEmbedding P u‖^2 ≤
      (2+2*lyGlobalRemainder g)*‖u‖^2 := by
  have hd := GW.Operators.uniformIndexPerturbation_bound (fiberUniformData g P) i u
  have hp := (le_abs_self (GW.Operators.uniformIndexPerturbation
    (fiberUniformData g P) i u u).re).trans
      ((Complex.abs_re_le_norm _).trans hd)
  change (GW.Operators.uniformIndexPerturbation (fiberUniformData g P) i u u).re ≤
    (1/2 : ℝ)*(freeFiberForm P u u).re + lyGlobalRemainder g*‖energyEmbedding P u‖^2 at hp
  have hn : 0 ≤ (freeFiberForm P u u).re := by
    rw [freeFiberForm_physical_energy]
    exact freeEnergy_nonneg P _
  have hb := lyGlobalRemainder_nonneg g
  have hm := mul_nonneg hb hn
  rw [← freeFiberForm_shifted_norm P u]
  change (freeFiberForm P u u).re +
      (GW.Operators.uniformIndexPerturbation (fiberUniformData g P) i u u).re +
        (lyGlobalRemainder g+1)*‖energyEmbedding P u‖^2 ≤ _
  nlinarith [sq_nonneg ‖energyEmbedding P u‖]

def fiberFormData (g : ℝ) (P : GW.Space) (i : Option GW.Operators.PositiveCutoff) :
    GW.Operators.CoerciveFormData (EnergySpace P) GW.Fock.Carrier where
  embedding := energyEmbedding P
  embedding_injective := energyEmbedding_injective P
  embedding_dense := energyEmbedding_dense P
  form := GW.Operators.uniformTotalForm (fiberUniformData g P) i
  hermitian := GW.Operators.uniformTotalForm_hermitian (fiberUniformData g P) i
  continuous_form := (freeFiberForm_continuous P).add
    (GW.Operators.uniformIndexPerturbation_continuous (fiberUniformData g P) i)
  shift := lyGlobalRemainder g+1
  lower := 1/2
  upper := 2+2*lyGlobalRemainder g
  lower_pos := by norm_num
  lower_le_upper := by linarith [lyGlobalRemainder_nonneg g]
  lower_bound u := by
    have h := (GW.Operators.uniform_shift_bounds (fiberUniformData g P) i u).1
    change (1-(1/2 : ℝ))*‖u‖^2 ≤
      (GW.Operators.uniformTotalForm (fiberUniformData g P) i u u).re +
        (lyGlobalRemainder g+1)*‖energyEmbedding P u‖^2 at h
    rw [show (1 : ℝ)-1/2 = 1/2 by norm_num] at h
    exact h
  upper_bound := fiberTotalForm_upper g P i

theorem fiberFormData_singular_apply (g : ℝ) (P : GW.Space) (w u : EnergySpace P) :
    (fiberFormData g P none).form w u = freeFiberForm P w u + singularInteraction g P w u := rfl

theorem fiberFormData_cutoff_apply (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (w u : EnergySpace P) :
    (fiberFormData g P (some Λ)).form w u =
      freeFiberForm P w u + cutoffInteractionForm g Λ.val Λ.property P w u := by
  change GW.Operators.uniformTotalForm (fiberUniformData g P) (some Λ) w u = _
  rw [GW.Operators.uniformTotalForm, GW.Operators.uniformIndexPerturbation_some]
  rfl

/-- The specific associated operator on the canonical physical GW carrier. -/
def fiberHamiltonian (g : ℝ) (P : GW.Space) : GW.Fock.Carrier →ₗ.[ℂ] GW.Fock.Carrier :=
  GW.Operators.formOperator (fiberFormData g P none)

def cutoffHamiltonian (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) :
    GW.Fock.Carrier →ₗ.[ℂ] GW.Fock.Carrier :=
  GW.Operators.formOperator (fiberFormData g P (some Λ))

theorem fiberHamiltonian_selfadjoint (g : ℝ) (P : GW.Space) :
    GW.IsSelfAdjointOperator (fiberHamiltonian g P) :=
  GW.Operators.formOperator_selfadjoint (fiberFormData g P none)

theorem fiberHamiltonian_domain (g : ℝ) (P : GW.Space) (u : GW.Fock.Carrier) :
    u ∈ (fiberHamiltonian g P).domain ↔
      ∃ x : EnergySpace P, energyEmbedding P x = u ∧ ∃ f : GW.Fock.Carrier,
        ∀ w : EnergySpace P, freeFiberForm P w x + singularInteraction g P w x =
          ⟪energyEmbedding P w,f⟫_ℂ :=
  GW.Operators.formOperator_domain_iff (fiberFormData g P none) u

end Froehlich
