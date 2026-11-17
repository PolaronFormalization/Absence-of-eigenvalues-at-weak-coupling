import Froehlich.Nodes.FB01LiebYamazakiExtension
import Froehlich.Nodes.FB02TailDifference
import Froehlich.Nodes.FD02FreeForm

/-! Actual cutoff data for the retained GW norm-limit and representation
construction. Every coupling is covered by the full two-term LY remainder. -/
noncomputable section
open MeasureTheory
namespace Froehlich

def lyGlobalRemainder (g : ℝ) : ℝ := lyRemainderConstant * (2*g^2+8*g^4)

theorem lyGlobalRemainder_nonneg (g : ℝ) : 0 ≤ lyGlobalRemainder g := by
  unfold lyGlobalRemainder
  exact mul_nonneg lyRemainderConstant_pos.le (by positivity)

theorem freeEnergy_nonneg (P : GW.Space) (u : GW.Fock.Carrier) : 0 ≤ freeEnergy P u := by
  apply tsum_nonneg
  intro n
  exact integral_nonneg (fun K => mul_nonneg (freeSymbol_nonneg P n K) (sq_nonneg _))

def fiberUniformData (g : ℝ) (P : GW.Space) :
    GW.Operators.UniformFormData (EnergySpace P) GW.Fock.Carrier where
  embedding := energyEmbedding P
  embedding_injective := energyEmbedding_injective P
  embedding_dense := energyEmbedding_dense P
  base := freeFiberForm P
  base_hermitian := freeFiberForm_hermitian P
  base_continuous := freeFiberForm_continuous P
  base_nonnegative u := by
    rw [freeFiberForm_physical_energy]
    exact freeEnergy_nonneg P _
  energy_identity u := (freeFiberForm_shifted_norm P u).symm
  perturbation ℓ := GW.Operators.boundedFormAlgebraic (cutoffInteractionForm g ℓ.val ℓ.property P)
  perturbation_hermitian ℓ := cutoffInteractionForm_hermitian g ℓ.val ℓ.property P
  relative := 1/2
  relative_nonnegative := by norm_num
  relative_small := by norm_num
  remainder := lyGlobalRemainder g
  remainder_nonnegative := lyGlobalRemainder_nonneg g
  diagonal_bound ℓ u := by
    have h := liebYamazaki_cutoff g ℓ.val ℓ.property P u (1/2) (by norm_num)
    rw [← freeFiberForm_physical_energy] at h
    have hr : lyRemainderConstant * (g^2/(1/2) + g^4/(1/2)^3) = lyGlobalRemainder g := by
      unfold lyGlobalRemainder
      ring
    rw [hr] at h
    exact h
  error := cutoffTailError g
  error_nonnegative R _ := cutoffTailError_nonneg g R
  error_tendsto := cutoffTailError_tendsto g
  difference_bound R hR ℓ μ hℓ hμ u :=
    cutoffInteraction_difference_diagonal g R ℓ.val μ.val hR ℓ.property μ.property hℓ hμ P u

end Froehlich
