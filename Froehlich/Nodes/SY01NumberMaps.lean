import Froehlich.Nodes.SY01Conjugation

/-! The actual number graph coordinates inherit the same conjugation and
reflection. Their reciprocal embeddings use real sector constants. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def numberConjugationLinear : NumberFormSpace →ₗ⋆[ℂ] NumberFormSpace where
  toFun := fockConjugation
  map_add' := fockConjugation_add
  map_smul' := fockConjugation_smul

def numberConjugation : NumberFormSpace →ₗᵢ⋆[ℂ] NumberFormSpace where
  toLinearMap := numberConjugationLinear
  norm_map' := fockConjugation_norm

def numberReflection : NumberFormSpace ≃ₗᵢ[ℂ] NumberFormSpace := fockReflectionEquiv

theorem numberConjugation_intertwines (u : NumberFormSpace) :
    numberFormEmbedding (numberConjugation u) = fockConjugation (numberFormEmbedding u) := by
  apply lp.ext
  funext n
  rw [numberFormEmbedding_sqrt_apply]
  change (((Real.sqrt ((n : ℝ)+1))⁻¹ : ℝ) : ℂ) • sectorConjugation n ((show GW.Fock.Carrier from u) n) =
    sectorConjugation n (numberFormEmbedding u n)
  rw [numberFormEmbedding_sqrt_apply, sectorConjugation_smul, Complex.conj_ofReal]

theorem numberReflection_intertwines (u : NumberFormSpace) :
    numberFormEmbedding (numberReflection u) = fockReflection (numberFormEmbedding u) := by
  apply lp.ext
  funext n
  rw [numberFormEmbedding_sqrt_apply]
  change (((Real.sqrt ((n : ℝ)+1))⁻¹ : ℝ) : ℂ) • sectorReflection n ((show GW.Fock.Carrier from u) n) =
    sectorReflection n (numberFormEmbedding u n)
  rw [numberFormEmbedding_sqrt_apply, map_smul]

theorem numberConjugation_involutive : Function.Involutive numberConjugation :=
  fockConjugation_involutive

theorem numberReflection_involutive : Function.Involutive numberReflection :=
  fockReflection_involutive

theorem energyNumberCoordinates_conjugation (P : GW.Space) (u : EnergySpace P) :
    energyNumberCoordinates P (energyConjugation P u) = numberConjugation (energyNumberCoordinates P u) := by
  apply numberFormEmbedding_injective
  rw [energyNumberCoordinates_intertwines, numberConjugation_intertwines,
    energyNumberCoordinates_intertwines, energyConjugation_intertwines]

theorem energyNumberCoordinates_reflection (P : GW.Space) (u : EnergySpace P) :
    energyNumberCoordinates (-P) (energyReflection P u) = numberReflection (energyNumberCoordinates P u) := by
  apply numberFormEmbedding_injective
  rw [energyNumberCoordinates_intertwines, numberReflection_intertwines,
    energyNumberCoordinates_intertwines, energyReflection_intertwines]

end Froehlich
