import Froehlich.Nodes.FD02Reflection
import Froehlich.Nodes.FD02WeightedConjugation

/-! Physical reflection between the actual reflected weighted domains. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

theorem sectorReflection_opNorm (n : ℕ) : ‖sectorReflection n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [sectorReflection_norm, one_mul]

def fockReflection : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  GW.Spaces.diagonalMap sectorReflection zero_le_one sectorReflection_opNorm

theorem fockReflection_involutive : Function.Involutive fockReflection := by
  intro u
  apply lp.ext
  funext n
  exact sectorReflection_involutive n (u n)

theorem fockReflection_norm (u : GW.Fock.Carrier) : ‖fockReflection u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [GW.Fock.carrier_norm_sq, GW.Fock.carrier_norm_sq]
  exact tsum_congr (fun n => congrArg (fun r : ℝ => r^2) (sectorReflection_norm n (u n)))

def fockReflectionEquiv : GW.Fock.Carrier ≃ₗᵢ[ℂ] GW.Fock.Carrier :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := fockReflection.toLinearMap, norm_map' := fockReflection_norm }
    fockReflection_involutive.surjective

theorem fockReflection_physical (u : GW.Fock.Carrier) (n : ℕ) :
    physicalSector n (fockReflection u n) =ᵐ[GW.Fock.sectorMeasure n]
      (fun k => physicalSector n (u n) (fun i => -k i)) := by
  change physicalSector n (sectorReflection n (u n)) =ᵐ[_] _
  rw [sectorReflection_physical]
  exact ambientReflection_ae n _

section Weights
variable (w v : ∀ n, GW.Fock.Coordinates n → ℝ)
  (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n k, 1 ≤ w n k)
  (hp : ∀ n (τ : Equiv.Perm (Fin n)) k, w n (fun i => k (τ i)) = w n k)
  (hv : ∀ n, Measurable (v n)) (hv1 : ∀ n k, 1 ≤ v n k)
  (hvp : ∀ n (τ : Equiv.Perm (Fin n)) k, v n (fun i => k (τ i)) = v n k)

def weightedReflection :
    GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp) ≃ₗᵢ[ℂ]
      GW.Spaces.WeightedDomain (fockWeightedGraph v hv hv1 hvp) :=
  ((fockWeightedCoordinates w hw hw1 hp).trans fockReflectionEquiv).trans
    (fockWeightedCoordinates v hv hv1 hvp).symm

theorem weightedReflection_physical
    (hrel : ∀ n, (fun k => v n k) =ᵐ[GW.Fock.sectorMeasure n] (fun k => w n (fun i => -k i)))
    (u : GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp)) :
    weightedFockValue v hv hv1 hvp (weightedReflection w v hw hw1 hp hv hv1 hvp u) =
      fockReflection (weightedFockValue w hw hw1 hp u) := by
  apply lp.ext
  funext n
  apply (physicalSector n).injective
  apply Lp.ext
  have ht := fockWeightedCoordinates_physical v hv hv1 hvp
    (weightedReflection w v hw hw1 hp hv hv1 hvp u) n
  have he : fockWeightedCoordinates v hv hv1 hvp
      (weightedReflection w v hw hw1 hp hv hv1 hvp u) =
        fockReflection (fockWeightedCoordinates w hw hw1 hp u) := by
    change fockWeightedCoordinates v hv hv1 hvp
      ((fockWeightedCoordinates v hv hv1 hvp).symm
        (fockReflectionEquiv (fockWeightedCoordinates w hw hw1 hp u))) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
    rfl
  rw [he] at ht
  have hs := (configurationNegation_preserving n).quasiMeasurePreserving.ae
    (fockWeightedCoordinates_physical w hw hw1 hp u n)
  filter_upwards [ht, hs, hrel n,
    fockReflection_physical (fockWeightedCoordinates w hw hw1 hp u) n,
    fockReflection_physical (weightedFockValue w hw hw1 hp u) n] with k ht hs hr hf hu
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans_le (hv1 n k))))
  rw [ht, hf, hu, hr]
  exact hs.symm

end Weights
end Froehlich
