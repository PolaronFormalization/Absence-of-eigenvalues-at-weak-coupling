import Froehlich.Nodes.SY01EnergyMaps
import Froehlich.Nodes.FD02WeightedConjugationMap

/-! Actual conjugation on the canonical free energy coordinates. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

def energyConjugationLinear (P : GW.Space) : EnergySpace P →ₗ⋆[ℂ] EnergySpace P where
  toFun u := (energyCoordinates P).symm (fockConjugation (energyCoordinates P u))
  map_add' u v := by
    apply (energyCoordinates P).injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_add, fockConjugation_add, map_add]
    simp only [LinearIsometryEquiv.apply_symm_apply]
  map_smul' c u := by
    apply (energyCoordinates P).injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_smul, fockConjugation_smul, map_smul]
    simp only [LinearIsometryEquiv.apply_symm_apply, RingHom.id_apply]

def energyConjugation (P : GW.Space) : EnergySpace P →ₗᵢ⋆[ℂ] EnergySpace P where
  toLinearMap := energyConjugationLinear P
  norm_map' u := by
    change ‖(energyCoordinates P).symm (fockConjugation (energyCoordinates P u))‖ = _
    rw [LinearIsometryEquiv.norm_map, fockConjugation_norm, LinearIsometryEquiv.norm_map]

theorem energyConjugation_coordinates (P : GW.Space) (u : EnergySpace P) :
    energyCoordinates P (energyConjugation P u) = fockConjugation (energyCoordinates P u) :=
  (energyCoordinates P).apply_symm_apply _

theorem energyConjugation_involutive (P : GW.Space) : Function.Involutive (energyConjugation P) := by
  intro u
  apply (energyCoordinates P).injective
  rw [energyConjugation_coordinates, energyConjugation_coordinates, fockConjugation_involutive]

theorem energyConjugation_intertwines (P : GW.Space) (u : EnergySpace P) :
    energyEmbedding P (energyConjugation P u) = fockConjugation (energyEmbedding P u) := by
  apply lp.ext
  funext n
  apply (physicalSector n).injective
  apply Lp.ext
  have ht := energyEmbedding_weighted_ae P (energyConjugation P u) n
  rw [energyConjugation_coordinates] at ht
  filter_upwards [ht, energyEmbedding_weighted_ae P u n,
    fockConjugation_physical (energyCoordinates P u) n,
    fockConjugation_physical (energyEmbedding P u) n] with k ht hu hf hv
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (zero_lt_one.trans_le (energyWeight_ge_one P n k))))
  simp only [smul_eq_mul] at ht hu
  rw [ht, hf, ← hu, hv, map_mul, Complex.conj_ofReal]

theorem energyConjugation_norm (P : GW.Space) (u : EnergySpace P) :
    ‖energyConjugation P u‖ = ‖u‖ := (energyConjugation P).norm_map u

end Froehlich
