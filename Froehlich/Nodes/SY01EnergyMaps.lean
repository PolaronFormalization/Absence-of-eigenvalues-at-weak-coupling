import Froehlich.Nodes.FD02WeightedReflection

/-! Exact reflection of the free energy coordinates, on the same canonical
physical Fock carrier. Interaction and operator symmetries are separate. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

theorem totalMomentum_negation (n : ℕ) (k : GW.Fock.Coordinates n) :
    totalMomentum n (fun i => -k i) = -totalMomentum n k := by
  simp only [totalMomentum, Finset.sum_neg_distrib]

theorem freeSymbol_negation (P : GW.Space) (n : ℕ) (k : GW.Fock.Coordinates n) :
    freeSymbol (-P) n (fun i => -k i) = freeSymbol P n k := by
  unfold freeSymbol
  rw [totalMomentum_negation]
  have he : -totalMomentum n k - (-P) = -(totalMomentum n k - P) := by module
  rw [he, norm_neg]

theorem energyWeight_negation (P : GW.Space) (n : ℕ) (k : GW.Fock.Coordinates n) :
    energyWeight (-P) n (fun i => -k i) = energyWeight P n k := by
  simp only [energyWeight, freeSymbol_negation]

theorem operatorGraphWeight_negation (P : GW.Space) (n : ℕ) (k : GW.Fock.Coordinates n) :
    operatorGraphWeight (-P) n (fun i => -k i) = operatorGraphWeight P n k := by
  simp only [operatorGraphWeight, freeSymbol_negation]

def energyReflection (P : GW.Space) : EnergySpace P ≃ₗᵢ[ℂ] EnergySpace (-P) :=
  ((energyCoordinates P).trans fockReflectionEquiv).trans (energyCoordinates (-P)).symm

theorem energyReflection_coordinates (P : GW.Space) (u : EnergySpace P) :
    energyCoordinates (-P) (energyReflection P u) = fockReflection (energyCoordinates P u) := by
  change energyCoordinates (-P) ((energyCoordinates (-P)).symm
    (fockReflectionEquiv (energyCoordinates P u))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem energyReflection_intertwines (P : GW.Space) (u : EnergySpace P) :
    energyEmbedding (-P) (energyReflection P u) = fockReflection (energyEmbedding P u) := by
  apply lp.ext
  funext n
  apply (physicalSector n).injective
  apply Lp.ext
  have ht := energyEmbedding_weighted_ae (-P) (energyReflection P u) n
  rw [energyReflection_coordinates] at ht
  have hs := (configurationNegation_preserving n).quasiMeasurePreserving.ae
    (energyEmbedding_weighted_ae P u n)
  filter_upwards [ht, hs, fockReflection_physical (energyCoordinates P u) n,
    fockReflection_physical (energyEmbedding P u) n] with k ht hs hf hu
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (zero_lt_one.trans_le (energyWeight_ge_one (-P) n k))))
  have hr : energyWeight (-P) n k = energyWeight P n (fun i => -k i) := by
    simpa only [neg_neg] using energyWeight_negation P n (fun i => -k i)
  simp only [smul_eq_mul] at ht hs
  rw [ht, hf, hu, hr]
  exact hs.symm

theorem energyReflection_norm (P : GW.Space) (u : EnergySpace P) :
    ‖energyReflection P u‖ = ‖u‖ := (energyReflection P).norm_map u

end Froehlich
