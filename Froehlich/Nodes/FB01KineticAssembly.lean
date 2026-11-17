import Froehlich.Nodes.FB01KineticDomain

/-! Bounded energy-to-physical shifted momentum actions, identified with
their actual maximal multiplication graphs. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

def energyKineticComponent (P : GW.Space) (a : Fin 3) : EnergySpace P →L[ℂ] GW.Fock.Carrier :=
  (GW.Spaces.diagonalMap (energyKineticSector P a) zero_le_one (energyKineticSector_norm P a)).comp
    (energyCoordinates P).toLinearIsometry.toContinuousLinearMap

theorem energyKineticComponent_apply (P : GW.Space) (a : Fin 3) (x : EnergySpace P) (n : ℕ) :
    energyKineticComponent P a x n = energyKineticSector P a n (energyCoordinates P x n) := rfl

theorem energyKineticComponent_norm_le (P : GW.Space) (a : Fin 3) (x : EnergySpace P) :
    ‖energyKineticComponent P a x‖ ≤ ‖x‖ := by
  have h := GW.Spaces.diagonal_norm_bound (energyKineticSector P a) zero_le_one
    (energyKineticSector_norm P a) (energyCoordinates P x)
  rw [one_mul,(energyCoordinates P).norm_map] at h
  exact h

theorem energyKineticComponent_ae (P : GW.Space) (a : Fin 3) (x : EnergySpace P) (n : ℕ) :
    (fun K => (energyKineticSymbol P a n K : ℂ) • physicalSector n (energyEmbedding P x n) K)
      =ᵐ[GW.Fock.sectorMeasure n] physicalSector n (energyKineticComponent P a x n) := by
  filter_upwards [energyEmbedding_weighted_ae P x n,
    energyKineticSector_ae P a n (energyCoordinates P x n)] with K hw hm
  rw [energyKineticComponent_apply,← hm,← hw,smul_smul]
  have hn : energyWeight P n K ≠ 0 := ne_of_gt (zero_lt_one.trans_le (energyWeight_ge_one P n K))
  have hr : (energyKineticRatio P a n K : ℂ) * (energyWeight P n K : ℂ) =
      (energyKineticSymbol P a n K : ℂ) := by
    rw [← Complex.ofReal_mul]
    exact congrArg (fun t : ℝ => (t : ℂ)) (div_mul_cancel₀ (energyKineticSymbol P a n K) hn)
  rw [hr]

theorem energyKineticComponent_graph (P : GW.Space) (a : Fin 3) (x : EnergySpace P) :
    (energyEmbedding P x,energyKineticComponent P a x) ∈
      (fockRealMultiplier (energyKineticSymbol P a)).graph :=
  (fockRealMultiplier_graph_ae_iff _ _ _).mpr (energyKineticComponent_ae P a x)

def energyKineticInput (P : GW.Space) (a : Fin 3) (x : EnergySpace P) :
    (fockRealMultiplier (energyKineticSymbol P a)).domain :=
  ⟨energyEmbedding P x,(fockRealMultiplier _).mem_domain_of_mem_graph (energyKineticComponent_graph P a x)⟩

theorem energyKineticComponent_actual (P : GW.Space) (a : Fin 3) (x : EnergySpace P) :
    fockRealMultiplier (energyKineticSymbol P a) (energyKineticInput P a x) = energyKineticComponent P a x :=
  (fockRealMultiplier _).mem_graph_snd_inj
    ((fockRealMultiplier _).mem_graph (energyKineticInput P a x)) (energyKineticComponent_graph P a x) rfl

theorem energyKineticComponent_core (P : GW.Space) (a : Fin 3) (u : boundedMomentumCore) :
    energyKineticComponent P a (coreEnergyLift P u) = coreKineticComponent P a u := by
  have h := energyKineticComponent_graph P a (coreEnergyLift P u)
  rw [coreEnergyLift_embedding] at h
  exact (fockRealMultiplier _).mem_graph_snd_inj h (coreKineticComponent_graph P a u) rfl

end Froehlich
