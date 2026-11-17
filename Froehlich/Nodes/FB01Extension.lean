import Froehlich.Nodes.FB01CoreForms

/-! Extension from the actual bounded-momentum core in the energy norm. -/
noncomputable section
namespace Froehlich

theorem freeEnergy_embedding_continuous (P : GW.Space) :
    Continuous (fun x : EnergySpace P => freeEnergy P (energyEmbedding P x)) := by
  have he (x : EnergySpace P) : freeEnergy P (energyEmbedding P x) =
      ‖x‖ ^ 2 - ‖energyEmbedding P x‖ ^ 2 := by
    have h := energyEmbedding_norm_identity P x
    linarith
  simp_rw [he]
  exact (continuous_norm.pow 2).sub ((energyEmbedding P).continuous.norm.pow 2)

theorem boundedForm_core_diagonal_extension (P : GW.Space)
    (a : GW.Analysis.BoundedForm (EnergySpace P))
    (b : EnergySpace P → ℝ) (hb : Continuous b)
    (h : ∀ u : boundedMomentumCore,
      ‖a (coreEnergyLift P u) (coreEnergyLift P u)‖ ≤ b (coreEnergyLift P u)) :
    ∀ x : EnergySpace P, ‖a x x‖ ≤ b x := by
  have ha : Continuous (fun x : EnergySpace P => a x x) :=
    a.continuous.clm_apply continuous_id
  intro x
  exact (coreEnergyLift_denseRange P).induction_on x (isClosed_le ha.norm hb) h

theorem numberRoot_energy_continuous (P : GW.Space) :
    Continuous (fun x : EnergySpace P =>
      ‖GW.Fock.numberPower GW.Fock.Sector (1/2)
        (numberFormRootInput (energyNumberCoordinates P x))‖ ^ 2) := by
  have he (x : EnergySpace P) :
      ‖GW.Fock.numberPower GW.Fock.Sector (1/2)
        (numberFormRootInput (energyNumberCoordinates P x))‖ ^ 2 =
      ‖energyNumberCoordinates P x‖ ^ 2 - ‖energyEmbedding P x‖ ^ 2 := by
    have h := numberForm_norm_identity (energyNumberCoordinates P x)
    rw [energyNumberCoordinates_intertwines] at h
    linarith
  simp_rw [he]
  exact ((energyNumberCoordinates P).continuous.norm.pow 2).sub
    ((energyEmbedding P).continuous.norm.pow 2)

end Froehlich
