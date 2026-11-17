import Froehlich.Nodes.FB01KineticAssembly
import Froehlich.Nodes.FB01KineticIdentity
import Froehlich.Nodes.FB01Extension

/-! Exact full form-domain kinetic and number energy decomposition. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

def energyKineticNorm (P : GW.Space) (x : EnergySpace P) : ℝ :=
  Real.sqrt (∑ a : Fin 3, ‖energyKineticComponent P a x‖^2)

theorem energyKineticSum_continuous (P : GW.Space) :
    Continuous (fun x : EnergySpace P => ∑ a : Fin 3, ‖energyKineticComponent P a x‖^2) :=
  continuous_finsetSum Finset.univ (fun a _ => (energyKineticComponent P a).continuous.norm.pow 2)

theorem energyKineticNorm_continuous (P : GW.Space) : Continuous (energyKineticNorm P) :=
  Real.continuous_sqrt.comp (energyKineticSum_continuous P)

theorem energyKineticNorm_sq (P : GW.Space) (x : EnergySpace P) :
    energyKineticNorm P x ^ 2 = ∑ a : Fin 3, ‖energyKineticComponent P a x‖^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem energyKineticNorm_core (P : GW.Space) (u : boundedMomentumCore) :
    energyKineticNorm P (coreEnergyLift P u) = Real.sqrt (∑ a : Fin 3, ‖coreKineticComponent P a u‖^2) := by
  unfold energyKineticNorm
  simp_rw [energyKineticComponent_core]

theorem energyKineticNumber_identity (P : GW.Space) (x : EnergySpace P) :
    (∑ a : Fin 3, ‖energyKineticComponent P a x‖^2) +
      ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput (energyNumberCoordinates P x))‖^2 =
        freeEnergy P (energyEmbedding P x) := by
  have hc : IsClosed {y : EnergySpace P |
      (∑ a : Fin 3, ‖energyKineticComponent P a y‖^2) +
        ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput (energyNumberCoordinates P y))‖^2 =
          freeEnergy P (energyEmbedding P y)} :=
    isClosed_eq ((energyKineticSum_continuous P).add (numberRoot_energy_continuous P))
      (freeEnergy_embedding_continuous P)
  exact (coreEnergyLift_denseRange P).induction_on x hc (fun u => by
    simp_rw [energyKineticComponent_core,coreEnergyNumberCoordinates_eq,coreEnergyLift_embedding]
    exact coreKineticNumber_identity P u)

theorem energyKineticNorm_number_identity (P : GW.Space) (x : EnergySpace P) :
    energyKineticNorm P x ^ 2 +
      ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput (energyNumberCoordinates P x))‖^2 =
        freeEnergy P (energyEmbedding P x) := by
  rw [energyKineticNorm_sq]
  exact energyKineticNumber_identity P x

theorem numberForm_shiftedRoot_norm (x : NumberFormSpace) :
    ‖GW.Fock.shiftedNumberPower GW.Fock.Sector (1/2)
      (GW.Fock.shiftedNumberInput GW.Fock.Sector (1/2) (by positivity) (numberFormRootInput x))‖ = ‖x‖ := by
  have h := congrArg (fun y : NumberFormSpace => ‖y‖) (numberFormGraph.product_embedding x)
  exact h

end Froehlich
