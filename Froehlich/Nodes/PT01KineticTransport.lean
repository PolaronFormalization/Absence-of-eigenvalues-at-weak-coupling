import Froehlich.Nodes.FB01KineticAssembly
import Froehlich.Nodes.FB02Transport

set_option autoImplicit false

/-! The genuine momentum actions transported to one fixed energy space.
Their momentum dependence is affine in operator norm. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem energyKineticComponent_change (P Q : GW.Space) (a : Fin 3) (x : EnergySpace Q) :
    energyKineticComponent P a (energyCoordinateChange P Q x) =
      energyKineticComponent Q a x - ((P a-Q a : ℝ) : ℂ) • energyEmbedding Q x := by
  have h := fockRealMultiplier_shift_graph (energyKineticSymbol Q a) (P a-Q a)
    (energyEmbedding Q x) (energyKineticComponent Q a x) (energyKineticComponent_graph Q a x)
  have he : (fun n K => energyKineticSymbol Q a n K-(P a-Q a)) = energyKineticSymbol P a := by
    funext n K
    unfold energyKineticSymbol
    ring
  rw [he] at h
  have hp := energyKineticComponent_graph P a (energyCoordinateChange P Q x)
  rw [energyCoordinateChange_intertwines] at hp
  exact (fockRealMultiplier (energyKineticSymbol P a)).mem_graph_snd_inj hp h rfl

def fixedEnergyKineticComponent (Q : GW.Space) (a : Fin 3) (P : GW.Space) :
    EnergySpace Q →L[ℂ] GW.Fock.Carrier :=
  energyKineticComponent Q a - ((P a-Q a : ℝ) : ℂ) • energyEmbedding Q

theorem fixedEnergyKineticComponent_actual (Q : GW.Space) (a : Fin 3) (P : GW.Space) :
    fixedEnergyKineticComponent Q a P =
      (energyKineticComponent P a).comp (energyCoordinateChange P Q) := by
  apply ContinuousLinearMap.ext
  intro x
  exact (energyKineticComponent_change P Q a x).symm

theorem fixedEnergyKineticComponent_continuous (Q : GW.Space) (a : Fin 3) :
    Continuous (fixedEnergyKineticComponent Q a) := by
  have hc : Continuous (fun P : GW.Space => ((P a-Q a : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) a).sub continuous_const)
  exact continuous_const.sub (hc.smul continuous_const)

end Froehlich
