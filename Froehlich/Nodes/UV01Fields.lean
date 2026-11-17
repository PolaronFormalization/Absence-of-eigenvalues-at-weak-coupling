import Froehlich.Nodes.UV01PhysicalResolvent
import Froehlich.Nodes.UV01SourceAnchors

/-! Literal cutoff Z,Y,X, with zero extension from the actual high sector.
All reference energies are the same e used by the singular RS01 fields. -/
noncomputable section
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (Λ : GW.Operators.PositiveCutoff) (g : ℝ) (hg : |g| ≤ 1)
    (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2)

def cutoffAuxiliaryExtendedResolvent : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  (HighSectorSpace n).subtypeL.comp
    ((cutoffAuxiliaryResolvent n e p he Λ g hg hsmall).comp (highSectorProject n))

theorem cutoffAuxiliaryExtendedResolvent_on_high (f : HighSectorSpace n) :
    cutoffAuxiliaryExtendedResolvent n e p he Λ g hg hsmall (f : GW.Fock.Carrier) =
      (cutoffAuxiliaryResolvent n e p he Λ g hg hsmall f : GW.Fock.Carrier) := by
  have hf : highSectorProject n (f : GW.Fock.Carrier) = f := by
    apply Subtype.ext
    exact (highSector_mem_iff n f).mp f.property
  change (cutoffAuxiliaryResolvent n e p he Λ g hg hsmall (highSectorProject n (f : GW.Fock.Carrier)) : GW.Fock.Carrier) = _
  rw [hf]

theorem cutoffAuxiliaryExtendedResolvent_discarded (f : GW.Fock.Carrier) (hf : highSectorProjection n f=0) :
    cutoffAuxiliaryExtendedResolvent n e p he Λ g hg hsmall f=0 := by
  have hp : highSectorProject n f=0 := by apply Subtype.ext; exact hf
  change (cutoffAuxiliaryResolvent n e p he Λ g hg hsmall (highSectorProject n f) : GW.Fock.Carrier)=0
  rw [hp,map_zero]
  rfl

theorem cutoffAuxiliaryExtendedResolvent_norm_le :
    ‖cutoffAuxiliaryExtendedResolvent n e p he Λ g hg hsmall‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  have hp : ‖highSectorProject n f‖ ≤ ‖f‖ := highSectorProjection_norm_le n f
  change ‖cutoffAuxiliaryResolvent n e p he Λ g hg hsmall (highSectorProject n f)‖ ≤ 2*‖f‖
  exact ((cutoffAuxiliaryResolvent n e p he Λ g hg hsmall).le_opNorm _).trans
    (mul_le_mul (cutoffAuxiliaryResolvent_norm_le n e p he Λ g hg hsmall) hp (norm_nonneg _) (by norm_num))

def cutoffAuxiliaryZ : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  cutoffAuxiliaryExtendedResolvent 0 e p he Λ g hg hsmall

def cutoffAuxiliaryY : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  cutoffAuxiliaryExtendedResolvent 1 e p he Λ g hg hsmall

def cutoffAuxiliaryX (P : GW.Space) : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  cutoffAuxiliaryExtendedResolvent 2 e (-P) he Λ g hg hsmall

end Froehlich
