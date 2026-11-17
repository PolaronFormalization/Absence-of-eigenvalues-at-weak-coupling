import Froehlich.Nodes.RS01CompressedInverse
import Froehlich.Nodes.SY01SourceLoads

/-! Literal auxiliary fields Z,Y,X and the singular source solution.
High resolvents extend by zero; the uncut source remains a conjugate load. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

variable (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2)

def auxiliaryExtendedResolvent : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  (HighSectorSpace n).subtypeL.comp
    ((auxiliaryResolvent n e p he g hg hsmall).comp (highSectorProject n))

theorem auxiliaryExtendedResolvent_on_high (f : HighSectorSpace n) :
    auxiliaryExtendedResolvent n e p he g hg hsmall (f : GW.Fock.Carrier) =
      (auxiliaryResolvent n e p he g hg hsmall f : GW.Fock.Carrier) := by
  have hf : highSectorProject n (f : GW.Fock.Carrier) = f := by
    apply Subtype.ext
    exact (highSector_mem_iff n f).mp f.property
  change (auxiliaryResolvent n e p he g hg hsmall (highSectorProject n (f : GW.Fock.Carrier)) : GW.Fock.Carrier) = _
  rw [hf]

theorem auxiliaryExtendedResolvent_discarded (f : GW.Fock.Carrier) (hf : highSectorProjection n f = 0) :
    auxiliaryExtendedResolvent n e p he g hg hsmall f = 0 := by
  have hp : highSectorProject n f = 0 := by apply Subtype.ext; exact hf
  change (auxiliaryResolvent n e p he g hg hsmall (highSectorProject n f) : GW.Fock.Carrier) = 0
  rw [hp,map_zero]
  rfl

def auxiliaryZ : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier := auxiliaryExtendedResolvent 0 e p he g hg hsmall

def auxiliaryY : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier := auxiliaryExtendedResolvent 1 e p he g hg hsmall

def auxiliaryX (P : GW.Space) : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  auxiliaryExtendedResolvent 2 e (-P) he g hg hsmall

def auxiliaryGroundSourceEnergy : HighEnergySpace (-p) 1 :=
  auxiliaryDualSolution 1 e p (by norm_num) he g hg hsmall (highFiberSourceLoad g (-p) 1)

def auxiliaryGroundSourceVector : GW.Fock.Carrier :=
  energyEmbedding (-p) (auxiliaryGroundSourceEnergy e p he g hg hsmall : EnergySpace (-p))

def auxiliarySelfEnergy : ℝ :=
  -(highFiberSourceLoad g (-p) 1 (auxiliaryGroundSourceEnergy e p he g hg hsmall)).re

theorem auxiliaryGroundSourceEnergy_weak (w : HighEnergySpace (-p) 1) :
    (fiberFormData g (-p) none).form (w : EnergySpace (-p))
      (auxiliaryGroundSourceEnergy e p he g hg hsmall : EnergySpace (-p)) -
      (e : ℂ)*⟪energyEmbedding (-p) (w : EnergySpace (-p)),
        energyEmbedding (-p) (auxiliaryGroundSourceEnergy e p he g hg hsmall : EnergySpace (-p))⟫_ℂ =
      highFiberSourceLoad g (-p) 1 w := by
  have h := auxiliaryDualSolution_weak 1 e p (by norm_num) he g hg hsmall (highFiberSourceLoad g (-p) 1) w
  simpa only [Nat.cast_one,sub_self,zero_sub,zero_add,Complex.ofReal_neg,neg_mul,
    sub_eq_add_neg,auxiliaryGroundSourceEnergy] using h

theorem auxiliaryGroundSourceEnergy_value_real :
    (highFiberSourceLoad g (-p) 1 (auxiliaryGroundSourceEnergy e p he g hg hsmall)).im = 0 := by
  let u := auxiliaryGroundSourceEnergy e p he g hg hsmall
  have hs := auxiliaryGroundSourceEnergy_weak e p he g hg hsmall u
  change (fiberFormData g (-p) none).form (u : EnergySpace (-p)) u -
    (e : ℂ)*⟪energyEmbedding (-p) (u : EnergySpace (-p)),energyEmbedding (-p) (u : EnergySpace (-p))⟫_ℂ =
      highFiberSourceLoad g (-p) 1 u at hs
  have hf := (fiberFormData g (-p) none).hermitian (u : EnergySpace (-p)) u
  have hfi := congrArg Complex.im hf
  simp only [Complex.star_def,Complex.conj_im] at hfi
  have hi := congrArg Complex.im (inner_conj_symm (𝕜 := ℂ)
    (energyEmbedding (-p) (u : EnergySpace (-p))) (energyEmbedding (-p) (u : EnergySpace (-p))))
  simp only [Complex.conj_im] at hi
  have hform0 : ((fiberFormData g (-p) none).form (u : EnergySpace (-p)) u).im = 0 := by linarith
  have hinner0 : (⟪energyEmbedding (-p) (u : EnergySpace (-p)),energyEmbedding (-p) (u : EnergySpace (-p))⟫_ℂ).im = 0 := by linarith
  have hsi := congrArg Complex.im hs
  simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_add,add_zero] at hsi
  rw [hform0,hinner0,mul_zero,sub_zero] at hsi
  exact hsi.symm

end Froehlich
