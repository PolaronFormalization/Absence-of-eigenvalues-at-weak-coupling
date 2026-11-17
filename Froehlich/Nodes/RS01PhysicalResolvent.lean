import Froehlich.Nodes.RS01NormalizedForm
import Froehlich.Nodes.RS01FreeInverse

/-! The literal physical formula G M⁻¹ G, positive with norm at most two,
and its weak equation on every original high-energy test vector. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)

theorem auxiliaryEnergyLift_high_physical (u : HighSectorSpace n) :
    highEnergyEmbedding (-p) n (auxiliaryEnergyLiftEquivalence n e p hn he u) =
      auxiliaryPhysicalFreeInverse n e p he.2 u := by
  apply Subtype.ext
  change energyEmbedding (-p)
    (auxiliaryEnergyLiftEquivalence n e p hn he u : EnergySpace (-p)) = _
  rw [auxiliaryEnergyLiftEquivalence_val,auxiliaryEnergyLift_physical n e p hn he]

def auxiliaryPhysicalLoad (f : HighSectorSpace n) : ConjugateLoad (HighEnergySpace (-p) n) :=
  (innerSLFlip ℂ f).comp (highEnergyEmbedding (-p) n)

theorem auxiliaryPhysicalLoad_pullback (f : HighSectorSpace n) :
    loadRiesz ((auxiliaryPhysicalLoad n p f).comp
      (auxiliaryEnergyLiftEquivalence n e p hn he).toContinuousLinearMap) =
      auxiliaryPhysicalFreeInverse n e p he.2 f := by
  apply Eq.symm
  apply loadRiesz_unique
  intro u
  change ⟪highEnergyEmbedding (-p) n (auxiliaryEnergyLiftEquivalence n e p hn he u),f⟫_ℂ = _
  rw [auxiliaryEnergyLift_high_physical]
  simpa only [auxiliaryPhysicalFreeInverse_selfadjoint] using
    ((auxiliaryPhysicalFreeInverse n e p he.2).adjoint_inner_right u f).symm

variable (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2)

def auxiliaryResolvent : HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  (auxiliaryPhysicalFreeInverse n e p he.2).comp
    ((auxiliaryNormalizedInverse g n e p he.2 hg hsmall).comp (auxiliaryPhysicalFreeInverse n e p he.2))

def auxiliaryPhysicalEnergySolution (f : HighSectorSpace n) : HighEnergySpace (-p) n :=
  auxiliaryEnergyLiftEquivalence n e p hn he
    (auxiliaryNormalizedInverse g n e p he.2 hg hsmall (auxiliaryPhysicalFreeInverse n e p he.2 f))

theorem auxiliaryResolvent_solution_embedding (f : HighSectorSpace n) :
    highEnergyEmbedding (-p) n (auxiliaryPhysicalEnergySolution n e p hn he g hg hsmall f) =
      auxiliaryResolvent n e p he g hg hsmall f := by
  exact auxiliaryEnergyLift_high_physical n e p hn he _

theorem auxiliaryResolvent_weak (f : HighSectorSpace n) (w : HighEnergySpace (-p) n) :
    (fiberFormData g (-p) none).form (w : EnergySpace (-p))
      (auxiliaryPhysicalEnergySolution n e p hn he g hg hsmall f : EnergySpace (-p)) +
      ((1-(n : ℝ)-e : ℝ) : ℂ)*
        ⟪energyEmbedding (-p) (w : EnergySpace (-p)),
          energyEmbedding (-p) (auxiliaryPhysicalEnergySolution n e p hn he g hg hsmall f : EnergySpace (-p))⟫_ℂ =
      ⟪highEnergyEmbedding (-p) n w,f⟫_ℂ := by
  have h := auxiliaryDualSolution_weak n e p hn he g hg hsmall (auxiliaryPhysicalLoad n p f) w
  have hs : auxiliaryDualSolution n e p hn he g hg hsmall (auxiliaryPhysicalLoad n p f) =
      auxiliaryPhysicalEnergySolution n e p hn he g hg hsmall f := by
    unfold auxiliaryDualSolution
    rw [auxiliaryPhysicalLoad_pullback]
    rfl
  rw [hs] at h
  exact h

theorem auxiliaryResolvent_nonnegative (f : HighSectorSpace n) :
    0 ≤ (⟪f,auxiliaryResolvent n e p he g hg hsmall f⟫_ℂ).re := by
  change 0 ≤ (⟪f,auxiliaryPhysicalFreeInverse n e p he.2
    (auxiliaryNormalizedInverse g n e p he.2 hg hsmall (auxiliaryPhysicalFreeInverse n e p he.2 f))⟫_ℂ).re
  rw [← (auxiliaryPhysicalFreeInverse n e p he.2).adjoint_inner_left,auxiliaryPhysicalFreeInverse_selfadjoint]
  exact auxiliaryNormalizedInverse_nonnegative g n e p he.2 hg hsmall _

theorem auxiliaryResolvent_norm_le : ‖auxiliaryResolvent n e p he g hg hsmall‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  have hG (u : HighSectorSpace n) : ‖auxiliaryPhysicalFreeInverse n e p he.2 u‖ ≤ ‖u‖ :=
    ((auxiliaryPhysicalFreeInverse n e p he.2).le_opNorm u).trans
      (by nlinarith [auxiliaryPhysicalFreeInverse_norm_le n e p he.2,norm_nonneg u])
  have hM := (auxiliaryNormalizedInverse g n e p he.2 hg hsmall).le_opNorm
    (auxiliaryPhysicalFreeInverse n e p he.2 f)
  have hMi := auxiliaryNormalizedInverse_norm_le g n e p he.2 hg hsmall
  change ‖auxiliaryPhysicalFreeInverse n e p he.2
    (auxiliaryNormalizedInverse g n e p he.2 hg hsmall (auxiliaryPhysicalFreeInverse n e p he.2 f))‖ ≤ 2*‖f‖
  exact (hG _).trans (hM.trans (by nlinarith [hG f,norm_nonneg (auxiliaryPhysicalFreeInverse n e p he.2 f)]))

end Froehlich
