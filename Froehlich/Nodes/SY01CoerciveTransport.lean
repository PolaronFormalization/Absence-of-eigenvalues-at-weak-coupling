import Froehlich.Nodes.SY01SourceLoads
import Froehlich.Nodes.SY01WeakEquations

/-! Conditional symmetry of actual compressed coercive weak solutions.
The input records only coercivity and the literal shifted-form representative;
the inverse itself is constructed by the retained GW theorem. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

structure CompressedCoercivity (g lam : ℝ) (P : GW.Space) (n : ℕ)
    (i : Option GW.Operators.PositiveCutoff) where
  operator : HighEnergySpace P n →L[ℂ] HighEnergySpace P n
  selfadjoint : operator.adjoint = operator
  lower : ℝ
  positive : 0 < lower
  bound : ∀ u, lower*‖u‖^2 ≤ (⟪u,operator u⟫_ℂ).re
  representative : ∀ w u, ⟪w,operator u⟫_ℂ = (compressedFiberFormData g P n i).form w u -
    (lam : ℂ)*⟪highEnergyEmbedding P n w,highEnergyEmbedding P n u⟫_ℂ

def compressedCoerciveSolution {g lam : ℝ} {P : GW.Space} {n : ℕ}
    {i : Option GW.Operators.PositiveCutoff} (d : CompressedCoercivity g lam P n i)
    (F : ConjugateLoad (HighEnergySpace P n)) : HighEnergySpace P n :=
  coerciveEnergyInverse d.operator d.selfadjoint d.positive d.bound (loadRiesz F)

theorem compressedCoerciveSolution_equation {g lam : ℝ} {P : GW.Space} {n : ℕ}
    {i : Option GW.Operators.PositiveCutoff} (d : CompressedCoercivity g lam P n i)
    (F : ConjugateLoad (HighEnergySpace P n)) (w : HighEnergySpace P n) :
    (compressedFiberFormData g P n i).form w (compressedCoerciveSolution d F) -
      (lam : ℂ)*⟪highEnergyEmbedding P n w,highEnergyEmbedding P n (compressedCoerciveSolution d F)⟫_ℂ = F w := by
  rw [← d.representative]
  exact coerciveEnergyInverse_load d.operator d.selfadjoint d.positive d.bound F w

theorem compressedCoerciveSolution_unique {g lam : ℝ} {P : GW.Space} {n : ℕ}
    {i : Option GW.Operators.PositiveCutoff} (d : CompressedCoercivity g lam P n i)
    (F : ConjugateLoad (HighEnergySpace P n)) (x : HighEnergySpace P n)
    (hx : ∀ w, (compressedFiberFormData g P n i).form w x -
      (lam : ℂ)*⟪highEnergyEmbedding P n w,highEnergyEmbedding P n x⟫_ℂ = F w) :
    x = compressedCoerciveSolution d F := by
  apply coercive_weak_unique d.operator d.selfadjoint d.lower d.positive d.bound
  intro w
  rw [d.representative,d.representative,hx,compressedCoerciveSolution_equation]

theorem compressedCoerciveSolution_conjugation {g lam : ℝ} {P : GW.Space} {n : ℕ}
    {i : Option GW.Operators.PositiveCutoff} (d : CompressedCoercivity g lam P n i)
    (F F' : ConjugateLoad (HighEnergySpace P n))
    (hF : ∀ w, F' w = (starRingEnd ℂ) (F (highEnergyConjugation P n w))) :
    highEnergyConjugation P n (compressedCoerciveSolution d F) = compressedCoerciveSolution d F' := by
  apply compressedCoerciveSolution_unique d F'
  intro w
  have h := compressedWeak_conjugation g lam P n i F (compressedCoerciveSolution d F)
    (compressedCoerciveSolution_equation d F) w
  exact h.trans (hF w).symm

theorem compressedCoerciveSolution_reflection {g lam : ℝ} {P : GW.Space} {n : ℕ}
    {i : Option GW.Operators.PositiveCutoff} (d : CompressedCoercivity g lam P n i)
    (d' : CompressedCoercivity g lam (-P) n i)
    (F : ConjugateLoad (HighEnergySpace P n)) (F' : ConjugateLoad (HighEnergySpace (-P) n))
    (hF : ∀ w, F' w = F (highEnergyReflectionInv P n w)) :
    highEnergyReflection P n (compressedCoerciveSolution d F) = compressedCoerciveSolution d' F' := by
  apply compressedCoerciveSolution_unique d' F'
  intro w
  have h := compressedWeak_reflection g lam P n i F (compressedCoerciveSolution d F)
    (compressedCoerciveSolution_equation d F) w
  exact h.trans (hF w).symm

theorem compressedSingularSolution_conjugation {g lam : ℝ} {P : GW.Space} {n : ℕ}
    {i : Option GW.Operators.PositiveCutoff} (d : CompressedCoercivity g lam P n i) :
    highEnergyConjugation P n (compressedCoerciveSolution d (highFiberSourceLoad g P n)) =
      compressedCoerciveSolution d (highFiberSourceLoad g P n) := by
  apply compressedCoerciveSolution_conjugation
  intro w
  exact (highFiberSourceLoad_conjugation g P n w).symm

theorem compressedSingularSolution_reflection {g lam : ℝ} {P : GW.Space} {n : ℕ}
    {i : Option GW.Operators.PositiveCutoff} (d : CompressedCoercivity g lam P n i)
    (d' : CompressedCoercivity g lam (-P) n i) :
    highEnergyReflection P n (compressedCoerciveSolution d (highFiberSourceLoad g P n)) =
      compressedCoerciveSolution d' (highFiberSourceLoad g (-P) n) := by
  apply compressedCoerciveSolution_reflection
  intro w
  have h := highFiberSourceLoad_reflection g P n (highEnergyReflectionInv P n w)
  rw [highEnergyReflection_apply_inverse] at h
  exact h

end Froehlich
